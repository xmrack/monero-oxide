use core::ops::Range;
use std_shims::vec::Vec;

use zeroize::Zeroize;
use subtle::ConditionallySelectable;

use multiexp::{multiexp as multiexp_ct, multiexp_vartime as multiexp_vt};
use ciphersuite::group::{ff::PrimeFieldBits, Group};

/// The maximum amount of threads used when proving.
pub const MAX_THREADS: usize = 16;

/// Evaluate `f` over consecutive ranges partitioning `0 .. len`, using up to `threads` threads.
///
/// Each range has a length of at least `min`, unless there's a single range. The results are
/// returned in the order of the ranges. Without the `std` feature, this runs on the calling thread.
pub(crate) fn map_ranges<T: Send>(
  threads: usize,
  len: usize,
  min: usize,
  f: impl Fn(Range<usize>) -> T + Sync,
) -> Vec<T> {
  map_ranges_with(threads, len, min, f, |_| true)
}

// `may_spawn` is asked whether to spawn a thread for a range, so failing to spawn one is testable.
#[cfg_attr(not(feature = "std"), allow(unused_variables))]
fn map_ranges_with<T: Send>(
  threads: usize,
  len: usize,
  min: usize,
  f: impl Fn(Range<usize>) -> T + Sync,
  may_spawn: impl Fn(usize) -> bool,
) -> Vec<T> {
  let chunks = threads.clamp(1, MAX_THREADS).min(len / min.max(1)).max(1);
  let range = |i: usize| ((i * len) / chunks) .. (((i + 1) * len) / chunks);

  #[cfg(feature = "std")]
  if chunks > 1 {
    let f = &f;
    return std::thread::scope(|scope| {
      let handles = (1 .. chunks)
        .map(|i| {
          if may_spawn(i) {
            std::thread::Builder::new().spawn_scoped(scope, move || f(range(i))).map_err(|_| i)
          } else {
            Err(i)
          }
        })
        .collect::<Vec<_>>();
      let mut res = Vec::with_capacity(chunks);
      res.push(f(range(0)));
      for handle in handles {
        res.push(match handle {
          Ok(handle) => handle.join().unwrap_or_else(|e| std::panic::resume_unwind(e)),
          // Run on this thread if a thread couldn't be spawned
          Err(i) => f(range(i)),
        });
      }
      res
    });
  }

  (0 .. chunks).map(|i| f(range(i))).collect()
}

/// `multiexp`, split across up to `threads` threads.
pub(crate) fn multiexp<
  G: Group<Scalar: PrimeFieldBits + Zeroize> + Zeroize + ConditionallySelectable,
>(
  threads: usize,
  terms: &[(G::Scalar, G)],
) -> G {
  map_ranges(threads, terms.len(), 64, |range| multiexp_ct(&terms[range])).into_iter().sum()
}

/// `multiexp_vartime`, split across up to `threads` threads.
pub(crate) fn multiexp_vartime<G: Group<Scalar: PrimeFieldBits>>(
  threads: usize,
  terms: &[(G::Scalar, G)],
) -> G {
  map_ranges(threads, terms.len(), 64, |range| multiexp_vt(&terms[range])).into_iter().sum()
}

#[cfg(all(test, feature = "std"))]
mod tests {
  use super::*;

  #[test]
  fn test_spawn_failures() {
    let caller = std::thread::current().id();
    for threads in [1, 2, 3, 7, 16] {
      for len in [0, 1, 5, 100] {
        for min in [1, 10] {
          // No thread spawns, the first or last do not, or only the even ones do
          let policies: [&dyn Fn(usize) -> bool; 4] =
            [&|_| true, &|_| false, &|i| i != 1, &|i| (i % 2) == 0];
          for may_spawn in policies {
            let res = map_ranges_with(
              threads,
              len,
              min,
              |range| (std::thread::current().id(), range.collect::<Vec<_>>()),
              may_spawn,
            );
            // Every index is visited exactly once, in order
            let visited =
              res.iter().flat_map(|(_, range)| range.iter().copied()).collect::<Vec<_>>();
            assert_eq!(visited, (0 .. len).collect::<Vec<_>>(), "{threads} {len} {min}");
            // Ranges which couldn't be given a thread ran on the caller
            for (i, (id, _)) in res.iter().enumerate() {
              if (i == 0) || !may_spawn(i) {
                assert_eq!(*id, caller);
              }
            }
          }
        }
      }
    }
  }
}
