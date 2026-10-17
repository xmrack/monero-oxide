//! Constant-time multi-scalar multiplication over fixed bases with precomputed tables.
//!
//! This is Straus's algorithm with signed radix-`2**WINDOW` digits. Every lookup reads the entire
//! table with `conditional_assign` and conditionally negates, so the memory access pattern and the
//! sequence of operations are independent of the scalars.

use std_shims::{vec, vec::Vec};

#[cfg(feature = "std")]
use std::sync::OnceLock;

use zeroize::Zeroizing;
use subtle::{Choice, ConstantTimeEq as _, ConditionallySelectable};

use ciphersuite::group::{ff::PrimeFieldBits, Group};

const WINDOW: usize = 5;
const TABLE_LEN: usize = 1 << (WINDOW - 1);
/// Windows processed for a scalar flagged as small.
const SMALL_WINDOWS: usize = 2;
/// Scalars flagged as small must be less than `2**SMALL_BITS`.
pub(crate) const SMALL_BITS: usize = (SMALL_WINDOWS * WINDOW) - 1;

/// The multiples `1 ..= TABLE_LEN` of a point.
pub(crate) type Table<G> = [G; TABLE_LEN];

fn table<G: Group>(point: G) -> Table<G> {
  let mut res = [point; TABLE_LEN];
  for i in 1 .. TABLE_LEN {
    res[i] = res[i - 1] + point;
  }
  res
}

/// Segment `s` holds the tables for the indexes `[2**(s - 1), 2**s)`, and segment `0` index `0`.
fn segment(i: usize) -> usize {
  usize::try_from(usize::BITS - i.leading_zeros()).unwrap()
}
fn segment_start(s: usize) -> usize {
  if s == 0 {
    0
  } else {
    1 << (s - 1)
  }
}

/// Segments retained once built, covering the indexes below `2**(CACHED_SEGMENTS - 1)`.
///
/// Tables for higher indexes are built for each use, bounding the memory retained.
#[cfg(feature = "std")]
const CACHED_SEGMENTS: usize = if cfg!(test) { 3 } else { 13 };

/// The tables for a set of generators, built on first use and owned by the generators.
#[derive(Clone)]
pub(crate) struct Tables<G: Group> {
  #[cfg(feature = "std")]
  g: OnceLock<Table<G>>,
  #[cfg(feature = "std")]
  h: OnceLock<Table<G>>,
  #[cfg(feature = "std")]
  g_bold: [OnceLock<Vec<Table<G>>>; CACHED_SEGMENTS],
  #[cfg(feature = "std")]
  h_bold: [OnceLock<Vec<Table<G>>>; CACHED_SEGMENTS],
  #[cfg(not(feature = "std"))]
  _group: core::marker::PhantomData<G>,
}

enum Segment<'a, G: Group> {
  #[cfg(feature = "std")]
  Cached(&'a [Table<G>]),
  Owned(Vec<Table<G>>, core::marker::PhantomData<&'a ()>),
}

/// Tables for a prefix of a list of generators.
pub(crate) struct TablesView<'a, G: Group>(Vec<Segment<'a, G>>);

impl<G: Group> TablesView<'_, G> {
  pub(crate) fn get(&self, i: usize) -> &Table<G> {
    let s = segment(i);
    let i = i - segment_start(s);
    match &self.0[s] {
      #[cfg(feature = "std")]
      Segment::Cached(tables) => &tables[i],
      Segment::Owned(tables, _) => &tables[i],
    }
  }
}

/// Which list of generators to view.
#[derive(Clone, Copy)]
pub(crate) enum Bold {
  G,
  H,
}

impl<G: Group> Tables<G> {
  pub(crate) fn new() -> Self {
    Self {
      #[cfg(feature = "std")]
      g: OnceLock::new(),
      #[cfg(feature = "std")]
      h: OnceLock::new(),
      #[cfg(feature = "std")]
      g_bold: core::array::from_fn(|_| OnceLock::new()),
      #[cfg(feature = "std")]
      h_bold: core::array::from_fn(|_| OnceLock::new()),
      #[cfg(not(feature = "std"))]
      _group: core::marker::PhantomData,
    }
  }

  /// The tables for `g` and `h`.
  #[cfg_attr(not(feature = "std"), allow(clippy::unused_self))]
  pub(crate) fn g_h(&self, g: G, h: G) -> TablesView<'_, G> {
    #[cfg(feature = "std")]
    {
      TablesView(vec![
        Segment::Cached(core::slice::from_ref(self.g.get_or_init(|| table(g)))),
        Segment::Cached(core::slice::from_ref(self.h.get_or_init(|| table(h)))),
      ])
    }
    #[cfg(not(feature = "std"))]
    {
      TablesView(vec![
        Segment::Owned(vec![table(g)], core::marker::PhantomData),
        Segment::Owned(vec![table(h)], core::marker::PhantomData),
      ])
    }
  }

  /// The tables for `generators[.. len]`, where `generators` is the full list of `g` (bold) or
  /// `h` (bold) generators, which has a power-of-two length of at least `len`.
  #[cfg_attr(not(feature = "std"), allow(clippy::unused_self))]
  pub(crate) fn bold(&self, which: Bold, generators: &[G], len: usize) -> TablesView<'_, G> {
    #[cfg(feature = "std")]
    let cached = match which {
      Bold::G => &self.g_bold,
      Bold::H => &self.h_bold,
    };
    #[cfg(not(feature = "std"))]
    let _ = which;

    let segments = if len == 0 { 0 } else { segment(len - 1) + 1 };
    let mut res = Vec::with_capacity(segments);
    for s in 0 .. segments {
      let points = &generators[segment_start(s) .. (1 << s)];
      let build = || points.iter().copied().map(table).collect::<Vec<_>>();
      #[cfg(feature = "std")]
      if let Some(cached) = cached.get(s) {
        res.push(Segment::Cached(cached.get_or_init(build)));
        continue;
      }
      res.push(Segment::Owned(build(), core::marker::PhantomData));
    }
    TablesView(res)
  }
}

fn windows<F: PrimeFieldBits>() -> usize {
  (usize::try_from(F::NUM_BITS).unwrap() / WINDOW) + 1
}

/// Append the signed digits of the scalar's `windows` lowest windows, each encoded as its absolute
/// value with the sign in the top bit.
fn recode<F: PrimeFieldBits>(scalar: &F, windows: usize, digits: &mut Vec<u8>) {
  const HALF: u32 = 1 << (WINDOW - 1);
  let mut bits = scalar.to_le_bits();
  let mut carry = 0u32;
  for w in 0 .. windows {
    let mut value = 0u32;
    for b in 0 .. WINDOW {
      let i = (w * WINDOW) + b;
      if i < bits.len() {
        value |= u32::from(bits[i]) << b;
      }
    }
    let value = value.wrapping_add(carry);
    // `value <= 2**WINDOW`. If it exceeds `HALF`, use `value - 2**WINDOW` and carry one.
    carry = HALF.wrapping_sub(value) >> 31;
    let mask = carry.wrapping_neg();
    let abs = value ^ ((value ^ (1u32 << WINDOW).wrapping_sub(value)) & mask);
    digits.push((abs | (carry << 7)).to_le_bytes()[0]);
  }
  bits.fill(false);
  core::hint::black_box(&bits);
}

#[inline(always)]
fn lookup<G: Group + ConditionallySelectable>(table: &Table<G>, digit: u8) -> G {
  let abs = digit & 0x7f;
  let mut res = G::identity();
  for (point, k) in table.iter().zip(1u8 ..) {
    res.conditional_assign(point, k.ct_eq(&abs));
  }
  let negated = -res;
  res.conditional_assign(&negated, Choice::from(digit >> 7));
  res
}

/// `sum(scalar * point)` over `full` and `small`, where every scalar in `small` is less than
/// `2**(2 * WINDOW - 1)` (only its lowest windows are processed).
///
/// This runs in time independent of the scalars.
pub(crate) fn multiexp<'a, G: Group + ConditionallySelectable + 'a>(
  full: impl IntoIterator<Item = (&'a G::Scalar, &'a Table<G>)>,
  small: impl IntoIterator<Item = (&'a G::Scalar, &'a Table<G>)>,
) -> G
where
  G::Scalar: PrimeFieldBits,
{
  let windows = windows::<G::Scalar>();

  let (full_scalars, full_tables): (Vec<&G::Scalar>, Vec<_>) = full.into_iter().unzip();
  let (small_scalars, small_tables): (Vec<&G::Scalar>, Vec<_>) = small.into_iter().unzip();

  // Allocated to size so the digits are never left behind by a reallocation
  let mut full_digits = Zeroizing::new(Vec::with_capacity(full_scalars.len() * windows));
  for scalar in full_scalars {
    recode(scalar, windows, &mut full_digits);
  }
  let mut small_digits = Zeroizing::new(Vec::with_capacity(small_scalars.len() * SMALL_WINDOWS));
  for scalar in small_scalars {
    debug_assert!(scalar.to_le_bits().iter().skip(SMALL_BITS).all(|bit| !*bit));
    recode(scalar, SMALL_WINDOWS, &mut small_digits);
  }

  let top = if full_tables.is_empty() { SMALL_WINDOWS } else { windows };
  let mut res = G::identity();
  for w in (0 .. top).rev() {
    if w != (top - 1) {
      for _ in 0 .. WINDOW {
        res = res.double();
      }
    }
    for (i, table) in full_tables.iter().enumerate() {
      res += lookup(table, full_digits[(i * windows) + w]);
    }
    if w < SMALL_WINDOWS {
      for (i, table) in small_tables.iter().enumerate() {
        res += lookup(table, small_digits[(i * SMALL_WINDOWS) + w]);
      }
    }
  }

  res
}
