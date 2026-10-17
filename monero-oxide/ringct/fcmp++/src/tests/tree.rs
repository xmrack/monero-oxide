use rand_core::{RngCore as _, SeedableRng as _};
use rand_chacha::ChaCha20Rng;

use ciphersuite::{
  group::{ff::Field as _, Group as _},
  Ciphersuite,
};
use helioselene::{Selene, Helios};
use multiexp::multiexp_vartime;
use ec_divisors::DivisorCurve;

use crate::tree::{self, TreeCurve};

#[test]
fn tables() {
  fn check<C: TreeCurve>() {
    let table = C::table();
    let g_bold = C::generators().g_bold_slice();
    assert!(table.generators > 0);
    for (i, entries) in table.points.chunks_exact(table.points.len() / table.generators).enumerate()
    {
      let mut point = g_bold[i];
      for entry in entries {
        assert_eq!(Some(*entry), C::G::to_xy(point));
        // The batched additions reject equal `x` and are only sound for points off these
        let (x, _) = entry;
        assert!(!bool::from(x.is_zero()));
        assert_ne!(*x, <C::G as DivisorCurve>::FieldElement::ONE);
        assert_ne!(*x, -<C::G as DivisorCurve>::FieldElement::ONE);
        for _ in 0 .. 4 {
          point = point.double();
        }
      }
    }
  }
  check::<Selene>();
  check::<Helios>();
}

fn scalar<C: Ciphersuite>(rng: &mut ChaCha20Rng) -> C::F {
  match rng.next_u32() % 6 {
    0 => C::F::ZERO,
    1 => -C::F::ONE,
    2 => C::F::ONE,
    _ => C::F::random(rng),
  }
}

fn check_shape<C: TreeCurve>(rng: &mut ChaCha20Rng, offset: usize, len: usize) {
  let width = C::table().generators;
  let mut children = (0 .. len).map(|_| scalar::<C>(rng)).collect::<Vec<_>>();
  if (rng.next_u32() % 4) == 0 {
    children = vec![scalar::<C>(rng); len];
  }
  let existing_child = if (rng.next_u32() % 2) == 0 {
    children.first().copied().unwrap_or(C::F::ZERO)
  } else {
    scalar::<C>(rng)
  };
  let existing_hash =
    if (rng.next_u32() % 4) == 0 { C::G::identity() } else { C::G::random(&mut *rng) };
  let generators = C::generators();
  // The table must be used whenever the children are within it, and not otherwise
  if let Some((first, rest)) = children.split_first() {
    let expected = multiexp_vartime(
      &children
        .iter()
        .copied()
        .zip(generators.g_bold_slice().get(offset ..).unwrap_or(&[]).iter().copied())
        .collect::<Vec<_>>(),
    );
    let used = tree::table_multiexp::<C>(offset, *first, rest);
    if (offset + len) <= width {
      assert_eq!(used, Some(expected), "offset {offset} len {len}");
    } else {
      assert_eq!(used, None, "offset {offset} len {len}");
    }
  }
  assert_eq!(
    tree::hash_grow::<C>(existing_hash, offset, existing_child, &children),
    fcmps::tree::hash_grow(generators, existing_hash, offset, existing_child, &children),
    "offset {offset} len {len}"
  );
  assert_eq!(
    tree::hash_trim::<C>(existing_hash, offset, &children, existing_child),
    fcmps::tree::hash_trim(generators, existing_hash, offset, &children, existing_child),
    "offset {offset} len {len}"
  );
}

#[test]
fn hash_grow_and_trim() {
  fn check<C: TreeCurve>() {
    let mut rng = ChaCha20Rng::seed_from_u64(0);
    let width = C::table().generators;
    for _ in 0 .. 200 {
      let offset = usize::try_from(rng.next_u32()).unwrap() % (width + 2);
      let len = usize::try_from(rng.next_u32()).unwrap() % (width + 3 - offset.min(width));
      check_shape::<C>(&mut rng, offset, len);
    }
    // Every shape that ends just before, at, and just after the end of the table
    for len in [1, 2, 3, 11, 12, 13, width - 1, width] {
      for end in [width - 1, width, width + 1] {
        if let Some(offset) = end.checked_sub(len) {
          check_shape::<C>(&mut rng, offset, len);
        }
      }
    }
    for offset in [usize::MAX, usize::MAX - 1, C::generators().g_bold_slice().len()] {
      let children = [C::F::ONE, C::F::ONE];
      assert_eq!(tree::hash_grow::<C>(C::G::identity(), offset, C::F::ZERO, &children), None);
      assert_eq!(tree::hash_trim::<C>(C::G::identity(), offset, &children, C::F::ZERO), None);
    }
  }
  check::<Selene>();
  check::<Helios>();
}

type Xy<C> = (
  <<C as Ciphersuite>::G as DivisorCurve>::FieldElement,
  <<C as Ciphersuite>::G as DivisorCurve>::FieldElement,
);

fn sum<C: TreeCurve>(points: &[Xy<C>]) -> C::G {
  points
    .iter()
    .map(|(x, y)| C::from_xy(*x, *y).unwrap())
    .fold(C::G::identity(), |sum, point| sum + point)
}

// Rounds of batched additions are used once enough pairs are present. As they cannot add equal
// points, a repeat is only rejected (returning `None`, so the caller does not use this) there.
#[test]
fn accumulate_batches() {
  fn check<C: TreeCurve>() {
    let table = C::table();
    let in_bucket =
      |points: &[Xy<C>], bucket| points.iter().map(|point| (bucket, *point)).collect::<Vec<_>>();
    for n in [1, 2, 3, 2 * tree::MIN_BATCH - 1, 2 * tree::MIN_BATCH, 2 * tree::MIN_BATCH + 1, 300] {
      let points = &table.points[.. n];
      let sums = tree::accumulate::<C>(1, &in_bucket(points, 0)).unwrap();
      assert_eq!(sums[0].unwrap(), sum::<C>(points), "{n} points");
    }

    // Spread over buckets, with an empty one
    let pending =
      table.points[.. 500].iter().enumerate().map(|(i, p)| (i % 3, *p)).collect::<Vec<_>>();
    let sums = tree::accumulate::<C>(4, &pending).unwrap();
    for (b, bucket) in sums.iter().enumerate() {
      let expected = pending.iter().filter(|(i, _)| *i == b).map(|(_, p)| *p).collect::<Vec<_>>();
      assert_eq!(bucket.is_some(), !expected.is_empty());
      if let Some(bucket) = bucket {
        assert_eq!(*bucket, sum::<C>(&expected));
      }
    }

    for negate in [false, true] {
      let flip = |(x, y): Xy<C>| (x, if negate { -y } else { y });
      // The first pair is a repeat
      let repeat = |n: usize| {
        let mut points = table.points[.. n].to_vec();
        points[1] = flip(points[0]);
        tree::accumulate::<C>(1, &in_bucket(&points, 0))
      };
      // The first round has fewer than the minimum of pairs, so complete additions are used
      assert_eq!(repeat(2 * (tree::MIN_BATCH - 1)).map(|sums| sums[0].is_some()), Some(true));
      // The first round is batched
      assert!(repeat(2 * tree::MIN_BATCH).is_none());

      // The first two sums of the first round are equal, and are paired in the second round
      let mut points = table.points[.. (4 * tree::MIN_BATCH)].to_vec();
      let first = sum::<C>(&points[.. 2]);
      let third = C::from_xy(points[3].0, points[3].1).unwrap();
      let wanted = if negate { -first } else { first } - third;
      points[2] = C::G::to_xy(wanted).unwrap();
      assert!(tree::accumulate::<C>(1, &in_bucket(&points, 0)).is_none());
    }
  }
  check::<Selene>();
  check::<Helios>();
}
