use std_shims::{sync::LazyLock, vec, vec::Vec};

use ciphersuite::{
  group::{
    ff::{Field as _, PrimeField as _, BatchInvert as _},
    Group as _,
  },
  Ciphersuite,
};
use helioselene::{Selene, Helios, SelenePoint, HeliosPoint};

use ec_divisors::{DivisorCurve, XyPoint as _};
use generalized_bulletproofs::Generators;

use fcmps::{LAYER_ONE_LEN, LAYER_TWO_LEN};

use crate::{SELENE_FCMP_GENERATORS, HELIOS_FCMP_GENERATORS};

// Table entries are `[2**(STEP * j)] G_i`, so one table serves windows of 4 and 8 bits.
const STEP: usize = 4;
// Scalars are encoded as 32 bytes. Signed digits need one window past them for the final carry.
const REPR_BITS: usize = 256;
const ENTRIES: usize = (REPR_BITS / STEP) + 1;
// Below this many scalars, 4-bit windows are faster than 8-bit windows.
const WIDE_WINDOW_SCALARS: usize = 12;
// Below this many pairs, an inversion costs more than it saves over complete additions.
pub(crate) const MIN_BATCH: usize = 32;

type Affine<G> = (<G as DivisorCurve>::FieldElement, <G as DivisorCurve>::FieldElement);

mod sealed {
  pub trait Sealed {}
  impl Sealed for helioselene::Selene {}
  impl Sealed for helioselene::Helios {}

  /// Affine multiples of the first generators of a set.
  pub struct Table<G: ec_divisors::DivisorCurve> {
    pub(crate) generators: usize,
    // `[2**(STEP * j)] G_i` is at `i * ENTRIES + j`
    pub(crate) points: std_shims::vec::Vec<super::Affine<G>>,
  }
}
use sealed::Table;

impl<G: DivisorCurve> Table<G> {
  fn new(generators: &[G]) -> Self {
    let mut points = Vec::with_capacity(generators.len() * ENTRIES);
    for generator in generators {
      let mut point = G::XyPoint::from(*generator);
      for _ in 0 .. ENTRIES {
        points.push(point);
        for _ in 0 .. STEP {
          point = point.double();
        }
      }
    }
    // None of these are the identity as the generators are of prime order and not the identity
    Table { generators: generators.len(), points: G::XyPoint::batch_to_xy(&points) }
  }
}

/// A curve whose tree hashes use the FCMP++ generators and precomputed tables.
pub trait TreeCurve: sealed::Sealed + Ciphersuite<G: DivisorCurve> {
  #[doc(hidden)]
  fn generators() -> &'static Generators<Self>;
  #[doc(hidden)]
  fn table() -> &'static Table<Self::G>;
  #[doc(hidden)]
  fn from_xy(
    x: <Self::G as DivisorCurve>::FieldElement,
    y: <Self::G as DivisorCurve>::FieldElement,
  ) -> Option<Self::G>;
}

fn table_for<C: Ciphersuite<G: DivisorCurve>>(generators: &Generators<C>, n: usize) -> Table<C::G> {
  let g_bold = generators.g_bold_slice();
  Table::new(&g_bold[.. n.min(g_bold.len())])
}

// 6 * LAYER_ONE_LEN Selene generators for leaf chunks, LAYER_TWO_LEN Helios generators
static SELENE_TABLE: LazyLock<Table<SelenePoint>> =
  LazyLock::new(|| table_for(&SELENE_FCMP_GENERATORS.generators, 6 * LAYER_ONE_LEN));
static HELIOS_TABLE: LazyLock<Table<HeliosPoint>> =
  LazyLock::new(|| table_for(&HELIOS_FCMP_GENERATORS.generators, LAYER_TWO_LEN));

impl TreeCurve for Selene {
  fn generators() -> &'static Generators<Self> {
    &SELENE_FCMP_GENERATORS.generators
  }
  fn table() -> &'static Table<SelenePoint> {
    &SELENE_TABLE
  }
  fn from_xy(
    x: <SelenePoint as DivisorCurve>::FieldElement,
    y: <SelenePoint as DivisorCurve>::FieldElement,
  ) -> Option<SelenePoint> {
    SelenePoint::from_xy(x, y).into()
  }
}

impl TreeCurve for Helios {
  fn generators() -> &'static Generators<Self> {
    &HELIOS_FCMP_GENERATORS.generators
  }
  fn table() -> &'static Table<HeliosPoint> {
    &HELIOS_TABLE
  }
  fn from_xy(
    x: <HeliosPoint as DivisorCurve>::FieldElement,
    y: <HeliosPoint as DivisorCurve>::FieldElement,
  ) -> Option<HeliosPoint> {
    HeliosPoint::from_xy(x, y).into()
  }
}

// Sum the points in each bucket.
//
// Rounds of pairwise additions within buckets share one inversion, while enough pairs remain for
// that to be faster. Returns `None` if two points to add in such a round share an `x` coordinate,
// or if a sum is not on the curve.
pub(crate) fn accumulate<C: TreeCurve>(
  buckets: usize,
  pending: &[(usize, Affine<C::G>)],
) -> Option<Vec<Option<C::G>>> {
  let mut start = vec![0; buckets + 1];
  for (bucket, _) in pending {
    start[bucket + 1] += 1;
  }
  for b in 0 .. buckets {
    start[b + 1] += start[b];
  }
  let mut len = (0 .. buckets).map(|b| start[b + 1] - start[b]).collect::<Vec<_>>();
  let zero = <C::G as DivisorCurve>::FieldElement::ZERO;
  let mut points = vec![(zero, zero); pending.len()];
  {
    let mut next = start.clone();
    for (bucket, point) in pending {
      points[next[*bucket]] = *point;
      next[*bucket] += 1;
    }
  }

  let mut denominators = Vec::with_capacity(pending.len() / 2);
  loop {
    if len.iter().map(|l| l / 2).sum::<usize>() < MIN_BATCH {
      break;
    }
    denominators.clear();
    for b in 0 .. buckets {
      let points = &points[start[b] .. (start[b] + len[b])];
      for pair in points.chunks_exact(2) {
        let denominator = pair[1].0 - pair[0].0;
        if bool::from(denominator.is_zero()) {
          None?;
        }
        denominators.push(denominator);
      }
    }
    denominators.iter_mut().batch_invert();

    let mut denominators = denominators.iter();
    for b in 0 .. buckets {
      let s = start[b];
      let l = len[b];
      for i in 0 .. (l / 2) {
        let (x1, y1) = points[s + (2 * i)];
        let (x2, y2) = points[s + (2 * i) + 1];
        let lambda = (y2 - y1) * denominators.next()?;
        let x3 = lambda.square() - x1 - x2;
        let y3 = (lambda * (x1 - x3)) - y1;
        points[s + i] = (x3, y3);
      }
      if (l % 2) == 1 {
        points[s + (l / 2)] = points[s + l - 1];
      }
      len[b] = l.div_ceil(2);
    }
  }

  let mut sums = Vec::with_capacity(buckets);
  for b in 0 .. buckets {
    let mut sum = None;
    for (x, y) in &points[start[b] .. (start[b] + len[b])] {
      let point = C::from_xy(*x, *y)?;
      sum = Some(sum.map(|sum| sum + point).unwrap_or(point));
    }
    sums.push(sum);
  }
  Some(sums)
}

// `sum scalars[i] * G_{offset + i}`, for generators within the table.
//
// Returns `None` if this should be computed without the table.
pub(crate) fn table_multiexp<C: TreeCurve>(
  offset: usize,
  first: C::F,
  rest: &[C::F],
) -> Option<C::G> {
  let table = C::table();
  let n = rest.len() + 1;
  if offset.checked_add(n)? > table.generators {
    None?;
  }

  let window = if n < WIDE_WINDOW_SCALARS { 4 } else { 8 };
  let stride = window / STEP;
  let windows = (REPR_BITS / window) + 1;
  let half = 1 << (window - 1);
  let mask = (1 << window) - 1;

  let mut pending = Vec::with_capacity(n * windows);
  for (i, scalar) in core::iter::once(first).chain(rest.iter().copied()).enumerate() {
    if bool::from(scalar.is_zero()) {
      continue;
    }
    let repr = scalar.to_repr();
    let repr = repr.as_ref();
    if repr.len() > (REPR_BITS / 8) {
      None?;
    }
    let entries = &table.points[((offset + i) * ENTRIES) .. ((offset + i + 1) * ENTRIES)];
    // Signed digits in `[-half, half)`. The last window is past the encoding, so its digit is the
    // carry and the carry out of it is zero.
    let mut carry = 0;
    for j in 0 .. windows {
      let bit = j * window;
      let byte = u32::from(repr.get(bit / 8).copied().unwrap_or(0));
      let mut digit = ((byte >> (bit % 8)) & mask) + carry;
      carry = 0;
      let negative = digit >= half;
      if negative {
        digit = (1 << window) - digit;
        carry = 1;
      }
      if digit == 0 {
        continue;
      }
      let (x, y) = entries[j * stride];
      let bucket = usize::try_from(digit - 1).ok()?;
      pending.push((bucket, (x, if negative { -y } else { y })));
    }
  }

  let buckets = accumulate::<C>(half.try_into().ok()?, &pending)?;

  // sum (b + 1) * buckets[b]
  let mut running = C::G::identity();
  let mut sum = C::G::identity();
  let mut started = false;
  for bucket in buckets.into_iter().rev() {
    if let Some(bucket) = bucket {
      running += bucket;
      started = true;
    }
    if started {
      sum += running;
    }
  }
  Some(sum)
}

/// Add children to an existing hash.
///
/// This is equivalent to `fcmps::tree::hash_grow` with the FCMP++ generators for this curve.
pub fn hash_grow<C: TreeCurve>(
  existing_hash: C::G,
  offset: usize,
  existing_child_at_offset: C::F,
  new_children: &[C::F],
) -> Option<C::G> {
  if let Some((first, rest)) = new_children.split_first() {
    if let Some(sum) = table_multiexp::<C>(offset, *first - existing_child_at_offset, rest) {
      return Some(existing_hash + sum);
    }
  }
  fcmps::tree::hash_grow(
    C::generators(),
    existing_hash,
    offset,
    existing_child_at_offset,
    new_children,
  )
}

/// Remove children from an existing hash, and grow back one child.
///
/// This is equivalent to `fcmps::tree::hash_trim` with the FCMP++ generators for this curve.
pub fn hash_trim<C: TreeCurve>(
  existing_hash: C::G,
  offset: usize,
  children: &[C::F],
  child_to_grow_back: C::F,
) -> Option<C::G> {
  if let Some((first, rest)) = children.split_first() {
    if let Some(sum) = table_multiexp::<C>(offset, *first - child_to_grow_back, rest) {
      return Some(existing_hash - sum);
    }
  }
  fcmps::tree::hash_trim(C::generators(), existing_hash, offset, children, child_to_grow_back)
}
