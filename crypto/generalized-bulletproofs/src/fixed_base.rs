#![allow(clippy::many_single_char_names)]

// Variable-time multiscalar multiplication for `Generators::verify`.
//
// Fixed generators: Brickell-Gordon-McCurley-Wilson tables holding `2^(W j) G` for every window
// `j`, so every digit of every fixed term lands in one shared set of buckets.
// Other points: interleaved wNAF (Straus) or signed-window Pippenger.
// Bucket sums use batch-affine additions (one inversion per round).
//
// Any unexpected state (a zero denominator, an inconsistent point) returns `None`, and the caller
// falls back to `multiexp_vartime`.

use core::mem::size_of;

use std_shims::{
  vec,
  vec::Vec,
  prelude::Box,
  sync::{Arc, LazyLock},
};

use ciphersuite::{
  group::ff::{Field, PrimeField},
  Ciphersuite,
};
use multiexp::multiexp_vartime;
use ec_divisors::DivisorCurve;

use crate::{BatchVerifier, Generators};

type Aff<F> = (F, F);

/// Window width of the fixed-base tables.
const W: usize = 10;
/// Upper bound, in bytes, on the tables of one `Generators`.
pub(crate) const TABLE_BYTES: usize = 8 << 20;

#[derive(Clone, Copy)]
struct Jac<F> {
  x: F,
  y: F,
  z: F,
}

impl<F: Field> Jac<F> {
  fn identity() -> Self {
    Jac { x: F::ONE, y: F::ONE, z: F::ZERO }
  }

  fn is_identity(&self) -> bool {
    bool::from(self.z.is_zero())
  }

  fn matches<G: DivisorCurve<FieldElement = F>>(&self, p: G) -> bool {
    let (x, y, z) = G::to_xyz(p);
    if self.is_identity() || bool::from(z.is_zero()) {
      return self.is_identity() && bool::from(z.is_zero());
    }
    let z2 = self.z.square();
    (self.x * z == x * z2) && (self.y * z == y * z2 * self.z)
  }

  // dbl-2007-bl
  fn double(&self, a: F) -> Self {
    if self.is_identity() {
      return *self;
    }
    let xx = self.x.square();
    let yy = self.y.square();
    let yyyy = yy.square();
    let zz = self.z.square();
    let s = ((self.x + yy).square() - xx - yyyy).double();
    let m = xx.double() + xx + (a * zz.square());
    let x3 = m.square() - s.double();
    let y3 = (m * (s - x3)) - yyyy.double().double().double();
    let z3 = (self.y + self.z).square() - yy - zz;
    Jac { x: x3, y: y3, z: z3 }
  }

  // madd-2007-bl
  fn add_affine(&self, p: &Aff<F>, a: F) -> Self {
    if self.is_identity() {
      return Jac { x: p.0, y: p.1, z: F::ONE };
    }
    let z1z1 = self.z.square();
    let u2 = p.0 * z1z1;
    let s2 = p.1 * self.z * z1z1;
    let h = u2 - self.x;
    let r = (s2 - self.y).double();
    if bool::from(h.is_zero()) {
      if bool::from(r.is_zero()) {
        return self.double(a);
      }
      return Self::identity();
    }
    let hh = h.square();
    let i = hh.double().double();
    let j = h * i;
    let v = self.x * i;
    let x3 = r.square() - j - v.double();
    let y3 = (r * (v - x3)) - (self.y * j).double();
    let z3 = (self.z + h).square() - z1z1 - hh;
    Jac { x: x3, y: y3, z: z3 }
  }

  // add-2007-bl
  fn add(&self, o: &Self, a: F) -> Self {
    if self.is_identity() {
      return *o;
    }
    if o.is_identity() {
      return *self;
    }
    let z1z1 = self.z.square();
    let z2z2 = o.z.square();
    let u1 = self.x * z2z2;
    let u2 = o.x * z1z1;
    let s1 = self.y * o.z * z2z2;
    let s2 = o.y * self.z * z1z1;
    let h = u2 - u1;
    let r = (s2 - s1).double();
    if bool::from(h.is_zero()) {
      if bool::from(r.is_zero()) {
        return self.double(a);
      }
      return Self::identity();
    }
    let i = h.double().square();
    let j = h * i;
    let v = u1 * i;
    let x3 = r.square() - j - v.double();
    let y3 = (r * (v - x3)) - (s1 * j).double();
    let z3 = ((self.z + o.z).square() - z1z1 - z2z2) * h;
    Jac { x: x3, y: y3, z: z3 }
  }
}

/// Invert every element in place. `None` if any element is zero.
fn batch_invert<F: Field>(v: &mut [F], scratch: &mut Vec<F>) -> Option<()> {
  scratch.clear();
  let mut acc = F::ONE;
  for x in v.iter() {
    scratch.push(acc);
    acc *= x;
  }
  let mut inv: F = Option::from(acc.invert())?;
  for (x, s) in v.iter_mut().zip(scratch.iter()).rev() {
    let t = inv * *x;
    *x = inv * s;
    inv = t;
  }
  Some(())
}

/// Affine coordinates, `None` for the identity.
fn to_affine<G: DivisorCurve>(points: &[G]) -> Option<Vec<Option<Aff<G::FieldElement>>>> {
  let mut xyz = Vec::with_capacity(points.len());
  let mut zs = Vec::with_capacity(points.len());
  for p in points {
    let (x, y, z) = G::to_xyz(*p);
    let identity = bool::from(z.is_zero());
    if identity != bool::from(p.is_identity()) {
      None?;
    }
    if !identity {
      zs.push(z);
    }
    xyz.push((x, y, identity));
  }
  // Points read from a proof have `Z = 1`
  if zs.iter().any(|z| *z != G::FieldElement::ONE) {
    batch_invert(&mut zs, &mut Vec::new())?;
  }
  let mut zs = zs.into_iter();
  let mut res = Vec::with_capacity(points.len());
  for (x, y, identity) in xyz {
    res.push(if identity {
      None
    } else {
      let z = zs.next()?;
      Some((x * z, y * z))
    });
  }
  Some(res)
}

#[derive(Clone, Copy)]
enum Pair {
  Add,
  Double,
  Cancel,
}

fn classify<F: Field>(p: &Aff<F>, q: &Aff<F>, denoms: &mut Vec<F>) -> Pair {
  if p.0 == q.0 {
    // Equal `x`: `q = p` or `q = -p` (`y = 0` is a point of order two)
    if (p.1 == q.1) && !bool::from(p.1.is_zero()) {
      denoms.push(p.1.double());
      Pair::Double
    } else {
      Pair::Cancel
    }
  } else {
    denoms.push(q.0 - p.0);
    Pair::Add
  }
}

/// `p + q` given the inverted denominator from `classify`.
fn apply<F: Field>(kind: Pair, p: &Aff<F>, q: &Aff<F>, inv: F, a: F) -> Aff<F> {
  let lambda = match kind {
    Pair::Double => (p.0.square().double() + p.0.square() + a) * inv,
    Pair::Add | Pair::Cancel => (q.1 - p.1) * inv,
  };
  let x3 = lambda.square() - p.0 - q.0;
  (x3, (lambda * (p.0 - x3)) - p.1)
}

/// Sum the points of each bucket, `pending` being `(bucket, point)` with `bucket < buckets`.
///
/// Pairs within each bucket are added with one shared inversion per round until every bucket
/// holds at most one point. Returns each bucket's sum, `None` for the identity.
fn accumulate<F: Field>(
  pending: &[(usize, Aff<F>)],
  buckets: usize,
  a: F,
) -> Option<Vec<Option<Aff<F>>>> {
  let mut start = vec![0usize; buckets + 1];
  for (b, _) in pending {
    *start.get_mut(b + 1)? += 1;
  }
  for i in 0 .. buckets {
    start[i + 1] += start[i];
  }
  let mut lists = vec![(F::ZERO, F::ZERO); pending.len()];
  let mut len = vec![0usize; buckets];
  for (b, p) in pending {
    lists[start[*b] + len[*b]] = *p;
    len[*b] += 1;
  }

  let mut active: Vec<usize> = (0 .. buckets).filter(|b| len[*b] >= 2).collect();
  let mut kinds = Vec::with_capacity(pending.len() / 2);
  let mut denoms = Vec::with_capacity(pending.len() / 2);
  let mut scratch = Vec::with_capacity(pending.len() / 2);
  while !active.is_empty() {
    kinds.clear();
    denoms.clear();
    for &b in &active {
      let list = &lists[start[b] .. (start[b] + len[b])];
      for pair in list.chunks_exact(2) {
        kinds.push(classify(&pair[0], &pair[1], &mut denoms));
      }
    }
    batch_invert(&mut denoms, &mut scratch)?;

    let mut kinds = kinds.iter();
    let mut invs = denoms.iter();
    let mut next = Vec::with_capacity(active.len());
    for &b in &active {
      let s = start[b];
      let l = len[b];
      let mut out = s;
      let mut i = 0;
      while (i + 1) < l {
        let (p, q) = (lists[s + i], lists[s + i + 1]);
        let kind = *kinds.next()?;
        if !matches!(kind, Pair::Cancel) {
          lists[out] = apply(kind, &p, &q, *invs.next()?, a);
          out += 1;
        }
        i += 2;
      }
      if i < l {
        lists[out] = lists[s + i];
        out += 1;
      }
      len[b] = out - s;
      if len[b] >= 2 {
        next.push(b);
      }
    }
    active = next;
  }
  Some((0 .. buckets).map(|b| (len[b] == 1).then(|| lists[start[b]])).collect())
}

/// `sum_k (k + 1) buckets[k]`.
fn reduce_buckets<F: Field>(buckets: &[Option<Aff<F>>], a: F) -> Jac<F> {
  let mut running = Jac::identity();
  let mut res = Jac::identity();
  for bucket in buckets.iter().rev() {
    if let Some(bucket) = bucket {
      running = running.add_affine(bucket, a);
    }
    res = res.add(&running, a);
  }
  res
}

/// The number of `w`-bit signed windows which represent any scalar, including the final carry.
fn windows<S: PrimeField>(w: usize) -> usize {
  (usize::try_from(S::NUM_BITS).unwrap_or(usize::MAX - w) + w) / w
}

/// If `to_repr` is the little-endian encoding, as `recode` and `wnaf` read it.
fn little_endian<S: PrimeField>() -> bool {
  let bits = usize::try_from(S::NUM_BITS).unwrap_or(usize::MAX);
  let mut power = S::ONE;
  for i in 0 .. bits {
    let repr = power.to_repr();
    let bytes = repr.as_ref();
    if bytes.len().saturating_mul(8) < bits {
      return false;
    }
    for (k, byte) in bytes.iter().enumerate() {
      if *byte != if k == (i / 8) { 1 << (i % 8) } else { 0 } {
        return false;
      }
    }
    power = power.double();
  }
  true
}

/// `|d| - 1` for a non-zero digit.
fn magnitude(d: i32) -> Option<usize> {
  usize::try_from(d.unsigned_abs()).ok()?.checked_sub(1)
}

/// Signed digits in `(-2^(w - 1), 2^(w - 1)]` with `s = sum_j digits[j] 2^(w j)`.
fn recode<S: PrimeField>(s: &S, w: usize, digits: &mut [i32]) -> Option<()> {
  let repr = s.to_repr();
  let bytes = repr.as_ref();
  let half = 1i32 << (w - 1);
  let mask = (1u32 << w) - 1;
  let mut carry = 0;
  for (j, digit) in digits.iter_mut().enumerate() {
    let bit = j * w;
    let mut v = 0u32;
    for k in 0 .. 4 {
      if let Some(byte) = bytes.get((bit / 8) + k) {
        v |= u32::from(*byte) << (8 * k);
      }
    }
    let mut d = i32::try_from((v >> (bit % 8)) & mask).ok()? + carry;
    carry = 0;
    if d > half {
      d -= 1 << w;
      carry = 1;
    }
    *digit = d;
  }
  (carry == 0).then_some(())
}

/// Width-`w` NAF: odd digits in `(-2^(w - 1), 2^(w - 1))`, least significant first.
fn wnaf<S: PrimeField>(s: &S, w: usize, digits: &mut Vec<i32>) -> Option<()> {
  let repr = s.to_repr();
  let bytes = repr.as_ref();
  let mut k = vec![0u64; bytes.len().div_ceil(8) + 1];
  for (i, byte) in bytes.iter().enumerate() {
    k[i / 8] |= u64::from(*byte) << (8 * (i % 8));
  }
  let full = 1u64 << w;
  let half = 1u64 << (w - 1);
  digits.clear();
  while k.iter().any(|limb| *limb != 0) {
    let mut d = 0;
    if (k[0] & 1) == 1 {
      let m = k[0] & (full - 1);
      if m < half {
        d = i32::try_from(m).ok()?;
        k[0] -= m;
      } else {
        d = -i32::try_from(full - m).ok()?;
        let (sum, mut carry) = k[0].overflowing_add(full - m);
        k[0] = sum;
        for limb in &mut k[1 ..] {
          if !carry {
            break;
          }
          (*limb, carry) = limb.overflowing_add(1);
        }
        if carry {
          None?;
        }
      }
    }
    digits.push(d);
    for i in 0 .. k.len() {
      k[i] = (k[i] >> 1) | k.get(i + 1).map(|next| next << 63).unwrap_or(0);
    }
  }
  Some(())
}

/// `P + Q` for many pairs with one inversion. `None` is the identity.
#[allow(clippy::type_complexity)]
fn batch_add<F: Field>(
  pairs: &[(Option<Aff<F>>, Option<Aff<F>>)],
  a: F,
) -> Option<Vec<Option<Aff<F>>>> {
  let mut kinds = Vec::with_capacity(pairs.len());
  let mut denoms = Vec::with_capacity(pairs.len());
  for pair in pairs {
    kinds.push(match pair {
      (Some(p), Some(q)) => Some(classify(p, q, &mut denoms)),
      _ => None,
    });
  }
  batch_invert(&mut denoms, &mut Vec::new())?;
  let mut invs = denoms.iter();
  let mut res = Vec::with_capacity(pairs.len());
  for (pair, kind) in pairs.iter().zip(kinds) {
    res.push(match (pair, kind) {
      ((Some(p), Some(q)), Some(kind)) => match kind {
        Pair::Cancel => None,
        Pair::Add | Pair::Double => Some(apply(kind, p, q, *invs.next()?, a)),
      },
      ((p, q), _) => p.or(*q),
    });
  }
  Some(res)
}

/// Interleaved wNAF over non-identity points, with batch-affine sums per bit position.
fn straus<F: Field, S: PrimeField>(
  scalars: &[S],
  points: &[Aff<F>],
  w: usize,
  a: F,
) -> Option<Jac<F>> {
  // (2k + 1) P_i at i * size + k
  let size = 1usize << (w - 2);
  let mut table = vec![None; points.len().checked_mul(size)?];
  for (i, p) in points.iter().enumerate() {
    table[i * size] = Some(*p);
  }
  if size > 1 {
    let doubles = batch_add(&points.iter().map(|p| (Some(*p), Some(*p))).collect::<Vec<_>>(), a)?;
    for k in 1 .. size {
      let pairs: Vec<_> =
        (0 .. points.len()).map(|i| (table[(i * size) + k - 1], doubles[i])).collect();
      for (i, sum) in batch_add(&pairs, a)?.into_iter().enumerate() {
        table[(i * size) + k] = sum;
      }
    }
  }

  let mut pending = Vec::with_capacity(points.len() * (2 + (256 / (w + 1))));
  let mut naf = Vec::with_capacity(260);
  let mut positions = 0;
  for (i, s) in scalars.iter().enumerate() {
    wnaf(s, w, &mut naf)?;
    positions = positions.max(naf.len());
    for (t, d) in naf.iter().enumerate() {
      if *d == 0 {
        continue;
      }
      let index = (i * size) + (magnitude(*d)? / 2);
      if let Some(p) = table.get(index)? {
        pending.push((t, if *d > 0 { *p } else { (p.0, -p.1) }));
      }
    }
  }
  let sums = accumulate(&pending, positions, a)?;
  let mut res = Jac::identity();
  for sum in sums.iter().rev() {
    res = res.double(a);
    if let Some(sum) = sum {
      res = res.add_affine(sum, a);
    }
  }
  Some(res)
}

/// Signed-window Pippenger over non-identity points, with batch-affine buckets.
fn pippenger<F: Field, S: PrimeField>(
  scalars: &[S],
  points: &[Aff<F>],
  w: usize,
  a: F,
) -> Option<Jac<F>> {
  let windows = windows::<S>(w);
  let half = 1usize << (w - 1);
  let mut pending = Vec::with_capacity(points.len().saturating_mul(windows));
  let mut digits = vec![0i32; windows];
  for (s, p) in scalars.iter().zip(points) {
    recode(s, w, &mut digits)?;
    for (j, d) in digits.iter().enumerate() {
      if *d != 0 {
        let bucket = (j * half) + magnitude(*d)?;
        pending.push((bucket, if *d > 0 { *p } else { (p.0, -p.1) }));
      }
    }
  }
  let buckets = accumulate(&pending, windows.checked_mul(half)?, a)?;
  let mut res = Jac::identity();
  for window in buckets.chunks_exact(half).rev() {
    for _ in 0 .. w {
      res = res.double(a);
    }
    res = res.add(&reduce_buckets(window, a), a);
  }
  Some(res)
}

/// The most points handled at once by `variable_msm`, bounding the memory of its buckets.
const VARIABLE_CHUNK: usize = 8192;

/// `sum scalars[i] points[i]` for arbitrary points, with the method and width of least cost.
fn variable_msm<F: Field, S: PrimeField>(scalars: &[S], points: &[Aff<F>], a: F) -> Option<Jac<F>> {
  let mut res = Jac::identity();
  for (scalars, points) in scalars.chunks(VARIABLE_CHUNK).zip(points.chunks(VARIABLE_CHUNK)) {
    res = res.add(&variable_msm_chunk(scalars, points, a)?, a);
  }
  Some(res)
}

fn variable_msm_chunk<F: Field, S: PrimeField>(
  scalars: &[S],
  points: &[Aff<F>],
  a: F,
) -> Option<Jac<F>> {
  let n = u64::try_from(points.len()).ok()?;
  if n == 0 {
    return Some(Jac::identity());
  }
  // Costs in affine additions
  let straus_cost = |w: u64| {
    n.saturating_mul(1 << (w - 2))
      .saturating_add(n.saturating_mul(256) / (w + 1))
      .saturating_add(768)
  };
  let pippenger_cost = |w: u64| {
    (n.saturating_mul(256) / w)
      .saturating_add((256 / w).saturating_mul(1 << (w + 1)))
      .saturating_add(384)
  };
  let (straus_w, straus_min) = (3 ..= 7).map(|w| (w, straus_cost(w))).min_by_key(|(_, c)| *c)?;
  let (pippenger_w, pippenger_min) =
    (4 ..= 14).map(|w| (w, pippenger_cost(w))).min_by_key(|(_, c)| *c)?;
  if straus_min <= pippenger_min {
    straus(scalars, points, usize::try_from(straus_w).ok()?, a)
  } else {
    pippenger(scalars, points, usize::try_from(pippenger_w).ok()?, a)
  }
}

/// Tables for a prefix of the generators.
struct Tables<F> {
  w: usize,
  windows: usize,
  /// `g_bold`/`h_bold` generators covered
  n: usize,
  /// `h_sum` entries covered
  n_h_sum: usize,
  /// Entry `(i, j)`, `2^(w j)` times fixed base `i`, at `i * windows + j`. The fixed bases are
  /// `g, h, g_bold[.. n], h_bold[.. n], h_sum[.. n_h_sum]`.
  points: Vec<Aff<F>>,
}

impl<F: Field> Tables<F> {
  fn new<G: DivisorCurve<FieldElement = F>>(
    bases: &[G],
    w: usize,
    n: usize,
    n_h_sum: usize,
  ) -> Option<Self> {
    if !little_endian::<G::Scalar>() {
      None?;
    }
    let windows = windows::<G::Scalar>(w);
    let a = G::a();
    let mut current = to_affine(bases)?.into_iter().collect::<Option<Vec<_>>>()?;
    let mut points = vec![(F::ZERO, F::ZERO); current.len().checked_mul(windows)?];
    let mut denoms = Vec::with_capacity(current.len());
    let mut scratch = Vec::with_capacity(current.len());
    for j in 0 .. windows {
      for (i, p) in current.iter().enumerate() {
        points[(i * windows) + j] = *p;
      }
      if (j + 1) == windows {
        break;
      }
      for _ in 0 .. w {
        denoms.clear();
        for p in &current {
          if bool::from(p.1.is_zero()) {
            None?;
          }
          denoms.push(p.1.double());
        }
        batch_invert(&mut denoms, &mut scratch)?;
        for (p, inv) in current.iter_mut().zip(&denoms) {
          *p = apply(Pair::Double, p, p, *inv, a);
        }
      }
    }

    // Check the last entry of the first and last base against the group's own arithmetic
    for (i, base) in [(0, bases.first()?), (bases.len() - 1, bases.last()?)] {
      let mut expected = *base;
      for _ in 0 .. (w * (windows - 1)) {
        expected = expected.double();
      }
      let (x, y, z) = G::to_xyz(expected);
      let entry = points.get((i * windows) + windows - 1)?;
      if (x != (entry.0 * z)) || (y != (entry.1 * z)) || bool::from(z.is_zero()) {
        None?;
      }
    }

    Some(Tables { w, windows, n, n_h_sum, points })
  }

  /// Compare `msm` against `multiexp_vartime` for pseudo-random scalars over every base.
  ///
  /// A scalar's digit in a window is nonzero with overwhelming probability, so this reads
  /// essentially every entry, and an incorrect entry changes the sum.
  fn check<C: Ciphersuite>(&self, bases: &[C::G]) -> Option<()>
  where
    C::G: DivisorCurve<FieldElement = F>,
  {
    let mut scalar = C::F::from(0x9e37_79b9_7f4a_7c15);
    let scalars = (0 .. bases.len())
      .map(|i| {
        scalar = scalar.square() + C::F::from(u64::try_from(i).unwrap_or(u64::MAX));
        scalar
      })
      .collect::<Vec<_>>();
    let terms = scalars.iter().copied().enumerate().collect::<Vec<_>>();
    let expected =
      multiexp_vartime(&scalars.into_iter().zip(bases.iter().copied()).collect::<Vec<_>>());
    self.msm(&terms, C::G::a())?.matches(expected).then_some(())
  }

  /// `sum s_i B_i` over fixed bases given as `(index, s_i)`.
  fn msm<S: PrimeField>(&self, terms: &[(usize, S)], a: F) -> Option<Jac<F>> {
    let half = 1usize << (self.w - 1);
    let mut pending = Vec::with_capacity(terms.len().saturating_mul(self.windows));
    let mut digits = vec![0i32; self.windows];
    for (i, s) in terms {
      if bool::from(s.is_zero()) {
        continue;
      }
      recode(s, self.w, &mut digits)?;
      let row = self.points.get((i * self.windows) .. ((i + 1) * self.windows))?;
      for (d, p) in digits.iter().zip(row) {
        if *d != 0 {
          pending.push((magnitude(*d)?, if *d > 0 { *p } else { (p.0, -p.1) }));
        }
      }
    }
    Some(reduce_buckets(&accumulate(&pending, half, a)?, a))
  }
}

pub(crate) trait VerifyTables<C: Ciphersuite>: Send + Sync {
  /// Whether the multiexp `Generators::verify` checks is the identity, if it could be evaluated.
  fn verify(&self, generators: &Generators<C>, verifier: &BatchVerifier<C>) -> Option<bool>;
}

type Build<F> = Box<dyn FnOnce() -> Option<Tables<F>> + Send>;

/// Tables built on first use.
pub(crate) struct LazyTables<F: Field>(LazyLock<Option<Tables<F>>, Build<F>>);

/// Tables for the largest power-of-two prefix of `g_bold`/`h_bold` within `TABLE_BYTES`.
pub(crate) fn verification_tables<C: Ciphersuite>(
  generators: &Generators<C>,
) -> Option<Arc<dyn VerifyTables<C>>>
where
  C::G: DivisorCurve,
{
  let tables: Arc<dyn VerifyTables<C>> = Arc::new(LazyTables::new(generators)?);
  Some(tables)
}

impl<F: Field> LazyTables<F> {
  fn new<C: Ciphersuite>(generators: &Generators<C>) -> Option<Self>
  where
    C::G: DivisorCurve<FieldElement = F>,
  {
    Self::with_cap(generators, TABLE_BYTES)
  }

  fn with_cap<C: Ciphersuite>(generators: &Generators<C>, table_bytes: usize) -> Option<Self>
  where
    C::G: DivisorCurve<FieldElement = F>,
  {
    let per_base = windows::<C::F>(W).saturating_mul(size_of::<Aff<F>>());
    let max_bases = table_bytes / per_base.max(1);
    let n_h_sum = generators.h_sum.len();
    let mut n = generators.g_bold.len().min(generators.h_bold.len());
    while (n > 0) && (2 + (2 * n) + n_h_sum) > max_bases {
      n /= 2;
    }
    if (2 + n_h_sum) > max_bases {
      None?;
    }
    let mut bases = Vec::with_capacity(2 + (2 * n) + n_h_sum);
    bases.push(generators.g);
    bases.push(generators.h);
    bases.extend(&generators.g_bold[.. n]);
    bases.extend(&generators.h_bold[.. n]);
    bases.extend(&generators.h_sum);
    let build: Build<F> = Box::new(move || {
      let tables = Tables::new::<C::G>(&bases, W, n, n_h_sum)?;
      tables.check::<C>(&bases)?;
      Some(tables)
    });
    Some(LazyTables(LazyLock::new(build)))
  }
}

impl<C: Ciphersuite> VerifyTables<C> for LazyTables<<C::G as DivisorCurve>::FieldElement>
where
  C::G: DivisorCurve,
{
  fn verify(&self, generators: &Generators<C>, verifier: &BatchVerifier<C>) -> Option<bool> {
    let tables = (*self.0).as_ref()?;
    let n = tables.n;
    let a = <C::G as DivisorCurve>::a();

    // The same terms as `Generators::verify`, including its truncation to the shorter list
    let mut fixed = Vec::with_capacity(2 + (2 * n) + tables.n_h_sum);
    let mut scalars = Vec::with_capacity(verifier.additional.len());
    let mut points = Vec::with_capacity(verifier.additional.len());
    let mut variable = |s: C::F, p: C::G| {
      if !bool::from(s.is_zero()) {
        scalars.push(s);
        points.push(p);
      }
    };
    fixed.push((0, verifier.g));
    fixed.push((1, verifier.h));
    for (i, (s, p)) in verifier.g_bold.iter().zip(&generators.g_bold).enumerate() {
      if i < n {
        fixed.push((2 + i, *s));
      } else {
        variable(*s, *p);
      }
    }
    for (i, (s, p)) in verifier.h_bold.iter().zip(&generators.h_bold).enumerate() {
      if i < n {
        fixed.push((2 + n + i, *s));
      } else {
        variable(*s, *p);
      }
    }
    for (i, (s, p)) in verifier.h_sum.iter().zip(&generators.h_sum).enumerate() {
      if i < tables.n_h_sum {
        fixed.push((2 + (2 * n) + i, *s));
      } else {
        variable(*s, *p);
      }
    }
    for (s, p) in &verifier.additional {
      variable(*s, *p);
    }

    let fixed = tables.msm(&fixed, a)?;
    let affine = to_affine(&points)?;
    let (scalars, points): (Vec<_>, Vec<_>) =
      scalars.into_iter().zip(affine).filter_map(|(s, p)| Some((s, p?))).unzip();
    let variable = variable_msm(&scalars, &points, a)?;
    Some(fixed.add(&variable, a).is_identity())
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use rand_core::{OsRng, RngCore as _};
  use ciphersuite::group::{ff::PrimeFieldBits, Group as _};
  use multiexp::multiexp_vartime;

  use crate::tests::insecure_test_generators;

  fn eq<G: DivisorCurve>(j: &Jac<G::FieldElement>, p: G) -> bool {
    j.matches(p)
  }

  fn from_i64<S: PrimeField>(d: i64) -> S {
    if d >= 0 {
      S::from(d.unsigned_abs())
    } else {
      -S::from(d.unsigned_abs())
    }
  }

  /// Zero, one, powers of two and their neighbours, and digit patterns at every width.
  fn edge_scalars<S: PrimeField>() -> Vec<S> {
    let mut res = vec![S::ZERO, S::ONE, -S::ONE, S::TWO_INV, -S::TWO_INV];
    let mut power = S::ONE;
    for _ in 0 .. S::NUM_BITS {
      res.extend([power, power - S::ONE, -power]);
      power = power.double();
    }
    for w in 2 .. 16 {
      let half = 1i64 << (w - 1);
      for pattern in 0 .. 6 {
        let mut acc = S::ZERO;
        for j in (0 ..= (256 / w)).rev() {
          for _ in 0 .. w {
            acc = acc.double();
          }
          acc += from_i64::<S>(match pattern {
            0 => half,
            1 => half + 1,
            2 => (2 * half) - 1,
            3 => 1 - half,
            4 => {
              if j % 2 == 0 {
                half
              } else {
                -half
              }
            }
            _ => i64::try_from(OsRng.next_u64() % (2 * half.unsigned_abs())).unwrap() - half,
          });
        }
        res.push(acc);
      }
    }
    res
  }

  /// Every method and width against `multiexp_vartime`. Returns the number of comparisons.
  fn check<G: DivisorCurve>(scalars: &[G::Scalar], points: &[G]) -> usize
  where
    G::Scalar: PrimeFieldBits,
  {
    let a = G::a();
    let expected =
      multiexp_vartime(&scalars.iter().copied().zip(points.iter().copied()).collect::<Vec<_>>());
    let affine = to_affine(points).unwrap();
    let (s, p): (Vec<_>, Vec<_>) = scalars
      .iter()
      .zip(&affine)
      .filter(|(s, _)| !bool::from(s.is_zero()))
      .filter_map(|(s, p)| Some((*s, (*p)?)))
      .unzip();
    let mut checks = 0;
    for w in 3 ..= 7 {
      assert!(eq(&straus(&s, &p, w, a).unwrap(), expected), "straus w={w}");
      checks += 1;
    }
    for w in [2, 3, 4, 5, 8, 9, 11, 13] {
      assert!(eq(&pippenger(&s, &p, w, a).unwrap(), expected), "pippenger w={w}");
      checks += 1;
    }
    assert!(eq(&variable_msm(&s, &p, a).unwrap(), expected));

    // As fixed bases (which exclude the identity)
    let (s, bases): (Vec<_>, Vec<_>) =
      scalars.iter().zip(points).filter(|(_, p)| !bool::from(p.is_identity())).unzip();
    if bases.is_empty() {
      return checks + 1;
    }
    let expected =
      multiexp_vartime(&s.iter().copied().zip(bases.iter().copied()).collect::<Vec<_>>());
    let terms: Vec<_> = s.into_iter().enumerate().collect();
    for w in [2, 3, 5, 8, 10, 11] {
      let tables = Tables::new::<G>(&bases, w, 0, 0).unwrap();
      assert!(eq(&tables.msm(&terms, a).unwrap(), expected), "fixed w={w}");
      checks += 1;
    }
    checks + 1
  }

  fn adversarial<G: DivisorCurve>() -> usize
  where
    G::Scalar: PrimeFieldBits,
  {
    assert!(little_endian::<G::Scalar>());
    let mut checks = 0;
    let p = G::random(&mut OsRng);
    let q = G::random(&mut OsRng);
    let s = G::Scalar::random(&mut OsRng);

    // Every digit of every copy in the same bucket
    for k in [2, 3, 4, 5, 7, 8, 16, 33] {
      checks += check(&vec![s; k], &vec![p; k]);
    }
    // P, -P pairs with the same scalar, with and without a leftover
    for k in [1, 2, 3, 8] {
      let mut points = vec![];
      for _ in 0 .. k {
        points.extend([p, -p]);
      }
      checks += check(&vec![s; 2 * k], &points);
      points.push(p);
      checks += check(&vec![s; (2 * k) + 1], &points);
    }
    // Sums which coincide or cancel in later rounds
    for points in [
      vec![p, q, q, p],
      vec![p, q, -q, -p],
      vec![p, p, -p.double()],
      vec![p, p, p.double()],
      vec![p, q, p + q, -(p + q).double()],
      vec![p, -p, p, -p, p],
      vec![G::identity(), p, G::identity(), -p],
      vec![p.double(), p, p, -p.double().double()],
    ] {
      checks += check(&vec![s; points.len()], &points);
      let alternating: Vec<_> =
        (0 .. points.len()).map(|k| if k % 2 == 0 { s } else { -s }).collect();
      checks += check(&alternating, &points);
    }
    // Odd multiples, colliding with the Straus tables
    let mut odd = vec![p];
    for _ in 0 .. 16 {
      odd.push(*odd.last().unwrap() + p.double());
    }
    checks += check(&vec![s; odd.len()], &odd);
    // 2^(w j) P, colliding with the fixed-base table entries
    for w in [2, 3, 5, 8, 10, 11] {
      let mut points = vec![p];
      let mut x = p;
      for _ in 0 .. 4 {
        for _ in 0 .. w {
          x = x.double();
        }
        points.extend([x, -x]);
      }
      checks += check(&vec![s; points.len()], &points);
      let random: Vec<_> = (0 .. points.len()).map(|_| G::Scalar::random(&mut OsRng)).collect();
      checks += check(&random, &points);
    }
    // Edge scalars, on distinct points and on one point
    let edge = edge_scalars::<G::Scalar>();
    for chunk in edge.chunks(40) {
      let points: Vec<_> = (0 .. chunk.len()).map(|_| G::random(&mut OsRng)).collect();
      checks += check(chunk, &points);
      checks += check(chunk, &vec![p; chunk.len()]);
    }
    // Random mixes with heavy duplication
    for trial in 0 .. 40 {
      let base: Vec<G> = (0 ..= (trial % 5)).map(|_| G::random(&mut OsRng)).collect();
      let n = 2 + ((trial * 13) % 150);
      let mut scalars = vec![];
      let mut points = vec![];
      for _ in 0 .. n {
        let b = base[usize::try_from(OsRng.next_u64()).unwrap() % base.len()];
        points.push(match OsRng.next_u64() % 4 {
          0 => b,
          1 => -b,
          2 => b.double(),
          _ => G::identity(),
        });
        scalars.push(match OsRng.next_u64() % 4 {
          0 => s,
          1 => -s,
          2 => G::Scalar::ZERO,
          _ => G::Scalar::random(&mut OsRng),
        });
      }
      checks += check(&scalars, &points);
    }
    checks
  }

  #[test]
  fn selene() {
    let checks = adversarial::<helioselene::SelenePoint>();
    println!("{checks} comparisons against multiexp_vartime");
    assert!(checks > 1000);
  }

  #[test]
  fn helios() {
    let checks = adversarial::<helioselene::HeliosPoint>();
    println!("{checks} comparisons against multiexp_vartime");
    assert!(checks > 1000);
  }

  #[test]
  fn ed25519() {
    let checks = adversarial::<dalek_ff_group::EdwardsPoint>();
    println!("{checks} comparisons against multiexp_vartime");
    assert!(checks > 1000);
  }

  /// `LazyTables::verify` against `Generators::verify` without tables, for tables covering every
  /// prefix of the generators and verifiers whose lengths are around each boundary.
  fn boundaries<C: Ciphersuite>()
  where
    C::G: DivisorCurve,
  {
    type Fe<C> = <<C as Ciphersuite>::G as DivisorCurve>::FieldElement;
    const GENERATORS: usize = 16;

    let generators = insecure_test_generators::<_, C>(&mut OsRng, GENERATORS).unwrap();
    let n_h_sum = generators.h_sum.len();
    let per_base = windows::<C::F>(W) * size_of::<Aff<Fe<C>>>();
    let scalar = || match OsRng.next_u32() % 8 {
      0 => C::F::ZERO,
      1 => C::F::ONE,
      2 => -C::F::ONE,
      _ => C::F::random(&mut OsRng),
    };
    let point = || {
      if (OsRng.next_u32() % 8) == 0 {
        C::G::identity()
      } else {
        C::G::random(&mut OsRng)
      }
    };

    // Not even the generators outside of the prefix
    assert!(LazyTables::<Fe<C>>::with_cap(&generators, (1 + n_h_sum) * per_base).is_none());

    for cap in [7, 9, 11, 14, 15, 22, 23, 39] {
      let lazy = LazyTables::<Fe<C>>::with_cap(&generators, cap * per_base);
      let Some(lazy) = lazy else {
        assert!(cap < (2 + n_h_sum));
        continue;
      };
      let n = lazy.0.as_ref().unwrap().n;
      // The largest power of two prefix which fits
      let expected = [16, 8, 4, 2, 1].into_iter().find(|n| (2 + (2 * n) + n_h_sum) <= cap);
      assert_eq!(n, expected.unwrap_or(0), "cap of {cap} bases");

      let mut g_lens = vec![0, 1, n.saturating_sub(1), n, n + 1, 2 * n, GENERATORS, GENERATORS + 3];
      g_lens.sort_unstable();
      g_lens.dedup();
      let h_sum_lens = [0, n_h_sum - 1, n_h_sum, n_h_sum + 2];
      for g_len in &g_lens {
        for h_len in &g_lens {
          for h_sum_len in &h_sum_lens {
            let mut verifier = Generators::<C>::batch_verifier();
            verifier.g = scalar();
            verifier.h = scalar();
            verifier.g_bold = (0 .. *g_len).map(|_| scalar()).collect();
            verifier.h_bold = (0 .. *h_len).map(|_| scalar()).collect();
            verifier.h_sum = (0 .. *h_sum_len).map(|_| scalar()).collect();
            verifier.additional =
              (0 .. (OsRng.next_u32() % 4)).map(|_| (scalar(), point())).collect();
            // So the sum is not the identity
            verifier.additional.push((C::F::ONE, C::G::random(&mut OsRng)));

            // The sum is the identity once its negation is added
            let sum = multiexp_vartime(
              &[(verifier.g, generators.g), (verifier.h, generators.h)]
                .into_iter()
                .chain(verifier.g_bold.iter().copied().zip(generators.g_bold.iter().copied()))
                .chain(verifier.h_bold.iter().copied().zip(generators.h_bold.iter().copied()))
                .chain(verifier.h_sum.iter().copied().zip(generators.h_sum.iter().copied()))
                .chain(verifier.additional.iter().copied())
                .collect::<Vec<_>>(),
            );
            let mut identity = verifier.clone();
            identity.additional.push((C::F::ONE, -sum));
            for (verifier, expected) in [(identity, true), (verifier, false)] {
              let context = format!("cap {cap}, lengths {g_len}, {h_len}, {h_sum_len}");
              assert_eq!(generators.verify(verifier.clone()), expected, "{context}");
              assert_eq!(lazy.verify(&generators, &verifier), Some(expected), "{context}");
            }
          }
        }
      }
    }
  }

  #[test]
  fn verify_boundaries() {
    boundaries::<helioselene::Selene>();
    boundaries::<helioselene::Helios>();
  }

  /// The points are summed in chunks, which must not change the sum.
  #[test]
  fn variable_chunks() {
    type G = helioselene::HeliosPoint;
    let a = G::a();
    for n in [VARIABLE_CHUNK - 1, VARIABLE_CHUNK, VARIABLE_CHUNK + 1, (2 * VARIABLE_CHUNK) + 5] {
      let points = (0 .. n).map(|_| G::random(&mut OsRng)).collect::<Vec<_>>();
      let scalars = (0 .. n)
        .map(|_| <G as ciphersuite::group::Group>::Scalar::random(&mut OsRng))
        .collect::<Vec<_>>();
      let expected =
        multiexp_vartime(&scalars.iter().copied().zip(points.iter().copied()).collect::<Vec<_>>());
      let affine = to_affine(&points).unwrap().into_iter().collect::<Option<Vec<_>>>().unwrap();
      assert!(eq(&variable_msm(&scalars, &affine, a).unwrap(), expected), "{n} points");
    }
  }

  #[test]
  fn digits() {
    type S = <helioselene::Selene as Ciphersuite>::F;
    let mut values = edge_scalars::<S>();
    values.extend((0 .. 64).map(|_| S::random(&mut OsRng)));
    for s in values {
      for w in 2 .. 17 {
        let mut d = vec![0; windows::<S>(w)];
        recode(&s, w, &mut d).unwrap();
        let mut acc = S::ZERO;
        for d in d.iter().rev() {
          for _ in 0 .. w {
            acc = acc.double();
          }
          acc += from_i64::<S>((*d).into());
          assert!((-(1 << (w - 1)) < *d) && (*d <= (1 << (w - 1))));
        }
        assert_eq!(acc, s);
      }
      for w in 2 .. 9 {
        let mut d = vec![];
        wnaf(&s, w, &mut d).unwrap();
        let mut acc = S::ZERO;
        for d in d.iter().rev() {
          acc = acc.double();
          acc += from_i64::<S>((*d).into());
          assert!((*d == 0) || ((d % 2 != 0) && (d.unsigned_abs() < (1 << (w - 1)))));
        }
        assert_eq!(acc, s);
      }
    }
  }
}
