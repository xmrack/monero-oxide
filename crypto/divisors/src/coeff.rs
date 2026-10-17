use std_shims::{vec, vec::Vec};

use subtle::{Choice, ConditionallySelectable, CtOption};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use ff::PrimeField;

use crate::divisor::SmallDivisor;

const KARATSUBA_THRESHOLD: usize = 16;

/// `out += a * b`, where `a.len() == b.len()` and `out.len() >= 2 * a.len()`.
fn mul_acc<F: PrimeField + Zeroize>(a: &[F], b: &[F], out: &mut [F]) {
  let n = a.len();
  debug_assert_eq!(n, b.len());
  debug_assert!(out.len() >= (2 * n));
  if n <= KARATSUBA_THRESHOLD {
    for (i, a) in a.iter().enumerate() {
      for (out, b) in out[i ..].iter_mut().zip(b) {
        *out += *a * b;
      }
    }
    return;
  }

  let lo = n / 2;
  let hi = n - lo;
  let (a0, a1) = a.split_at(lo);
  let (b0, b1) = b.split_at(lo);

  let mut z0 = Zeroizing::new(vec![F::ZERO; 2 * lo]);
  mul_acc(a0, b0, &mut z0);
  let mut z2 = Zeroizing::new(vec![F::ZERO; 2 * hi]);
  mul_acc(a1, b1, &mut z2);

  // (a0 + a1)(b0 + b1) - z0 - z2
  let mut sum_a = Zeroizing::new(a1.to_vec());
  let mut sum_b = Zeroizing::new(b1.to_vec());
  for ((sum_a, sum_b), (a0, b0)) in sum_a.iter_mut().zip(sum_b.iter_mut()).zip(a0.iter().zip(b0)) {
    *sum_a += a0;
    *sum_b += b0;
  }
  let mut z1 = Zeroizing::new(vec![F::ZERO; 2 * hi]);
  mul_acc(&sum_a, &sum_b, &mut z1);
  for (z1, z0) in z1.iter_mut().zip(z0.iter()) {
    *z1 -= z0;
  }
  for (z1, z2) in z1.iter_mut().zip(z2.iter()) {
    *z1 -= z2;
  }

  for (out, z0) in out.iter_mut().zip(z0.iter()) {
    *out += z0;
  }
  for (out, z1) in out[lo ..].iter_mut().zip(z1.iter()) {
    *out += z1;
  }
  for (out, z2) in out[(2 * lo) ..].iter_mut().zip(z2.iter()) {
    *out += z2;
  }
}

/// The product of two polynomials, as coefficients from the lowest degree.
fn mul<F: PrimeField + Zeroize>(a: &[F], b: &[F]) -> Zeroizing<Vec<F>> {
  let n = a.len().max(b.len());
  let pad = |v: &[F]| {
    // Allocated to size so the coefficients are never left behind by a reallocation
    let mut res = Zeroizing::new(Vec::with_capacity(n));
    res.extend_from_slice(v);
    res.resize(n, F::ZERO);
    res
  };
  let (a, b) = (pad(a), pad(b));
  let mut res = Zeroizing::new(vec![F::ZERO; 2 * n]);
  mul_acc(&a, &b, &mut res);
  res
}

/// Divide by `(x - c)` if `present`, where the division is exact, else leave as-is.
fn div_linear<F: PrimeField + ConditionallySelectable>(v: &mut [F], c: F, present: Choice) {
  // Synthetic division from the highest coefficient, where the quotient's coefficient for `x**i`
  // is the running value at `i + 1`
  let mut carry = F::ZERO;
  let mut quotient = F::ZERO;
  for coeff in v.iter_mut().rev() {
    let current = *coeff + carry;
    carry = current * c;
    let divided = quotient;
    quotient = current;
    coeff.conditional_assign(&divided, present);
  }
}

/// Truncate a polynomial to a length beyond which all coefficients are zero.
fn trim<F: PrimeField + Zeroize>(v: &mut Vec<F>, len: usize) {
  debug_assert!(v.iter().skip(len).all(|coeff| bool::from(coeff.is_zero())));
  for coeff in v.iter_mut().skip(len) {
    coeff.zeroize();
  }
  v.truncate(len);
}

/// A function `a(x) + y b(x)`, as coefficients from the lowest degree.
#[derive(Zeroize, ZeroizeOnDrop)]
pub(crate) struct CoeffDivisor<F: PrimeField + Zeroize> {
  pub(crate) a: Vec<F>,
  pub(crate) b: Vec<F>,
}

impl<F: PrimeField + Zeroize + ConditionallySelectable> CoeffDivisor<F> {
  pub(crate) fn from_small(small: &SmallDivisor<F>) -> Self {
    let (x_coefficient, zero_coefficient, y_coefficient) = small.coefficients();
    CoeffDivisor { a: vec![zero_coefficient, x_coefficient], b: vec![y_coefficient] }
  }

  /// Merge two divisors, multiplying by `small` and dividing by the vertical lines at `denom`.
  ///
  /// `len_a, len_b` are the lengths sufficient for the result. The sequence of operations is a
  /// function of the lengths alone.
  pub(crate) fn merge(
    divisors: [Self; 2],
    small: &SmallDivisor<F>,
    denom: (CtOption<F>, CtOption<F>),
    (curve_a, curve_b): (F, F),
    (len_a, len_b): (usize, usize),
  ) -> Self {
    let [d1, d2] = divisors;

    // (a1 + y b1)(a2 + y b2)
    //   = (a1 a2 + (x**3 + A x + B) b1 b2) + y((a1 + b1)(a2 + b2) - a1 a2 - b1 b2)
    let a1a2 = mul(&d1.a, &d2.a);
    let b1b2 = mul(&d1.b, &d2.b);
    let sum = |d: &Self| {
      let mut res = Zeroizing::new(vec![F::ZERO; d.a.len().max(d.b.len())]);
      for (res, a) in res.iter_mut().zip(&d.a) {
        *res += a;
      }
      for (res, b) in res.iter_mut().zip(&d.b) {
        *res += b;
      }
      res
    };
    let cross = mul(&sum(&d1), &sum(&d2));
    drop(d1);
    drop(d2);

    let len = a1a2.len().max(b1b2.len() + 3).max(cross.len());
    let mut a = Zeroizing::new(vec![F::ZERO; len]);
    let mut b = Zeroizing::new(vec![F::ZERO; len]);
    for (a, a1a2) in a.iter_mut().zip(a1a2.iter()) {
      *a += a1a2;
    }
    for (i, b1b2) in b1b2.iter().enumerate() {
      a[i + 3] += b1b2;
      a[i + 1] += *b1b2 * curve_a;
      a[i] += *b1b2 * curve_b;
    }
    for (b, cross) in b.iter_mut().zip(cross.iter()) {
      *b += cross;
    }
    for (b, a1a2) in b.iter_mut().zip(a1a2.iter()) {
      *b -= a1a2;
    }
    for (b, b1b2) in b.iter_mut().zip(b1b2.iter()) {
      *b -= b1b2;
    }

    // Multiply by the line `(x_coefficient x + zero_coefficient) + y y_coefficient`
    // a' = a (x_c x + z_c) + (x**3 + A x + B) b y_c, b' = a y_c + b (x_c x + z_c)
    let (x_c, z_c, y_c) = small.coefficients();
    let mut res = CoeffDivisor { a: vec![F::ZERO; len + 4], b: vec![F::ZERO; len + 4] };
    for (i, (a, b)) in a.iter().zip(b.iter()).enumerate() {
      res.a[i] += *a * z_c;
      res.a[i + 1] += *a * x_c;
      let b_y_c = *b * y_c;
      res.a[i + 3] += b_y_c;
      res.a[i + 1] += b_y_c * curve_a;
      res.a[i] += b_y_c * curve_b;

      res.b[i] += *a * y_c;
      res.b[i] += *b * z_c;
      res.b[i + 1] += *b * x_c;
    }

    // Divide by the vertical lines at the points summed by each divisor, if not the identity
    let (x1, x2) = denom;
    let (x1_present, x2_present) = (x1.is_some(), x2.is_some());
    let (x1, x2) = (x1.unwrap_or(F::ZERO), x2.unwrap_or(F::ZERO));
    div_linear(&mut res.a, x1, x1_present);
    div_linear(&mut res.b, x1, x1_present);
    div_linear(&mut res.a, x2, x2_present);
    div_linear(&mut res.b, x2, x2_present);

    trim(&mut res.a, len_a);
    trim(&mut res.b, len_b);
    res
  }
}
