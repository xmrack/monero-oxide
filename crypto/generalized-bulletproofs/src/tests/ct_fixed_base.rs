use rand_core::{RngCore as _, OsRng};

use ciphersuite::{
  group::{
    ff::{Field as _, PrimeField as _},
    Group as _,
  },
  Ciphersuite, Ristretto,
};
use multiexp::multiexp_vartime;

use crate::{
  PedersenVectorCommitment,
  ct_fixed_base::{self, Bold},
  tests::insecure_test_generators,
};

type F = <Ristretto as Ciphersuite>::F;
type G = <Ristretto as Ciphersuite>::G;

fn edge_scalars() -> Vec<F> {
  let mut res = vec![F::ZERO, F::ONE, -F::ONE, F::from(15u64), F::from(16u64), F::from(17u64)];
  let mut pow = F::ONE;
  for _ in 0 .. 256 {
    res.push(pow);
    res.push(-pow);
    res.push(pow - F::ONE);
    pow = pow.double();
  }
  // Every window `0b11111` or `0b10000`, maximising carries
  for k in [31u64, 16, 17] {
    let mut s = F::ZERO;
    for _ in 0 .. 51 {
      s = (s * F::from(32u64)) + F::from(k);
    }
    res.push(s);
    res.push(-s);
  }
  for _ in 0 .. 64 {
    res.push(F::random(&mut OsRng));
  }
  res
}

#[test]
fn test_fixed_base_multiexp() {
  let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, 64).unwrap();
  let tables = generators.tables.bold(Bold::G, generators.g_bold_slice(), 64);
  let g_h = generators.tables.g_h(generators.g(), generators.h());

  assert_eq!(ct_fixed_base::multiexp::<G>([], []), G::identity());

  let scalars = edge_scalars();
  for (i, scalar) in scalars.iter().enumerate() {
    let point = generators.g_bold_slice()[i % 64];
    let table = tables.get(i % 64);
    assert_eq!(ct_fixed_base::multiexp([(scalar, table)], []), point * scalar);
    assert_eq!(ct_fixed_base::multiexp([(scalar, g_h.get(1))], []), generators.h() * scalar);
  }

  for chunk in scalars.chunks(64) {
    let pairs =
      chunk.iter().zip(generators.g_bold_slice()).map(|(s, g)| (*s, *g)).collect::<Vec<_>>();
    assert_eq!(
      ct_fixed_base::multiexp(chunk.iter().enumerate().map(|(i, s)| (s, tables.get(i))), []),
      multiexp_vartime(&pairs)
    );
  }

  // Small scalars alone, and mixed with full scalars
  let small = (0 .. 512u64).map(F::from).collect::<Vec<_>>();
  for chunk in small.chunks(64) {
    let pairs =
      chunk.iter().zip(generators.g_bold_slice()).map(|(s, g)| (*s, *g)).collect::<Vec<_>>();
    let expected = multiexp_vartime(&pairs);
    assert_eq!(
      ct_fixed_base::multiexp([], chunk.iter().enumerate().map(|(i, s)| (s, tables.get(i)))),
      expected
    );
    let full = F::random(&mut OsRng);
    assert_eq!(
      ct_fixed_base::multiexp(
        [(&full, g_h.get(0))],
        chunk.iter().enumerate().map(|(i, s)| (s, tables.get(i)))
      ),
      expected + (generators.g() * full)
    );
  }
}

#[test]
fn test_vector_commitment() {
  for n in [1, 2, 3, 64, 100, 128] {
    let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, 128).unwrap();
    let mut values = vec![];
    let mut small = vec![];
    for _ in 0 .. n {
      if (OsRng.next_u64() % 2) == 1 {
        values.push(F::from(OsRng.next_u64() % 256));
        small.push(true);
      } else {
        values.push(F::random(&mut OsRng));
        small.push(false);
      }
    }
    let mask = F::random(&mut OsRng);
    let expected = PedersenVectorCommitment::<Ristretto> { g_values: values.clone(), mask }
      .commit(generators.g_bold_slice(), generators.h())
      .unwrap();
    assert_eq!(generators.vector_commitment(&values, &small, &mask), Some(expected));
    assert_eq!(generators.vector_commitment(&values, &vec![false; n], &mask), Some(expected));
    assert_eq!(generators.vector_commitment(&values, &small[1 ..], &mask), None);
  }
  let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, 2).unwrap();
  assert_eq!(generators.vector_commitment(&[F::ONE; 3], &[false; 3], &F::ONE), None);

  // A value declared small must be less than `2**9`
  let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, 4).unwrap();
  let mask = F::random(&mut OsRng);
  for (value, valid) in [
    (F::ZERO, true),
    (F::from(255u64), true),
    (F::from(511u64), true),
    (F::from(512u64), false),
    (F::from(1u64 << 40), false),
    (-F::ONE, false),
    (F::random(&mut OsRng), false),
  ] {
    let values = [F::random(&mut OsRng), value, F::ONE, F::random(&mut OsRng)];
    let expected = PedersenVectorCommitment::<Ristretto> { g_values: values.to_vec(), mask }
      .commit(generators.g_bold_slice(), generators.h())
      .unwrap();
    let small = [false, true, true, false];
    assert_eq!(generators.vector_commitment(&values, &small, &mask), valid.then_some(expected));
    assert_eq!(generators.vector_commitment(&values, &[false; 4], &mask), Some(expected));
    // Any value declared small is checked, and a random value is too large
    let small = [true, false, true, false];
    assert_eq!(generators.vector_commitment(&values, &small, &mask), None);
    let small = [false, false, true, true];
    assert_eq!(generators.vector_commitment(&values, &small, &mask), None);
  }
}

// The curves the prover uses, with scalars which stress the carries of the signed digits
fn vector_commitments_on<C: Ciphersuite>()
where
  C::G: subtle::ConditionallySelectable,
{
  const N: usize = 64;
  let generators = insecure_test_generators::<_, C>(&mut OsRng, N).unwrap();

  let mut scalars = vec![C::F::ZERO, C::F::ONE, -C::F::ONE];
  let mut pow = C::F::ONE;
  for _ in 0 .. C::F::NUM_BITS {
    scalars.extend([pow, -pow, pow - C::F::ONE, pow + C::F::ONE]);
    pow = pow.double();
  }
  for digit in [31u64, 16, 17, 15] {
    let mut s = C::F::ZERO;
    for _ in 0 .. 51 {
      s = (s * C::F::from(32u64)) + C::F::from(digit);
    }
    scalars.extend([s, -s]);
  }
  scalars.extend((0 .. 64).map(|_| C::F::random(&mut OsRng)));
  // The largest scalars
  scalars.extend([C::F::ZERO - C::F::ONE, C::F::TWO_INV, -C::F::TWO_INV]);

  let expected = |values: &[C::F], mask: C::F| {
    let terms = values.iter().copied().zip(generators.g_bold_slice().iter().copied());
    multiexp_vartime(&terms.chain([(mask, generators.h())]).collect::<Vec<_>>())
  };

  for chunk in scalars.chunks(N) {
    let mask = C::F::random(&mut OsRng);
    let commitment = generators.vector_commitment(chunk, &vec![false; chunk.len()], &mask);
    assert_eq!(commitment, Some(expected(chunk, mask)));
  }
  for mask in [C::F::ZERO, C::F::ONE, -C::F::ONE] {
    let values = vec![C::F::ZERO; N];
    assert_eq!(
      generators.vector_commitment(&values, &[false; N], &mask),
      Some(expected(&values, mask))
    );
  }

  // Every value which may be declared small
  let small = (0 .. 512u64).map(C::F::from).collect::<Vec<_>>();
  for chunk in small.chunks(N) {
    let mask = C::F::random(&mut OsRng);
    let commitment = generators.vector_commitment(chunk, &vec![true; chunk.len()], &mask);
    assert_eq!(commitment, Some(expected(chunk, mask)));
  }
}

#[test]
fn test_vector_commitments_on_prover_curves() {
  vector_commitments_on::<helioselene::Selene>();
  vector_commitments_on::<helioselene::Helios>();
}

// Tables are owned by the generators, so distinct generators at a reused address never share them
#[test]
fn test_tables_follow_generators() {
  let mut prior = None;
  let mut reused = 0;
  for _ in 0 .. 16 {
    let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, 64).unwrap();
    let address = generators.g_bold_slice().as_ptr();
    if prior == Some(address) {
      reused += 1;
    }
    prior = Some(address);
    let values = (0 .. 64).map(|_| F::random(&mut OsRng)).collect::<Vec<_>>();
    let mask = F::random(&mut OsRng);
    let expected = PedersenVectorCommitment::<Ristretto> { g_values: values.clone(), mask }
      .commit(generators.g_bold_slice(), generators.h())
      .unwrap();
    assert_eq!(generators.vector_commitment(&values, &[false; 64], &mask), Some(expected));
  }
  let _ = reused;
}
