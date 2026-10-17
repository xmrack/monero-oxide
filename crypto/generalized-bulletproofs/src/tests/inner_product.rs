// The inner product relation is P = sum(g_bold * a, h_bold * b, g * (a * b))

use rand_core::OsRng;

use ciphersuite::{
  group::{ff::Field as _, Group as _},
  Ciphersuite, Ristretto,
};

use crate::{
  ScalarVector, PointVector, Generators,
  transcript::*,
  inner_product::{P, IpStatement, IpWitness, IpProveError, wnaf, mul_vartime},
  tests::insecure_test_generators,
};

#[test]
fn test_zero_inner_product() {
  let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, 1).unwrap();
  let reduced = generators.reduce(1).unwrap();
  let witness = IpWitness::<Ristretto>::new(
    ScalarVector::<<Ristretto as Ciphersuite>::F>::new(1),
    ScalarVector::<<Ristretto as Ciphersuite>::F>::new(1),
  )
  .unwrap();

  let proof = {
    let mut transcript = Transcript::new([0; 32]);
    IpStatement::<Ristretto>::new(
      reduced,
      ScalarVector(vec![<Ristretto as Ciphersuite>::F::ONE; 1]),
      <Ristretto as Ciphersuite>::F::ONE,
      P::Prover,
    )
    .unwrap()
    .clone()
    .prove(&mut transcript, witness)
    .unwrap();
    transcript.complete()
  };

  let mut verifier = Generators::batch_verifier();
  IpStatement::<Ristretto>::new(
    reduced,
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ONE; 1]),
    <Ristretto as Ciphersuite>::F::ONE,
    P::Verifier { verifier_weight: <Ristretto as Ciphersuite>::F::ONE },
  )
  .unwrap()
  .verify(&mut verifier, &mut VerifierTranscript::new([0; 32], &proof))
  .unwrap();
  assert!(generators.verify(verifier));
}

#[test]
fn test_inner_product() {
  // P = sum(g_bold * a, h_bold * b)
  let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, 32).unwrap();
  let mut verifier = Generators::batch_verifier();
  let y = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  for i in 1 ..= 32_usize {
    let weights = ScalarVector::powers(y, i.next_power_of_two());
    let generators = generators.reduce(i).unwrap();
    let g = generators.g();
    assert_eq!(generators.len(), i.next_power_of_two());
    let mut g_bold = vec![];
    let mut h_bold = vec![];
    for i in 0 .. i.next_power_of_two() {
      g_bold.push(generators.g_bold(i));
      h_bold.push(generators.h_bold(i));
    }
    let g_bold = PointVector::<Ristretto>(g_bold);
    let h_bold = PointVector::<Ristretto>(h_bold);

    let mut a = ScalarVector::<<Ristretto as Ciphersuite>::F>::new(i.next_power_of_two());
    let mut b = ScalarVector::<<Ristretto as Ciphersuite>::F>::new(i.next_power_of_two());

    for i in 0 .. i {
      a[i] = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
      b[i] = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
    }

    let P = g_bold.multiexp(&a) +
      h_bold.mul_vec(&weights).multiexp(&b) +
      (g * a.inner_product(b.0.iter()));

    let witness = IpWitness::<Ristretto>::new(a, b).unwrap();

    let proof = {
      let mut transcript = Transcript::new([0; 32]);
      IpStatement::<Ristretto>::new(
        generators,
        weights.clone(),
        <Ristretto as Ciphersuite>::F::ONE,
        P::Prover,
      )
      .unwrap()
      .prove(&mut transcript, witness)
      .unwrap();
      transcript.complete()
    };

    verifier.additional.push((<Ristretto as Ciphersuite>::F::ONE, P));
    IpStatement::<Ristretto>::new(
      generators,
      weights,
      <Ristretto as Ciphersuite>::F::ONE,
      P::Verifier { verifier_weight: <Ristretto as Ciphersuite>::F::ONE },
    )
    .unwrap()
    .verify(&mut verifier, &mut VerifierTranscript::new([0; 32], &proof))
    .unwrap();
  }
  assert!(generators.verify(verifier));
}

#[test]
fn test_inner_product_weights() {
  let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, 4).unwrap();
  let generators = generators.reduce(4).unwrap();
  let mut weights = ScalarVector::powers(<Ristretto as Ciphersuite>::F::random(&mut OsRng), 4);
  weights[3] += <Ristretto as Ciphersuite>::F::ONE;
  let witness = IpWitness::<Ristretto>::new(
    ScalarVector::<<Ristretto as Ciphersuite>::F>::new(4),
    ScalarVector::<<Ristretto as Ciphersuite>::F>::new(4),
  )
  .unwrap();
  assert_eq!(
    IpStatement::<Ristretto>::new(
      generators,
      weights,
      <Ristretto as Ciphersuite>::F::ONE,
      P::Prover
    )
    .unwrap()
    .prove(&mut Transcript::new([0; 32]), witness),
    Err(IpProveError::InconsistentWitness)
  );
}

#[test]
fn test_mul_vartime() {
  let point = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
  let mut scalars = vec![
    <Ristretto as Ciphersuite>::F::ZERO,
    <Ristretto as Ciphersuite>::F::ONE,
    -<Ristretto as Ciphersuite>::F::ONE,
    <Ristretto as Ciphersuite>::F::from(15u64),
    <Ristretto as Ciphersuite>::F::from(16u64),
    <Ristretto as Ciphersuite>::F::from(17u64),
    <Ristretto as Ciphersuite>::F::from(31u64),
    <Ristretto as Ciphersuite>::F::from(32u64),
    <Ristretto as Ciphersuite>::F::from(u64::MAX),
    <Ristretto as Ciphersuite>::F::from(2u64).pow_vartime([252]) -
      <Ristretto as Ciphersuite>::F::ONE,
    <Ristretto as Ciphersuite>::F::from(2u64).pow_vartime([252]),
  ];
  for _ in 0 .. 64 {
    scalars.push(<Ristretto as Ciphersuite>::F::random(&mut OsRng));
  }
  for scalar in scalars {
    assert_eq!(mul_vartime(point, &wnaf(&scalar)), point * scalar);
  }
}
