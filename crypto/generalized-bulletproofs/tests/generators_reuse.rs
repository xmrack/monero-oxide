//! Proving with a fresh `Generators` placed where a dropped one was must use its own tables.

#![allow(non_snake_case)]

use rand_core::OsRng;

use ciphersuite::{group::ff::Field as _, Ciphersuite, Ristretto};

use generalized_bulletproofs::{
  Generators,
  transcript::*,
  arithmetic_circuit_proof::{ArithmeticCircuitStatement, ArithmeticCircuitWitness},
  tests::insecure_test_generators,
};

fn prove_and_verify(generators: &Generators<Ristretto>) -> bool {
  let aL = vec![<Ristretto as Ciphersuite>::F::random(&mut OsRng); 4];
  let aR = vec![<Ristretto as Ciphersuite>::F::random(&mut OsRng); 4];
  let mut transcript = Transcript::new([0; 32]);
  let commitments = transcript.write_commitments(vec![], vec![]);
  let statement = ArithmeticCircuitStatement::<Ristretto>::new(
    generators.reduce(4).unwrap(),
    vec![],
    commitments,
  )
  .unwrap();
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(aL, aR, vec![], vec![]).unwrap();
  statement.clone().prove(&mut OsRng, &mut transcript, witness).unwrap();
  let proof = transcript.complete();

  let mut verifier = Generators::batch_verifier();
  let mut transcript = VerifierTranscript::new([0; 32], &proof);
  transcript.read_commitments::<Ristretto>(0, 0).unwrap();
  statement.verify(&mut OsRng, &mut verifier, &mut transcript).is_ok() &&
    generators.verify(verifier)
}

#[test]
fn test_generators_at_reused_address() {
  let mut slot = insecure_test_generators::<_, Ristretto>(&mut OsRng, 4).unwrap();
  let mut same_address = 0;
  for _ in 0 .. 16 {
    assert!(prove_and_verify(&slot));
    let struct_address = core::ptr::from_ref(&slot);
    let bold_address = slot.g_bold_slice().as_ptr();
    // Replace in place, after the old generators (and their tables) are dropped
    drop(core::mem::replace(&mut slot, insecure_test_generators(&mut OsRng, 1).unwrap()));
    slot = insecure_test_generators::<_, Ristretto>(&mut OsRng, 4).unwrap();
    assert_eq!(core::ptr::from_ref(&slot), struct_address);
    same_address += usize::from(slot.g_bold_slice().as_ptr() == bold_address);
  }
  assert!(prove_and_verify(&slot));
  // The allocator usually hands the freed buffer back, which is the case this test exists for
  println!("g_bold buffer reused in {same_address}/16 replacements");
}
