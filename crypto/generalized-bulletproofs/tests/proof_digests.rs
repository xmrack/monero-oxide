//! Proofs from fixed inputs must stay byte-identical to those produced by `31c26d9`.
//!
//! Everything is derived from a deterministic RNG, so the digest changes if the prover draws from
//! its RNG in a different order or computes any element differently, even if the proof verifies.

#![allow(non_snake_case)]

use core::fmt::Write as _;

use blake2::{Blake2b512, Digest as _};

use ciphersuite::{group::ff::Field as _, Ciphersuite, Ristretto};

use generalized_bulletproofs::{
  PedersenCommitment, PedersenVectorCommitment, Generators,
  transcript::*,
  arithmetic_circuit_proof::{
    Variable, LinComb, ArithmeticCircuitStatement, ArithmeticCircuitWitness,
  },
  tests::insecure_test_generators,
};

type F = <Ristretto as Ciphersuite>::F;

struct TestRng(u64);
impl rand_core::RngCore for TestRng {
  fn next_u32(&mut self) -> u32 {
    u32::try_from(self.next_u64() >> 32).unwrap()
  }
  fn next_u64(&mut self) -> u64 {
    self.0 ^= self.0 << 13;
    self.0 ^= self.0 >> 7;
    self.0 ^= self.0 << 17;
    self.0
  }
  fn fill_bytes(&mut self, dest: &mut [u8]) {
    rand_core::impls::fill_bytes_via_next(self, dest);
  }
  fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
    self.fill_bytes(dest);
    Ok(())
  }
}
impl rand_core::CryptoRng for TestRng {}

const DIGESTS: [&str; 3] = [
  "207c19154e531460cd3264bfbe18d824",
  "6870843252ee71b99e5c8b447e79b084",
  "3e5af05d2b184315d669efb6e384d132",
];

fn digest(n: usize, vector_commitments: usize, seed: u64) -> String {
  let mut rng = TestRng(seed);
  let generators = insecure_test_generators::<_, Ristretto>(&mut rng, n).unwrap();
  let reduced = generators.reduce(n).unwrap();

  let aL = (0 .. n).map(|_| F::random(&mut rng)).collect::<Vec<F>>();
  let aR = (0 .. n).map(|_| F::random(&mut rng)).collect::<Vec<F>>();
  let C = (0 .. vector_commitments)
    .map(|_| PedersenVectorCommitment::<Ristretto> {
      g_values: (0 .. n).map(|_| F::random(&mut rng)).collect(),
      mask: F::random(&mut rng),
    })
    .collect::<Vec<_>>();
  let V = (0 .. 2)
    .map(|_| PedersenCommitment::<Ristretto> {
      value: F::random(&mut rng),
      mask: F::random(&mut rng),
    })
    .collect::<Vec<_>>();

  let mut constraints = vec![];
  for (i, V) in V.iter().enumerate() {
    constraints.push(LinComb::empty().term(-F::ONE, Variable::V(i)).constant(V.value));
  }
  constraints.push(
    LinComb::empty()
      .term(F::ONE, Variable::aL(0))
      .term(F::ONE, Variable::aR(n - 1))
      .term(F::ONE, Variable::CG { commitment: vector_commitments - 1, index: n - 1 })
      .term(F::ONE, Variable::V(1))
      .constant(-(aL[0] + aR[n - 1] + C[vector_commitments - 1].g_values[n - 1] + V[1].value)),
  );

  let mut transcript = Transcript::new([0; 32]);
  let commitments = transcript.write_commitments(
    C.iter().map(|C| C.commit(generators.g_bold_slice(), generators.h()).unwrap()).collect(),
    V.iter().map(|V| V.commit(generators.g(), generators.h())).collect(),
  );
  let statement =
    ArithmeticCircuitStatement::<Ristretto>::new(reduced, constraints, commitments).unwrap();
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(aL, aR, C, V).unwrap();
  statement.clone().prove(&mut TestRng(seed + 1), &mut transcript, witness).unwrap();
  let proof = transcript.complete();

  let mut verifier = Generators::batch_verifier();
  let mut transcript = VerifierTranscript::new([0; 32], &proof);
  transcript.read_commitments::<Ristretto>(vector_commitments, 2).unwrap();
  statement.verify(&mut rng, &mut verifier, &mut transcript).unwrap();
  assert!(generators.verify(verifier));

  Blake2b512::digest(&proof).iter().take(16).fold(String::new(), |mut hex, byte| {
    write!(hex, "{byte:02x}").unwrap();
    hex
  })
}

#[test]
fn test_proof_digests() {
  let digests = [digest(8, 1, 1), digest(64, 3, 2), digest(512, 3, 3)];
  assert_eq!(digests, DIGESTS);
}
