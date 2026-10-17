//! `ConstraintBlock`s which use an index past the statement are rejected.

extern crate alloc;
use alloc::sync::Arc;

use rand_core::OsRng;

use ciphersuite::{group::Group as _, Ciphersuite, Ristretto};

use generalized_bulletproofs::{
  transcript::*,
  arithmetic_circuit_proof::{
    AcStatementError, ArithmeticCircuitStatement, BlockBounds, ConstraintBlock, LinComb, WeightAcc,
  },
  tests::insecure_test_generators,
};

type F = <Ristretto as Ciphersuite>::F;

struct Block(BlockBounds);
impl ConstraintBlock<F> for Block {
  fn accumulate(&self, _: &[F], _: &mut WeightAcc<'_, F>) {}
  fn bounds(&self) -> BlockBounds {
    self.0
  }
}

const TERMS: usize = 4;
const CONSTRAINTS: usize = 3;
const VECTOR_COMMITMENTS: usize = 2;

fn with_bounds(bounds: BlockBounds) -> Result<(), AcStatementError> {
  let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, TERMS).unwrap();
  let mut transcript = Transcript::new([0; 32]);
  let commitments = transcript.write_commitments(
    (0 .. VECTOR_COMMITMENTS).map(|_| <Ristretto as Ciphersuite>::G::random(&mut OsRng)).collect(),
    vec![],
  );
  ArithmeticCircuitStatement::<Ristretto>::new_with_blocks(
    generators.reduce(TERMS).unwrap(),
    (0 .. CONSTRAINTS).map(|_| LinComb::empty()).collect(),
    vec![Arc::new(Block(bounds))],
    commitments,
  )
  .map(|_| ())
}

#[test]
fn test_block_bounds() {
  let within = BlockBounds {
    a: Some(TERMS - 1),
    c: Some(VECTOR_COMMITMENTS - 1),
    constraint: Some(CONSTRAINTS - 1),
  };
  with_bounds(within).unwrap();
  with_bounds(BlockBounds::default()).unwrap();

  assert!(matches!(
    with_bounds(BlockBounds { a: Some(TERMS), ..within }),
    Err(AcStatementError::ConstrainedNonExistentTerm)
  ));
  assert!(matches!(
    with_bounds(BlockBounds { constraint: Some(CONSTRAINTS), ..within }),
    Err(AcStatementError::ConstrainedNonExistentTerm)
  ));
  assert!(matches!(
    with_bounds(BlockBounds { c: Some(VECTOR_COMMITMENTS), ..within }),
    Err(AcStatementError::ConstrainedNonExistentVectorCommitment)
  ));
  for bounds in [
    BlockBounds { a: Some(usize::MAX), ..within },
    BlockBounds { constraint: Some(usize::MAX), ..within },
    BlockBounds { c: Some(usize::MAX), ..within },
  ] {
    assert!(with_bounds(bounds).is_err());
  }
}
