#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(missing_docs)]
#![allow(non_snake_case)]

use core::fmt;
use std_shims::{vec, vec::Vec, sync::Arc};

use zeroize::{Zeroize, ZeroizeOnDrop};

use ciphersuite::{
  group::ff::{Field as _, FromUniformBytes},
  Ciphersuite,
};

use generalized_bulletproofs::{
  PedersenCommitment, PedersenVectorCommitment, ProofGenerators,
  transcript::{Transcript as ProverTranscript, VerifierTranscript, Commitments},
  arithmetic_circuit_proof::{
    AcStatementError, ArithmeticCircuitStatement, ArithmeticCircuitWitness,
  },
};
pub use generalized_bulletproofs::arithmetic_circuit_proof::{
  Variable, LinComb, ConstraintBlock, BlockBounds, WeightAcc,
};

mod gadgets;

/// A trait for the transcript, whether proving for verifying, as necessary for sampling
/// challenges.
pub trait Transcript {
  /// Sample a challenge from the transacript.
  ///
  /// It is the caller's responsibility to have properly transcripted all variables prior to
  /// sampling this challenge.
  fn challenge<C: Ciphersuite>(&mut self) -> C::F
  where
    C::F: FromUniformBytes<64>;

  /// Sample a challenge as a byte array.
  ///
  /// It is the caller's responsibility to have properly transcripted all variables prior to
  /// sampling this challenge.
  fn challenge_bytes(&mut self) -> [u8; 64];
}
impl Transcript for ProverTranscript {
  fn challenge<C: Ciphersuite>(&mut self) -> C::F
  where
    C::F: FromUniformBytes<64>,
  {
    self.challenge::<C>()
  }
  fn challenge_bytes(&mut self) -> [u8; 64] {
    self.challenge_bytes()
  }
}
impl Transcript for VerifierTranscript<'_> {
  fn challenge<C: Ciphersuite>(&mut self) -> C::F
  where
    C::F: FromUniformBytes<64>,
  {
    self.challenge::<C>()
  }
  fn challenge_bytes(&mut self) -> [u8; 64] {
    self.challenge_bytes()
  }
}

/// The witness for the satisfaction of this circuit.
#[derive(Clone, PartialEq, Eq, Debug, Zeroize, ZeroizeOnDrop)]
struct ProverData<C: Ciphersuite> {
  aL: Vec<C::F>,
  aR: Vec<C::F>,
  C: Vec<PedersenVectorCommitment<C>>,
  V: Vec<PedersenCommitment<C>>,
}

/// A struct representing a circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Circuit<C: Ciphersuite> {
  muls: usize,
  // A series of linear combinations which must evaluate to 0.
  constraints: Vec<LinComb<C::F>>,
  prover: Option<ProverData<C>>,
  blocks: BlockList<C>,
}

#[derive(Clone)]
struct BlockList<C: Ciphersuite>(Option<Vec<Arc<dyn ConstraintBlock<C::F>>>>);
impl<C: Ciphersuite> PartialEq for BlockList<C> {
  fn eq(&self, other: &Self) -> bool {
    match (&self.0, &other.0) {
      (Some(a), Some(b)) => (a.len() == b.len()) && a.iter().zip(b).all(|(a, b)| Arc::ptr_eq(a, b)),
      (None, None) => true,
      (Some(_), None) | (None, Some(_)) => false,
    }
  }
}
impl<C: Ciphersuite> Eq for BlockList<C> {}
impl<C: Ciphersuite> fmt::Debug for BlockList<C> {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt.debug_struct("BlockList").field("len", &self.0.as_ref().map(Vec::len)).finish()
  }
}

impl<C: Ciphersuite> Circuit<C> {
  /// Returns the amount of multiplications used by this circuit.
  pub fn muls(&self) -> usize {
    self.muls
  }

  /// Create an instance to prove satisfaction of a circuit with.
  #[allow(clippy::type_complexity)]
  pub fn prove(
    vector_commitments: Vec<PedersenVectorCommitment<C>>,
    commitments: Vec<PedersenCommitment<C>>,
  ) -> Self {
    Self {
      muls: 0,
      constraints: vec![],
      prover: Some(ProverData { aL: vec![], aR: vec![], C: vector_commitments, V: commitments }),
      blocks: BlockList(None),
    }
  }

  /// Create an instance to verify a proof with.
  pub fn verify() -> Self {
    Self { muls: 0, constraints: vec![], prover: None, blocks: BlockList(Some(vec![])) }
  }

  /// Create an instance to verify a proof with which builds every constraint as a `LinComb`.
  ///
  /// This is the reference the structured verifier is checked against.
  #[doc(hidden)]
  pub fn verify_unstructured() -> Self {
    Self { muls: 0, constraints: vec![], prover: None, blocks: BlockList(None) }
  }

  /// The constraints which were built as `LinComb`s.
  #[doc(hidden)]
  pub fn constraints(&self) -> &[LinComb<C::F>] {
    &self.constraints
  }

  /// The `ConstraintBlock`s which were added.
  #[doc(hidden)]
  pub fn blocks(&self) -> &[Arc<dyn ConstraintBlock<C::F>>] {
    self.blocks.0.as_deref().unwrap_or(&[])
  }

  /// Whether this circuit accepts `ConstraintBlock`s.
  pub fn structured(&self) -> bool {
    self.blocks.0.is_some()
  }

  /// Add a `ConstraintBlock` over `muls` new multiplications and `constraints` new constraints.
  ///
  /// `block` is called with the index of the first multiplication and of the first constraint.
  /// Returns false, without changing the circuit, if this circuit doesn't accept blocks.
  pub fn constraint_block(
    &mut self,
    muls: usize,
    constraints: usize,
    block: impl FnOnce(usize, usize) -> Arc<dyn ConstraintBlock<C::F>>,
  ) -> bool {
    let Some(blocks) = self.blocks.0.as_mut() else { return false };
    let block = block(self.muls, self.constraints.len());
    blocks.push(block);
    self.muls += muls;
    self.constraints.resize(self.constraints.len() + constraints, LinComb::empty());
    true
  }

  /// Evaluate a linear combination.
  ///
  /// Yields WL aL + WR aR + WO aO + WCG CG + WV V + c.
  ///
  /// May panic if the linear combination references non-existent terms.
  ///
  /// Returns None if not a prover.
  pub fn eval(&self, lincomb: &LinComb<C::F>) -> Option<C::F> {
    self.prover.as_ref().map(|prover| {
      let mut res = lincomb.c();
      for (index, weight) in lincomb.WL() {
        res += prover.aL[*index] * weight;
      }
      for (index, weight) in lincomb.WR() {
        res += prover.aR[*index] * weight;
      }
      for (index, weight) in lincomb.WO() {
        res += prover.aL[*index] * prover.aR[*index] * weight;
      }
      for (i, C) in prover.C.iter().enumerate() {
        for (j, weight) in lincomb.WCG().get(&i).into_iter().flat_map(|values| values.iter()) {
          res += C.g_values[*j] * weight;
        }
      }
      for (index, weight) in lincomb.WV() {
        res += prover.V[*index].value * weight;
      }
      res
    })
  }

  /// Multiply two values, optionally constrained, returning the constrainable left/right/out
  /// terms.
  ///
  /// May panic if any linear combinations reference non-existent terms or if the witness isn't
  /// provided when proving/is provided when verifying.
  #[allow(clippy::many_single_char_names)]
  pub fn mul(
    &mut self,
    a: Option<LinComb<C::F>>,
    b: Option<LinComb<C::F>>,
    witness: Option<(C::F, C::F)>,
  ) -> (Variable, Variable, Variable) {
    let l = Variable::aL(self.muls);
    let r = Variable::aR(self.muls);
    let o = Variable::aO(self.muls);
    self.muls += 1;

    debug_assert_eq!(self.prover.is_some(), witness.is_some());
    if let Some(witness) = witness {
      let prover = self.prover.as_mut().unwrap();
      prover.aL.push(witness.0);
      prover.aR.push(witness.1);
    }

    if let Some(a) = a {
      self.constrain_equal_to_zero(a.term(-C::F::ONE, l));
    }
    if let Some(b) = b {
      self.constrain_equal_to_zero(b.term(-C::F::ONE, r));
    }

    (l, r, o)
  }

  /// Constrain a linear combination to be equal to 0.
  ///
  /// May panic if the linear combination references non-existent terms.
  pub fn constrain_equal_to_zero(&mut self, lincomb: LinComb<C::F>) {
    self.constraints.push(lincomb);
  }
}

impl<C: Ciphersuite> Circuit<C>
where
  C::F: FromUniformBytes<64>,
{
  /// Obtain the statement for this circuit.
  ///
  /// If configured as the prover, the witness to use is also returned if one was successfully
  /// constructed.
  #[allow(clippy::type_complexity)]
  pub fn statement(
    self,
    generators: ProofGenerators<'_, C>,
    commitments: Commitments<C>,
  ) -> Result<
    (ArithmeticCircuitStatement<'_, C>, Option<ArithmeticCircuitWitness<C>>),
    AcStatementError,
  > {
    let statement = match self.blocks.0 {
      Some(blocks) => ArithmeticCircuitStatement::new_with_blocks(
        generators,
        self.constraints,
        blocks,
        commitments,
      )?,
      None => ArithmeticCircuitStatement::new(generators, self.constraints, commitments)?,
    };

    let witness = self.prover.and_then(|mut prover| {
      // We can't deconstruct the witness as it implements Drop (per ZeroizeOnDrop)
      // Accordingly, we take the values within it and move forward with those
      let mut aL = vec![];
      core::mem::swap(&mut prover.aL, &mut aL);
      let mut aR = vec![];
      core::mem::swap(&mut prover.aR, &mut aR);
      let mut C = vec![];
      core::mem::swap(&mut prover.C, &mut C);
      let mut V = vec![];
      core::mem::swap(&mut prover.V, &mut V);
      ArithmeticCircuitWitness::new(aL, aR, C, V)
    });

    Ok((statement, witness))
  }
}
