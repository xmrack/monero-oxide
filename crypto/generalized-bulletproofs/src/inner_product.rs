use std_shims::{vec, vec::Vec};

use subtle::ConditionallySelectable;

use multiexp::multiexp_vartime;
use ciphersuite::{
  group::{
    ff::{Field as _, PrimeFieldBits, FromUniformBytes, BatchInvert as _},
    Group,
  },
  Ciphersuite,
};

use crate::{ScalarVector, ProofGenerators, BatchVerifier, transcript::*};

#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum P<C: Ciphersuite> {
  Verifier { verifier_weight: C::F },
  Prover,
}

/// The Bulletproofs Inner-Product statement.
///
/// This is for usage with Protocol 2 from the Bulletproofs paper.
#[derive(Clone, Debug)]
pub(crate) struct IpStatement<'a, C: Ciphersuite> {
  generators: ProofGenerators<'a, C>,
  // Weights for h_bold
  h_bold_weights: ScalarVector<C::F>,
  // u as the discrete logarithm of G
  u: C::F,
  // P
  P: P<C>,
}

/// The witness for the Bulletproofs Inner-Product statement.
#[derive(Clone, Debug)]
pub(crate) struct IpWitness<C: Ciphersuite> {
  // a
  a: ScalarVector<C::F>,
  // b
  b: ScalarVector<C::F>,
}

impl<C: Ciphersuite> IpWitness<C> {
  /// Construct a new witness for an Inner-Product statement.
  ///
  /// This functions return `None` if `a.len() != b.len()` or if the lengths are not a power of
  /// two.
  pub(crate) fn new(mut a: ScalarVector<C::F>, mut b: ScalarVector<C::F>) -> Option<Self> {
    if a.len() != b.len() {
      None?;
    }
    if !a.len().is_power_of_two() {
      None?;
    }

    // If no IPA rows were used, pad to have a length of one
    if a.is_empty() {
      a.0.push(C::F::ZERO);
      b.0.push(C::F::ZERO);
    }
    Some(Self { a, b })
  }
}

impl<'a, C: Ciphersuite> IpStatement<'a, C>
where
  C::F: FromUniformBytes<64>,
{
  /// Create a new Inner-Product statement.
  ///
  /// This does not perform any transcripting of any variables within this statement. They must be
  /// deterministic to the existing transcript.
  //
  /// Returns `None` if `generators.h_bold_slice().len() != h_bold_weights.len()` or if the lengths
  /// are not a power of two.
  pub(crate) fn new(
    generators: ProofGenerators<'a, C>,
    h_bold_weights: ScalarVector<C::F>,
    u: C::F,
    P: P<C>,
  ) -> Option<Self> {
    if generators.h_bold_slice().len() != h_bold_weights.len() {
      None?;
    }
    if !generators.h_bold_slice().len().is_power_of_two() {
      None?;
    }
    Some(Self { generators, h_bold_weights, u, P })
  }
}

/// An error from proving Inner-Product statements.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum IpProveError {
  /// An incorrect amount of generators was provided.
  IncorrectAmountOfGenerators,
  /// The witness was inconsistent to the statement.
  ///
  /// Sanity checks on the witness are always performed. This library may also check whether or not
  /// the witness actually opens the statement (such as if `debug_assertions = on`), and if so, may
  /// return this error if the witness is perceived as inconsistent with the statement.
  InconsistentWitness,
}

/// The non-adjacent form of a scalar, with digits odd and less than `2**(WINDOW - 1)` in magnitude.
pub(crate) fn wnaf<F: PrimeFieldBits>(scalar: &F) -> Vec<i8> {
  const WINDOW: usize = 5;
  let bits = scalar.to_le_bits();
  let bit = |i: usize| (i < bits.len()) && bits[i];
  let mut naf = vec![0; bits.len() + 1];
  let mut carry = 0;
  let mut i = 0;
  while i < naf.len() {
    if u8::from(bit(i)) == carry {
      i += 1;
      continue;
    }
    let mut window = carry;
    for b in 0 .. WINDOW {
      window += u8::from(bit(i + b)) << b;
    }
    let digit = i8::try_from(window).unwrap();
    if window < (1 << (WINDOW - 1)) {
      naf[i] = digit;
      carry = 0;
    } else {
      naf[i] = digit - (1 << WINDOW);
      carry = 1;
    }
    i += WINDOW;
  }
  naf
}

/// `point * scalar`, in variable time, where `naf` is the scalar's non-adjacent form.
pub(crate) fn mul_vartime<G: Group>(point: G, naf: &[i8]) -> G {
  let double = point.double();
  let mut odd = [point; 8];
  for i in 1 .. odd.len() {
    odd[i] = odd[i - 1] + double;
  }
  let mut res = G::identity();
  for digit in naf.iter().rev() {
    res = res.double();
    let i = usize::from(digit.unsigned_abs() / 2);
    if *digit > 0 {
      res += odd[i];
    } else if *digit < 0 {
      res -= odd[i];
    }
  }
  res
}

impl<C: Ciphersuite> IpStatement<'_, C>
where
  C::F: FromUniformBytes<64>,
  C::G: ConditionallySelectable,
{
  /// Prove for this Inner-Product statement.
  ///
  /// This function executes in constant-time to all secrets as the witness is not considered a
  /// secret (as a Bulletproof is not a zero-knowledge proof).
  ///
  /// The `h_bold` weights must be the powers of a scalar, starting with one.
  pub(crate) fn prove(
    self,
    transcript: &mut Transcript,
    witness: IpWitness<C>,
  ) -> Result<(), IpProveError> {
    let IpStatement { generators, h_bold_weights, u, P } = self;
    let u = generators.g() * u;

    // Ensure we have the necessary amount of generators
    if witness.a.len() > ((usize::MAX >> 1) + 1) {
      Err(IpProveError::IncorrectAmountOfGenerators)?;
    }
    if generators.g_bold_slice().len() < witness.a.len().next_power_of_two() {
      Err(IpProveError::IncorrectAmountOfGenerators)?;
    }
    assert!(
      matches!(P, P::Prover),
      "prove called with a P specification which was for the verifier"
    );
    {
      let ratio = h_bold_weights.0.get(1).copied().unwrap_or(C::F::ONE);
      let mut expected = C::F::ONE;
      for weight in &h_bold_weights.0 {
        if *weight != expected {
          Err(IpProveError::InconsistentWitness)?;
        }
        expected *= ratio;
      }
    }

    /*
      The generators are represented as `g_weight * g_bold[i]` and `h_weights[i] * h_bold[i]`.
      As the weights are geometric, folding the second half into the first is one multiplication
      by a public scalar per generator.
    */
    let mut g_bold = generators.g_bold_slice().to_vec();
    let mut h_bold = generators.h_bold_slice().to_vec();
    let mut g_weight = C::F::ONE;
    let mut h_weights = h_bold_weights.0.clone();

    let IpWitness { mut a, mut b } = witness;

    // `else: (n > 1)` case, lines 18-35 of the Bulletproofs paper
    // This interprets `g_bold.len()` as `n`
    while g_bold.len() > 1 {
      // Split a, b, g_bold, h_bold as needed for lines 20-24
      let split_at = a.len().next_power_of_two() / 2;
      let (a1, a2) = a.split(split_at);
      let (b1, b2) = b.split(split_at);

      let n_hat = g_bold.len() / 2;

      // Sanity
      debug_assert_eq!(a1.len(), n_hat);
      debug_assert!(a2.len() <= n_hat);
      debug_assert_eq!(b1.len(), n_hat);
      debug_assert!(b2.len() <= n_hat);

      // cl, cr, lines 21-22
      let cl = b2.inner_product_without_length_checks(a1.0.iter());
      let cr = a2.inner_product_without_length_checks(b1.0.iter());

      let L = {
        let mut L_terms = Vec::with_capacity(1 + (2 * n_hat));
        for (a, g) in a1.0.iter().zip(&g_bold[n_hat ..]) {
          L_terms.push((*a * g_weight, *g));
        }
        for ((b, h), weight) in b2.0.iter().zip(&h_bold[.. n_hat]).zip(&h_weights) {
          L_terms.push((*b * weight, *h));
        }
        L_terms.push((cl, u));
        // Uses vartime since this isn't a ZK proof
        multiexp_vartime(&L_terms)
      };

      let R = {
        let mut R_terms = Vec::with_capacity(1 + (2 * n_hat));
        for (a, g) in a2.0.iter().zip(&g_bold[.. n_hat]) {
          R_terms.push((*a * g_weight, *g));
        }
        for ((b, h), weight) in b1.0.iter().zip(&h_bold[n_hat ..]).zip(&h_weights[n_hat ..]) {
          R_terms.push((*b * weight, *h));
        }
        R_terms.push((cr, u));
        multiexp_vartime(&R_terms)
      };

      // Now that we've calculate L, R, transcript them to receive x (26-27)
      transcript.push_point(&L);
      transcript.push_point(&R);
      let x: C::F = transcript.challenge::<C>();
      let x_inv = x.invert().expect("transcript challenge was 0");

      // The prover and verifier now calculate the following (28-31)
      // `g_bold[i] x_inv + g_bold[n_hat + i] x`, `h_bold[i] x + h_bold[n_hat + i] x_inv`
      let g_naf = wnaf(&x.square());
      let h_naf = wnaf(&(x_inv.square() * h_bold_weights[n_hat]));
      let (g_bold1, g_bold2) = g_bold.split_at_mut(n_hat);
      for (g1, g2) in g_bold1.iter_mut().zip(g_bold2.iter()) {
        *g1 += mul_vartime(*g2, &g_naf);
      }
      let (h_bold1, h_bold2) = h_bold.split_at_mut(n_hat);
      for (h1, h2) in h_bold1.iter_mut().zip(h_bold2.iter()) {
        *h1 += mul_vartime(*h2, &h_naf);
      }
      g_bold.truncate(n_hat);
      h_bold.truncate(n_hat);
      g_weight *= x_inv;
      h_weights.truncate(n_hat);
      for weight in &mut h_weights {
        *weight *= x;
      }

      // 32-34
      a = a1 * x;
      let a2 = a2 * x_inv;
      for (a, a2) in a.0.iter_mut().zip(a2.0.iter()) {
        *a += a2;
      }
      b = b1 * x_inv;
      let b2 = b2 * x;
      for (b, b2) in b.0.iter_mut().zip(b2.0.iter()) {
        *b += b2;
      }
    }

    // `if n = 1` case from line 14-17

    // Sanity
    debug_assert_eq!(g_bold.len(), 1);
    debug_assert_eq!(h_bold.len(), 1);
    debug_assert_eq!(a.len(), 1);
    debug_assert_eq!(b.len(), 1);

    // We simply send a/b
    transcript.push_scalar(a[0]);
    transcript.push_scalar(b[0]);
    Ok(())
  }
}

/// An error from verifying Inner-Product statements.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum IpVerifyError {
  /// The proof wasn't complete and the necessary values could not be read from the transcript.
  IncompleteProof,
}

impl<C: Ciphersuite> IpStatement<'_, C>
where
  C::F: FromUniformBytes<64>,
{
  /*
  This has room for optimization worth investigating further. It currently takes
  an iterative approach. It can be optimized further via divide and conquer.

  Assume there are 4 challenges.

  Iterative approach (current):
    1. Do the optimal multiplications across challenge column 0 and 1.
    2. Do the optimal multiplications across that result and column 2.
    3. Do the optimal multiplications across that result and column 3.

  Divide and conquer (worth investigating further):
    1. Do the optimal multiplications across challenge column 0 and 1.
    2. Do the optimal multiplications across challenge column 2 and 3.
    3. Multiply both results together.

  When there are 4 challenges (n=16), the iterative approach does 28 multiplications
  versus divide and conquer's 24.
  */
  fn challenge_products(challenges: &[(C::F, C::F)]) -> Vec<C::F> {
    let mut products = vec![C::F::ONE; 1 << challenges.len()];

    if !challenges.is_empty() {
      products[0] = challenges[0].1;
      products[1] = challenges[0].0;

      for (j, challenge) in challenges.iter().enumerate().skip(1) {
        let mut slots = (1 << (j + 1)) - 1;
        while slots > 0 {
          products[slots] = products[slots / 2] * challenge.0;
          products[slots - 1] = products[slots / 2] * challenge.1;

          slots = slots.saturating_sub(2);
        }
      }

      // Sanity check since if the above failed to populate, it'd be critical
      for product in &products {
        debug_assert!(!bool::from(product.is_zero()));
      }
    }

    products
  }

  /// Queue an Inner-Product proof for batch verification.
  ///
  /// This will return `Err(_)` if there is an error. This will return `Ok(_)` if the proof was
  /// successfully queued for batch verification. The caller is required to verify the batch in
  /// order to ensure the proof is actually correct.
  ///
  /// If this proof returns `Err(_)`, the BatchVerifier MUST be assumed corrupted and discarded.
  pub(crate) fn verify(
    self,
    verifier: &mut BatchVerifier<C>,
    transcript: &mut VerifierTranscript,
  ) -> Result<(), IpVerifyError> {
    if verifier.g_bold.len() < self.generators.len() {
      verifier.g_bold.resize(self.generators.len(), C::F::ZERO);
    }
    if verifier.h_bold.len() < self.generators.len() {
      verifier.h_bold.resize(self.generators.len(), C::F::ZERO);
    }

    let IpStatement { generators, h_bold_weights, u, P } = self;

    // Calculate the discrete log w.r.t. 2 for the amount of generators present
    let mut lr_len = 0;
    while (1 << lr_len) < generators.g_bold_slice().len() {
      lr_len += 1;
    }

    let weight = match P {
      P::Prover => panic!("prove called with a P specification which was for the prover"),
      P::Verifier { verifier_weight } => verifier_weight,
    };

    // Again, we start with the `else: (n > 1)` case

    // We need x, x_inv per lines 25-27 for lines 28-31
    let mut L = Vec::with_capacity(lr_len);
    let mut R = Vec::with_capacity(lr_len);
    let mut xs: Vec<C::F> = Vec::with_capacity(lr_len);
    for _ in 0 .. lr_len {
      L.push(transcript.read_point::<C>().map_err(|_| IpVerifyError::IncompleteProof)?);
      R.push(transcript.read_point::<C>().map_err(|_| IpVerifyError::IncompleteProof)?);
      let x = transcript.challenge::<C>();
      assert!(!bool::from(x.is_zero()), "transcript challenge was 0");
      xs.push(x);
    }

    // We calculate their inverse in batch
    let mut x_invs = xs.clone();
    (&mut x_invs).batch_invert();

    // Now, with x and x_inv, we need to calculate g_bold', h_bold', P'
    //
    // For the sake of performance, we solely want to calculate all of these in terms of scalings
    // for g_bold, h_bold, P, and don't want to actually perform intermediary scalings of the
    // points
    //
    // L and R are easy, as it's simply x**2, x**-2
    //
    // For the series of g_bold, h_bold, we use the `challenge_products` function
    // For how that works, please see its own documentation
    let product_cache = {
      let mut challenges = Vec::with_capacity(lr_len);
      verifier.additional.reserve(2 * lr_len);
      let x_iter = xs.into_iter().zip(x_invs);
      let lr_iter = L.into_iter().zip(R);
      for ((x, x_inv), (L, R)) in x_iter.zip(lr_iter) {
        challenges.push((x, x_inv));
        verifier.additional.push((weight * x.square(), L));
        verifier.additional.push((weight * x_inv.square(), R));
      }

      Self::challenge_products(&challenges)
    };

    // And now for the `if n = 1` case
    let a = transcript.read_scalar::<C>().map_err(|_| IpVerifyError::IncompleteProof)?;
    let b = transcript.read_scalar::<C>().map_err(|_| IpVerifyError::IncompleteProof)?;
    let c = a * b;

    // The multiexp of these terms equate to the final permutation of P
    // We now add terms for a * g_bold' + b * h_bold' b + c * u, with the scalars negative such
    // that the terms sum to 0 for an honest prover

    // The g_bold * a term case from line 16
    #[allow(clippy::needless_range_loop)]
    for i in 0 .. generators.g_bold_slice().len() {
      verifier.g_bold[i] -= weight * product_cache[i] * a;
    }
    // The h_bold * b term case from line 16
    for i in 0 .. generators.h_bold_slice().len() {
      verifier.h_bold[i] -=
        weight * product_cache[product_cache.len() - 1 - i] * b * h_bold_weights[i];
    }
    // The c * u term case from line 16
    verifier.g -= weight * c * u;

    Ok(())
  }
}
