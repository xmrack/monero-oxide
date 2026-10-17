//! Vector commitments across the indexes whose tables are retained and those built per use.
//!
//! The unit tests retain fewer tables, so this covers the amount retained outside of them.

use rand_core::{RngCore as _, OsRng};

use ciphersuite::{group::ff::Field as _, Ciphersuite, Ristretto};

use multiexp::multiexp_vartime;

use generalized_bulletproofs::tests::insecure_test_generators;

type F = <Ristretto as Ciphersuite>::F;

#[test]
fn test_vector_commitments_beyond_cached_tables() {
  const GENERATORS: usize = 8192;
  let generators = insecure_test_generators::<_, Ristretto>(&mut OsRng, GENERATORS).unwrap();

  let mut commitments = vec![];
  for n in [GENERATORS, 4097, 4096, 4095, 2049, 100, 1] {
    let (values, small): (Vec<_>, Vec<_>) = (0 .. n)
      .map(|_| match OsRng.next_u32() % 3 {
        0 => (F::from(OsRng.next_u64() % 512), true),
        1 => (F::from(OsRng.next_u64() % 512), false),
        _ => (F::random(&mut OsRng), false),
      })
      .unzip();
    commitments.push((values, small, F::random(&mut OsRng)));
  }

  let expected = commitments
    .iter()
    .map(|(values, _, mask)| {
      let terms = values.iter().copied().zip(generators.g_bold_slice().iter().copied());
      multiexp_vartime(&terms.chain([(*mask, generators.h())]).collect::<Vec<_>>())
    })
    .collect::<Vec<_>>();

  // The first pass builds the retained tables, and the second reads them
  for _ in 0 .. 2 {
    for ((values, small, mask), expected) in commitments.iter().zip(&expected) {
      assert_eq!(generators.vector_commitment(values, small, mask), Some(*expected));
    }
  }
}
