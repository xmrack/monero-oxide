#![expect(missing_docs)]

use zeroize::Zeroizing;
use rand_core::OsRng;

use curve25519_dalek::{
  constants::{ED25519_BASEPOINT_POINT, EIGHT_TORSION},
  edwards::EdwardsPoint,
  traits::Identity as _,
};

use monero_wallet::{
  ed25519::{Scalar, Point, Commitment},
  ringct::{RctType, clsag::Decoys},
  interface::FeeRate,
  address::{Network, AddressType, MoneroAddress},
  send::{Change, SendError, SignableTransaction},
  ViewPair, OutputWithDecoys,
};

fn random_point() -> EdwardsPoint {
  Scalar::random(&mut OsRng).into() * ED25519_BASEPOINT_POINT
}

fn input() -> OutputWithDecoys {
  let key = random_point();
  let mut bytes = vec![];
  bytes.extend(key.compress().to_bytes());
  Scalar::random(&mut OsRng).write(&mut bytes).unwrap();
  Commitment::new(Scalar::random(&mut OsRng), 1_000_000_000_000).write(&mut bytes).unwrap();
  let ring = (0 .. 16).map(|_| [Point::from(key), Point::from(random_point())]).collect();
  Decoys::new(vec![1; 16], 0, ring).unwrap().write(&mut bytes).unwrap();
  OutputWithDecoys::read(&mut bytes.as_slice()).unwrap()
}

fn send_to(spend: EdwardsPoint, view: EdwardsPoint) -> Result<SignableTransaction, SendError> {
  let address = MoneroAddress::new(
    Network::Mainnet,
    AddressType::Subaddress,
    Point::from(spend),
    Point::from(view),
  );
  let change = Change::new(
    ViewPair::new(Point::from(random_point()), Zeroizing::new(Scalar::random(&mut OsRng))).unwrap(),
    None,
  );
  SignableTransaction::new(
    RctType::ClsagBulletproofPlus,
    Zeroizing::new([0; 32]),
    vec![input()],
    vec![(address, 1_000_000_000)],
    change,
    vec![],
    FeeRate::new(20_000, 10_000).unwrap(),
  )
}

fn rejected(res: Result<SignableTransaction, SendError>) {
  assert_eq!(res.unwrap_err(), SendError::InvalidAddress);
}

#[test]
fn honest_address_is_accepted() {
  send_to(random_point(), random_point()).unwrap();
}

#[test]
fn identity_spend_key_is_rejected() {
  rejected(send_to(EdwardsPoint::identity(), random_point()));
}

#[test]
fn torsioned_spend_key_is_rejected() {
  rejected(send_to(EIGHT_TORSION[1], random_point()));
  rejected(send_to(random_point() + EIGHT_TORSION[1], random_point()));
}

#[test]
fn identity_or_torsioned_view_key_is_rejected() {
  rejected(send_to(random_point(), EdwardsPoint::identity()));
  rejected(send_to(random_point(), EIGHT_TORSION[1]));
}
