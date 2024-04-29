use crate::*;
use ark_ec::{pairing::Pairing as PairingEngine, AffineRepr as AffineCurve, Group as _};
use ark_ff::{Field, PrimeField, ToConstraintField, Zero};
use ark_poly_commit::*;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError, Valid};
use ark_std::{
  // collections::BTreeMap,
  borrow::Cow,
  io::{Read, Write},
  marker::PhantomData,
  ops::{Add, AddAssign, Mul},
  rand::RngCore,
};

/// `UniversalParams` are the universal parameters for the KZG10 scheme.
#[derive(Derivative)]
#[derivative(Clone(bound = ""), Debug(bound = ""))]
pub struct UniversalParams<E: PairingEngine> {
  /// Group elements of the form `{ \beta^i G }`, where `i` ranges from 0 to `degree`.
  pub powers_of_g: Vec<E::G1Affine>,
  //// Group elements of the form `{ \beta^i \gamma G }`, where `i` ranges from 0 to `degree`.
  // pub powers_of_gamma_g: BTreeMap<usize, E::G1Affine>,
  /// The generator of G2.
  pub h: E::G2Affine,
  /// \beta times the above generator of G2.
  pub beta_h: E::G2Affine,
  //// Group elements of the form `{ \beta^i G2 }`, where `i` ranges from `0` to `-degree`.
  // pub neg_powers_of_h: BTreeMap<usize, E::G2Affine>,
  /// The generator of G2, prepared for use in pairings.
  #[derivative(Debug = "ignore")]
  pub prepared_h: E::G2Prepared,
  /// \beta times the above generator of G2, prepared for use in pairings.
  #[derivative(Debug = "ignore")]
  pub prepared_beta_h: E::G2Prepared,
}

impl<E: PairingEngine> Valid for UniversalParams<E> {
  fn check(&self) -> Result<(), SerializationError> {
    self.powers_of_g.check()?;
    self.h.check()?;
    self.beta_h.check()?;
    self.prepared_h.check()?;
    self.prepared_beta_h.check()?;
    Ok(())
  }
}

impl<E: PairingEngine> UniversalParams<E> {
  pub fn empty() -> Self {
    let powers_of_g = Vec::new();
    let h = E::G2Affine::default();
    let beta_h = E::G2Affine::default();
    let prepared_h = E::G2Prepared::default();
    let prepared_beta_h = E::G2Prepared::default();
    Self {
      powers_of_g,
      h,
      beta_h,
      prepared_h,
      prepared_beta_h,
    }
  }
}

impl<E: PairingEngine> PCUniversalParams for UniversalParams<E> {
  fn max_degree(&self) -> usize {
    self.powers_of_g.len() - 1
  }
}

impl<E: PairingEngine> CanonicalSerialize for UniversalParams<E> {
  fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
    self.powers_of_g.serialized_size(compress)
      + self.h.serialized_size(compress)
      + self.beta_h.serialized_size(compress)
  }

  fn serialize_with_mode<W: Write>(
    &self,
    mut writer: W,
    compress: ark_serialize::Compress,
  ) -> Result<(), SerializationError> {
    self
      .powers_of_g
      .serialize_with_mode(&mut writer, compress)?;
    self.h.serialize_with_mode(&mut writer, compress)?;
    self.beta_h.serialize_with_mode(&mut writer, compress)
  }
}

impl<E: PairingEngine> CanonicalDeserialize for UniversalParams<E> {
  fn deserialize_with_mode<R: Read>(
    mut reader: R,
    compress: ark_serialize::Compress,
    validate: ark_serialize::Validate,
  ) -> Result<Self, SerializationError> {
    let powers_of_g = Vec::<E::G1Affine>::deserialize_with_mode(&mut reader, compress, validate)?;
    let h = E::G2Affine::deserialize_with_mode(&mut reader, compress, validate)?;
    let beta_h = E::G2Affine::deserialize_with_mode(&mut reader, compress, validate)?;

    let prepared_h = E::G2Prepared::from(h.clone());
    let prepared_beta_h = E::G2Prepared::from(beta_h.clone());

    Ok(Self {
      powers_of_g,
      h,
      beta_h,
      prepared_h,
      prepared_beta_h,
    })
  }
}

/// `Powers` is used to commit to and create evaluation proofs for a given
/// polynomial.
#[derive(Derivative)]
#[derivative(
  Default(bound = ""),
  Hash(bound = ""),
  Clone(bound = ""),
  Debug(bound = "")
)]
pub struct Powers<'a, E: PairingEngine> {
  /// Group elements of the form `β^i G`, for different values of `i`.
  pub powers_of_g: Cow<'a, [E::G1Affine]>,
}

impl<E: PairingEngine> Powers<'_, E> {
  /// The number of powers in `self`.
  pub fn size(&self) -> usize {
    self.powers_of_g.len()
  }
}

/// `VerifierKey` is used to check evaluation proofs for a given commitment.
#[derive(Derivative)]
#[derivative(Default(bound = ""), Clone(bound = ""), Debug(bound = ""))]
pub struct VerifierKey<E: PairingEngine> {
  /// The generator of G1.
  pub g: E::G1Affine,
  /// The generator of G2.
  pub h: E::G2Affine,
  /// \beta times the above generator of G2.
  pub beta_h: E::G2Affine,
  /// The generator of G2, prepared for use in pairings.
  #[derivative(Debug = "ignore")]
  pub prepared_h: E::G2Prepared,
  /// \beta times the above generator of G2, prepared for use in pairings.
  #[derivative(Debug = "ignore")]
  pub prepared_beta_h: E::G2Prepared,
}

impl<E: PairingEngine> CanonicalSerialize for VerifierKey<E> {
  fn serialize_with_mode<W: Write>(
    &self,
    mut writer: W,
    compress: ark_serialize::Compress,
  ) -> Result<(), SerializationError> {
    self.g.serialize_with_mode(&mut writer, compress)?;
    self.h.serialize_with_mode(&mut writer, compress)?;
    self.beta_h.serialize_with_mode(&mut writer, compress)
  }

  fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
    self.g.serialized_size(compress)
      + self.h.serialized_size(compress)
      + self.beta_h.serialized_size(compress)
  }
}

impl<E: PairingEngine> Valid for VerifierKey<E> {
  fn check(&self) -> Result<(), SerializationError> {
    self.g.check()?;
    self.h.check()?;
    self.beta_h.check()?;
    self.prepared_h.check()?;
    self.prepared_beta_h.check()?;
    Ok(())
  }
}

impl<E: PairingEngine> CanonicalDeserialize for VerifierKey<E> {
  fn deserialize_with_mode<R: Read>(
    mut reader: R,
    compress: ark_serialize::Compress,
    validate: ark_serialize::Validate,
  ) -> Result<Self, SerializationError> {
    let g = E::G1Affine::deserialize_with_mode(&mut reader, compress, validate)?;
    let h = E::G2Affine::deserialize_with_mode(&mut reader, compress, validate)?;
    let beta_h = E::G2Affine::deserialize_with_mode(&mut reader, compress, validate)?;

    let prepared_h = E::G2Prepared::from(h.clone());
    let prepared_beta_h = E::G2Prepared::from(beta_h.clone());

    Ok(Self {
      g,
      h,
      beta_h,
      prepared_h,
      prepared_beta_h,
    })
  }
}

impl<E: PairingEngine> ToConstraintField<<E::BaseField as Field>::BasePrimeField> for VerifierKey<E>
where
  E::G1Affine: ToConstraintField<<E::BaseField as Field>::BasePrimeField>,
  E::G2Affine: ToConstraintField<<E::BaseField as Field>::BasePrimeField>,
{
  fn to_field_elements(&self) -> Option<Vec<<E::BaseField as Field>::BasePrimeField>> {
    let mut res = Vec::new();

    res.extend_from_slice(&self.g.to_field_elements().unwrap());
    res.extend_from_slice(&self.h.to_field_elements().unwrap());
    res.extend_from_slice(&self.beta_h.to_field_elements().unwrap());

    Some(res)
  }
}

/// `PreparedVerifierKey` is the fully prepared version for checking evaluation proofs for a given commitment.
#[derive(Derivative)]
#[derivative(Default(bound = ""), Clone(bound = ""), Debug(bound = ""))]
pub struct PreparedVerifierKey<E: PairingEngine> {
  /// The generator of G1, prepared for power series.
  pub prepared_g: Vec<E::G1Affine>,
  /// The generator of G2, prepared for use in pairings.
  pub prepared_h: E::G2Prepared,
  /// \beta times the above generator of G2, prepared for use in pairings.
  pub prepared_beta_h: E::G2Prepared,
}

impl<E: PairingEngine> PreparedVerifierKey<E> {
  /// prepare `PreparedVerifierKey` from `VerifierKey`
  pub fn prepare(vk: &VerifierKey<E>) -> Self {
    let supported_bits = E::ScalarField::MODULUS_BIT_SIZE;

    let mut prepared_g = Vec::<E::G1Affine>::new();
    let mut g = E::G1::from(vk.g.clone());
    for _ in 0..supported_bits {
      prepared_g.push(g.clone().into());
      g.double_in_place();
    }

    Self {
      prepared_g,
      prepared_h: vk.prepared_h.clone(),
      prepared_beta_h: vk.prepared_beta_h.clone(),
    }
  }
}

/// `Commitment` commits to a polynomial. It is output by `KZG10::commit`.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
  Default(bound = ""),
  Hash(bound = ""),
  Clone(bound = ""),
  Copy(bound = ""),
  Debug(bound = ""),
  PartialEq(bound = ""),
  Eq(bound = "")
)]
pub struct Commitment<E: PairingEngine>(
  /// The commitment is a group element.
  pub E::G1Affine,
);

impl<E: PairingEngine> PCCommitment for Commitment<E> {
  #[inline]
  fn empty() -> Self {
    Commitment(E::G1Affine::zero())
  }

  fn has_degree_bound(&self) -> bool {
    false
  }
}

impl<E: PairingEngine> ToConstraintField<<E::BaseField as Field>::BasePrimeField> for Commitment<E>
where
  E::G1Affine: ToConstraintField<<E::BaseField as Field>::BasePrimeField>,
{
  fn to_field_elements(&self) -> Option<Vec<<E::BaseField as Field>::BasePrimeField>> {
    self.0.to_field_elements()
  }
}

impl<'a, E: PairingEngine> AddAssign<(E::ScalarField, &'a Commitment<E>)> for Commitment<E> {
  #[inline]
  fn add_assign(&mut self, (f, other): (E::ScalarField, &'a Commitment<E>)) {
    let mut other = other.0.mul(f);
    other.add_assign(&self.0);
    self.0 = other.into();
  }
}

/// `PreparedCommitment` commits to a polynomial and prepares for mul_bits.
#[derive(Derivative)]
#[derivative(
  Default(bound = ""),
  Hash(bound = ""),
  Clone(bound = ""),
  Debug(bound = ""),
  PartialEq(bound = ""),
  Eq(bound = "")
)]
pub struct PreparedCommitment<E: PairingEngine>(
  /// The commitment is a group element.
  pub Vec<E::G1Affine>,
);

impl<E: PairingEngine> PreparedCommitment<E> {
  /// prepare `PreparedCommitment` from `Commitment`
  pub fn prepare(comm: &Commitment<E>) -> Self {
    let mut prepared_comm = Vec::<E::G1Affine>::new();
    let mut cur = E::G1::from(comm.0.clone());

    let supported_bits = E::ScalarField::MODULUS_BIT_SIZE;

    for _ in 0..supported_bits {
      prepared_comm.push(cur.clone().into());
      cur.double_in_place();
    }

    Self { 0: prepared_comm }
  }
}

/// `Randomness` hides the polynomial inside a commitment. It is output by `KZG10::commit`.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
  Hash(bound = ""),
  Clone(bound = ""),
  Debug(bound = ""),
  PartialEq(bound = ""),
  Eq(bound = "")
)]
pub struct Randomness<F: PrimeField, P: DenseUVPolynomial<F>> {
  /// For KZG10, the commitment randomness is a random polynomial.
  pub blinding_polynomial: P,
  _field: PhantomData<F>,
}

impl<F: PrimeField, P: DenseUVPolynomial<F>> Randomness<F, P> {
  /// Does `self` provide any hiding properties to the corresponding commitment?
  /// `self.is_hiding() == true` only if the underlying polynomial is non-zero.
  #[inline]
  pub fn is_hiding(&self) -> bool {
    !self.blinding_polynomial.is_zero()
  }

  /// What is the degree of the hiding polynomial for a given hiding bound?
  #[inline]
  pub fn calculate_hiding_polynomial_degree(hiding_bound: usize) -> usize {
    hiding_bound + 1
  }
}

impl<F: PrimeField, P: DenseUVPolynomial<F>> PCRandomness for Randomness<F, P> {
  fn empty() -> Self {
    Self {
      blinding_polynomial: P::zero(),
      _field: PhantomData,
    }
  }

  fn rand<R: RngCore>(hiding_bound: usize, _: bool, _: Option<usize>, rng: &mut R) -> Self {
    let mut randomness = Randomness::empty();
    let hiding_poly_degree = Self::calculate_hiding_polynomial_degree(hiding_bound);
    randomness.blinding_polynomial = P::rand(hiding_poly_degree, rng);
    randomness
  }
}

impl<'a, F: PrimeField, P: DenseUVPolynomial<F>> Add<&'a Randomness<F, P>> for Randomness<F, P> {
  type Output = Self;

  #[inline]
  fn add(mut self, other: &'a Self) -> Self {
    self.blinding_polynomial += &other.blinding_polynomial;
    self
  }
}

impl<'a, F: PrimeField, P: DenseUVPolynomial<F>> Add<(F, &'a Randomness<F, P>)>
  for Randomness<F, P>
{
  type Output = Self;

  #[inline]
  fn add(mut self, other: (F, &'a Randomness<F, P>)) -> Self {
    self += other;
    self
  }
}

impl<'a, F: PrimeField, P: DenseUVPolynomial<F>> AddAssign<&'a Randomness<F, P>>
  for Randomness<F, P>
{
  #[inline]
  fn add_assign(&mut self, other: &'a Self) {
    self.blinding_polynomial += &other.blinding_polynomial;
  }
}

impl<'a, F: PrimeField, P: DenseUVPolynomial<F>> AddAssign<(F, &'a Randomness<F, P>)>
  for Randomness<F, P>
{
  #[inline]
  fn add_assign(&mut self, (f, other): (F, &'a Randomness<F, P>)) {
    self.blinding_polynomial += (f, &other.blinding_polynomial);
  }
}

/// `Proof` is an evaluation proof that is output by `KZG10::open`.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
  Default(bound = ""),
  Hash(bound = ""),
  Clone(bound = ""),
  Copy(bound = ""),
  Debug(bound = ""),
  PartialEq(bound = ""),
  Eq(bound = "")
)]
pub struct Proof<E: PairingEngine> {
  /// This is a commitment to the witness polynomial; see [KZG10] for more details.
  pub w: E::G1Affine,
  //// This is the evaluation of the random polynomial at the point for which
  //// the evaluation proof was produced.
  // pub random_v: Option<E::ScalarField>,
}
