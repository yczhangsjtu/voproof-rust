// mod template;

use crate::cs::{
  hpr::{HPRInstance, HPRSize, HPRWitness, HPR},
  pov::{POVInstance, POVSize, POVWitness, POV},
  r1cs::{R1CSInstance, R1CSSize, R1CSWitness, R1CS},
  CSSize, ConstraintSystem, Instance, Witness,
};
use crate::error::Error;
use crate::kzg::*;
use crate::kzg::{Proof as KZGProof, UniversalParams, VerifierKey};
use crate::tools::*;
use crate::*;
use ark_ec::{
  pairing::Pairing as PairingEngine, AffineRepr as AffineCurve, CurveGroup as ProjectiveCurve,
};
use ark_ff::{fields::batch_inversion, FftField, Field};
use ark_poly::{
  univariate::DensePolynomial as DensePoly, EvaluationDomain, Evaluations, GeneralEvaluationDomain,
  Polynomial,
};
use ark_poly_commit::DenseUVPolynomial as UVPolynomial;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
  collections::hash_map::HashMap, end_timer, ops::Mul, start_timer, test_rng, vec::Vec, One, Zero,
};

pub trait SNARKProverKey<E: PairingEngine> {}
pub trait SNARKVerifierKey<E: PairingEngine> {}
pub trait SNARKProof<E: PairingEngine> {}

// degree_bound can be larger than powers.len() when powers neglect the unused
// items in the middle.
// degree_bound always equals the exponent of the largest power + 1
pub fn vector_to_commitment<E: PairingEngine>(
  powers: &Vec<E::G1Affine>,
  vec: &Vec<E::ScalarField>,
  degree: u64,
) -> Result<Commitment<E>, Error> {
  KZG10::<E, DensePoly<E::ScalarField>>::commit_with_coefficients(
    &powers[if (degree as usize) < vec.len() {
      0
    } else {
      degree as usize - vec.len()
    }..],
    vec,
  )
}

pub fn scalar_to_commitment<E: PairingEngine>(
  g: &E::G1Affine,
  c: &E::ScalarField,
) -> Result<Commitment<E>, Error> {
  KZG10::<E, DensePoly<E::ScalarField>>::commit_single(g, c)
}

macro_rules! commit_scalar {
  ($vk:expr, $c:expr) => {
    scalar_to_commitment::<E>(&$vk.kzg_vk.g, &$c)
      .unwrap()
      .0
      .into_group()
  };
}

pub trait SNARK<E: PairingEngine> {
  type Size: CSSize;
  type CS: ConstraintSystem<E::ScalarField, Self::Size>;
  type PK: SNARKProverKey<E>;
  type VK: SNARKVerifierKey<E>;
  type Ins: Instance<E::ScalarField>;
  type Wit: Witness<E::ScalarField>;
  type Pf: SNARKProof<E>;

  fn setup(size: usize) -> Result<UniversalParams<E>, Error>;
  fn index(pp: &UniversalParams<E>, cs: &Self::CS) -> Result<(Self::PK, Self::VK), Error>;
  fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error>;
  fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error>;
}

pub mod voproof_hpr;
pub mod voproof_pov;
pub mod voproof_pov_prover_efficient;
pub mod voproof_r1cs;
pub mod voproof_r1cs_prover_efficient;
