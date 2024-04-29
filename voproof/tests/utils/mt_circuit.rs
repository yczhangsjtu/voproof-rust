use ark_crypto_primitives::{
  crh::{
    poseidon::{
      constraints::{CRHGadget, TwoToOneCRHGadget},
      TwoToOneCRH, CRH,
    },
    CRHScheme, CRHSchemeGadget, TwoToOneCRHScheme, TwoToOneCRHSchemeGadget,
  },
  merkle_tree::{
    constraints::{ConfigGadget, PathVar},
    Config, IdentityDigestConverter, Path,
  },
};
use ark_ec::pairing::Pairing as PairingEngine;
use ark_ff::fields::{FftField, Field, FpConfig as FpParameters, PrimeField};
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, uint64::UInt64, R1CSVar};
use ark_relations::{
  lc, ns,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};

type F = ark_bls12_381::Fr;
type E = ark_bls12_381::Bls12_381;
struct FieldMTConfig;
impl Config for FieldMTConfig {
  type Leaf = [F];
  type LeafDigest = F;
  type LeafInnerDigestConverter = IdentityDigestConverter<F>;
  type InnerDigest = F;
  type LeafHash = CRH<F>;
  type TwoToOneHash = TwoToOneCRH<F>;
}

struct FieldMTConfigVar;
impl ConfigGadget<FieldMTConfig, F> for FieldMTConfigVar {
  type Leaf = [FpVar<F>];
  type LeafDigest = FpVar<F>;
  type LeafInnerConverter = IdentityDigestConverter<FpVar<F>>;
  type InnerDigest = FpVar<F>;
  type LeafHash = CRHGadget<F>;
  type TwoToOneHash = TwoToOneCRHGadget<F>;
}

#[derive(Copy, Clone)]
pub struct MerkleTreeCircuit {
  pub height: usize,
}

impl ConstraintSynthesizer<F> for MerkleTreeCircuit {
  fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
    let generator: F = <<E as PairingEngine>::ScalarField as FftField>::GENERATOR;
    let leaf_crh_params = super::poseidon_parameters();
    let two_to_one_params = leaf_crh_params.clone();
    let mut path = Path::<FieldMTConfig> {
      leaf_sibling_hash: generator,
      auth_path: vec![generator; self.height],
      leaf_index: 0,
    };
    let leaf = vec![generator];
    let mut curr = CRH::<F>::evaluate(&leaf_crh_params, leaf.clone()).unwrap();
    curr = TwoToOneCRH::<F>::evaluate(&two_to_one_params, &curr, &path.leaf_sibling_hash).unwrap();
    for node in path.auth_path.iter() {
      curr = TwoToOneCRH::<F>::evaluate(&two_to_one_params, &curr, &node).unwrap();
    }
    let root = curr;
    assert!(path
      .verify(&leaf_crh_params, &two_to_one_params, &root, leaf.clone())
      .unwrap());

    let root = FpVar::new_input(cs.clone(), || Ok(root)).unwrap();
    let constraints_from_digest = cs.num_constraints();
    println!("constraints from digest: {}", constraints_from_digest);

    let leaf_crh_params_var =
      <CRHGadget<F> as CRHSchemeGadget<CRH<F>, _>>::ParametersVar::new_constant(
        ns!(cs, "leaf_crh_params"),
        &leaf_crh_params,
      )
      .unwrap();

    let two_to_one_crh_params_var = <TwoToOneCRHGadget<F> as TwoToOneCRHSchemeGadget<
      TwoToOneCRH<F>,
      _,
    >>::ParametersVar::new_constant(
      ns!(cs, "two_to_one_params"), &leaf_crh_params
    )
    .unwrap();

    let leaf_g: Vec<_> = leaf
      .iter()
      .map(|x| FpVar::new_input(cs.clone(), || Ok(*x)).unwrap())
      .collect();

    let mut cw =
      PathVar::<FieldMTConfig, F, FieldMTConfigVar>::new_witness(ns!(cs, "new_witness"), || {
        Ok(&path)
      })
      .unwrap();

    // assert!(cs.is_satisfied().unwrap());

    let leaf_pos = UInt64::new_witness(cs.clone(), || Ok(0))
      .unwrap()
      .to_bits_le();
    cw.set_leaf_position(leaf_pos.clone());

    // let expected_leaf_pos = leaf_pos.value().unwrap();
    // let mut actual_leaf_pos = cw.get_leaf_position().value().unwrap();
    // actual_leaf_pos.extend((0..(64 - actual_leaf_pos.len())).map(|_| false));
    // assert_eq!(expected_leaf_pos, actual_leaf_pos);

    cw.verify_membership(
      &leaf_crh_params_var,
      &two_to_one_crh_params_var,
      &root,
      &leaf_g,
    )
    .unwrap();
    // assert!(
    // cs.is_satisfied().unwrap(),
    // "verification constraints not satisfied"
    // );

    println!("number of public inputs {}", cs.num_instance_variables());

    println!("number of witness {}", cs.num_witness_variables());
    Ok(())
  }
}
