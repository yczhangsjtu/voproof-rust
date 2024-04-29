use ark_ec::pairing::Pairing as PairingEngine;
use ark_serialize::CanonicalSerialize;
use ark_std::test_rng;
use voproof::cs::{hpr::*, ConstraintSystem};
use voproof::error::Error;
use voproof::fmt_ff_vector;
use voproof::kzg::UniversalParams;
use voproof::snarks::{voproof_hpr::*, SNARK};
use voproof::tools::{fmt_field, try_to_int};

fn run_hpr_example<E: PairingEngine>(scale: usize) -> Result<(), Error> {
  let rng = &mut test_rng();
  let (hpr, instance, witness) =
    generate_random_hpr_instance(scale as u64, scale as u64, scale as u64 / 5, rng);

  if hpr.satisfy(&instance, &witness) {
    println!("HPR satisfied!");
  } else {
    println!("HPR unsatisfied!");
  }

  let max_degree = VOProofHPR::get_max_degree(hpr.get_size());
  // Let the universal parameters take a larger size than expected
  let universal_params: UniversalParams<E> = VOProofHPR::setup(max_degree + 10).unwrap();
  println!(
    "Universal parameter size: {}",
    universal_params.powers_of_g.len()
  );
  let (pk, vk) = VOProofHPR::index(&universal_params, &hpr).unwrap();
  println!("Degree bound: {}", vk.degree_bound);
  println!("Max degree: {}", pk.max_degree);
  println!("Prover key matrix size: {}", pk.cap_m_mat.0.len());
  println!("Prover key u size: {}", pk.u_vec.len());
  println!("Prover key v size: {}", pk.v_vec.len());
  println!("Prover key w size: {}", pk.w_vec.len());

  println!("M A row indices: {:?}", pk.cap_m_mat.0);
  println!("M A col indices: {:?}", pk.cap_m_mat.1);
  println!("M A vals: {}", fmt_ff_vector!(pk.cap_m_mat.2));
  let vksize = vk.size.clone();
  println!("H: {}", vksize.nrows);
  println!("K: {}", vksize.ncols);

  let proof = VOProofHPR::prove(&pk, &instance, &witness)?;
  println!(
    "Proof size: {}",
    proof.serialized_size(ark_serialize::Compress::No)
  );
  VOProofHPR::verify(&vk, &instance, &proof)
}

#[test]
fn test_simple_hpr_small_scales() {
  assert!(run_hpr_example::<ark_bls12_381::Bls12_381>(5).is_ok());
  assert!(run_hpr_example::<ark_bls12_381::Bls12_381>(10).is_ok());
  assert!(run_hpr_example::<ark_bls12_381::Bls12_381>(15).is_ok());
  assert!(run_hpr_example::<ark_bls12_381::Bls12_381>(20).is_ok());
}
