use ark_bls12_381::Bls12_381 as E;
use ark_bls12_381::Fr;
use ark_ec::PairingEngine;
use ark_ff::fields::{FftField, Fp256, FpParameters, PrimeField};
use ark_groth16::{
  create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use ark_poly::univariate::DensePolynomial as P;
use ark_poly_commit::sonic_pc::SonicKZG10;
use ark_relations::{
  lc,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};
use ark_std::{end_timer, start_timer};
use blake2::Blake2s;
use voproof::max;
use voproof::tools::to_field;
mod utils;
use utils::mt_circuit::MerkleTreeCircuit;
use utils::test_circuit::TestCircuit;

fn gen_test_circ<E: PairingEngine>(
  scale: usize,
) -> (TestCircuit<E::ScalarField>, Vec<E::ScalarField>) {
  let rng = &mut ark_std::test_rng();
  let c = TestCircuit::<E::ScalarField> {
    a: Some(to_field::<E::ScalarField>(3)),
    b: Some(to_field::<E::ScalarField>(2)),
    num_variables: scale,
    num_constraints: scale,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];

  let cs = ArkR1CS::<E::ScalarField>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  cs.inline_all_lcs();
  let matrices = cs.to_matrices().unwrap();
  let (m, n, s) = (
    matrices.num_constraints,
    matrices.num_instance_variables + matrices.num_witness_variables,
    max!(
      matrices.a_num_non_zero,
      matrices.b_num_non_zero,
      matrices.c_num_non_zero
    ),
  );
  (c, x)
}

fn gen_mt_circ<E: PairingEngine<Fr = Fp256<ark_bls12_381::FrParameters>>>(
  scale: usize,
) -> (MerkleTreeCircuit, Vec<E::ScalarField>) {
  let rng = &mut ark_std::test_rng();
  let c = MerkleTreeCircuit { height: scale };

  let cs = ArkR1CS::<E::ScalarField>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  cs.inline_all_lcs();
  let matrices = cs.to_matrices().unwrap();
  let x = cs
    .into_inner()
    .unwrap()
    .instance_assignment
    .iter()
    .skip(1)
    .map(|x| *x)
    .collect::<Vec<E::ScalarField>>();
  let (m, n, s) = (
    matrices.num_constraints,
    matrices.num_instance_variables + matrices.num_witness_variables,
    max!(
      matrices.a_num_non_zero,
      matrices.b_num_non_zero,
      matrices.c_num_non_zero
    ),
  );
  (c, x)
}

macro_rules! define_test {
  ($func_name:ident, $circuit_generator:ident, $scale:literal) => {
    #[test]
    fn $func_name() {
      let (c, x) = $circuit_generator::<E>($scale);
      let timer = start_timer!(|| "Indexing");
      let rng = &mut ark_std::test_rng();
      let params = generate_random_parameters::<E, _, _>(c, rng).unwrap();
      end_timer!(timer);
      let pvk = prepare_verifying_key(&params.vk);
      let timer = start_timer!(|| "Proving");
      let proof = create_random_proof(c, &params, rng).unwrap();
      end_timer!(timer);
      let timer = start_timer!(|| "Verifier");
      assert!(verify_proof(&pvk, &proof, &x).unwrap());
      end_timer!(timer);
    }
  };
}

define_test!(test_groth16_test_circuit_scale_1000, gen_test_circ, 1000);
define_test!(test_groth16_test_circuit_scale_2000, gen_test_circ, 2000);
define_test!(test_groth16_test_circuit_scale_4000, gen_test_circ, 4000);
define_test!(test_groth16_test_circuit_scale_8000, gen_test_circ, 8000);
define_test!(test_groth16_test_circuit_scale_16000, gen_test_circ, 16000);
define_test!(test_groth16_test_circuit_scale_32000, gen_test_circ, 32000);
define_test!(test_groth16_test_circuit_scale_64000, gen_test_circ, 64000);
define_test!(
  test_groth16_test_circuit_scale_128000,
  gen_test_circ,
  128000
);
define_test!(
  test_groth16_test_circuit_scale_256000,
  gen_test_circ,
  256000
);
define_test!(
  test_groth16_test_circuit_scale_512000,
  gen_test_circ,
  512000
);
define_test!(
  test_groth16_test_circuit_scale_1024000,
  gen_test_circ,
  1024000
);
define_test!(test_groth16_mt_circuit_scale_8, gen_mt_circ, 8);
define_test!(test_groth16_mt_circuit_scale_16, gen_mt_circ, 16);
define_test!(test_groth16_mt_circuit_scale_32, gen_mt_circ, 32);
define_test!(test_groth16_mt_circuit_scale_64, gen_mt_circ, 64);
