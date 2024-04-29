use ark_ec::pairing::Pairing as PairingEngine;
use ark_ff::{FftField, Fp256, FpConfig as FpParameters, PrimeField};
use ark_relations::{
  lc, ns,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};
use ark_serialize::CanonicalSerialize;
use ark_std::{end_timer, start_timer, Zero};
use voproof::cs::{circuit::fan_in_two::FanInTwoCircuit, pov::*, r1cs::*, ConstraintSystem};
use voproof::error::Error;
use voproof::kzg::UniversalParams;
use voproof::snarks::{voproof_pov::*, voproof_pov_prover_efficient::*, SNARK};
use voproof::tools::{fmt_field, to_field, try_to_int};
use voproof::{fmt_ff_vector, generator_of, max};
mod utils;
use utils::mt_circuit::MerkleTreeCircuit;
use utils::test_circuit::TestCircuit;

macro_rules! define_run_pov_example {
  ($func_name:ident, $snark:ident) => {
    fn $func_name<E: PairingEngine>() -> Result<(), Error> {
      let mut circ = FanInTwoCircuit::<E::ScalarField>::new();
      let a = circ.add_global_input_variable().unwrap();
      let b = circ.add_global_input_variable().unwrap();
      let c = circ.add_global_input_variable().unwrap();
      let d = circ.add_vars(&a, &b);
      let e = circ.mul_vars(&b, &c);
      let f = circ.mul_vars(&d, &e);
      let g = circ.add_vars(&a, &d);
      let h = circ.mul_vars(&g, &f);
      let o = circ.const_var(to_field::<E::ScalarField>(10));
      let p = circ.mul_vars(&h, &o);
      circ.mark_as_complete().unwrap();
      circ.mark_variable_as_public(&a).unwrap();
      circ.mark_variable_as_public(&p).unwrap();
      circ
        .evaluate(&vec![
          to_field::<E::ScalarField>(1),
          to_field::<E::ScalarField>(2),
          to_field::<E::ScalarField>(3),
        ])
        .unwrap();
      let ins = POVInstance {
        instance: circ.get_instance().unwrap(),
      };
      let mut wit = POVWitness {
        witness: circ.get_witness().unwrap(),
      };
      println!("{:?}", ins.instance.0);
      println!("{}", fmt_ff_vector!(ins.instance.1));
      println!("{}", fmt_ff_vector!(wit.witness.0));
      println!("{}", fmt_ff_vector!(wit.witness.1));
      println!("{}", fmt_ff_vector!(wit.witness.2));
      println!("{:?}", circ.get_wiring());
      assert_eq!(circ.get_add_num(), 2);
      assert_eq!(circ.get_mul_num(), 4);
      assert_eq!(circ.get_const_num(), 1);
      assert_eq!(wit.witness.0.len(), 7);
      assert_eq!(wit.witness.1.len(), 7);
      assert_eq!(wit.witness.2.len(), 7);
      let pov = POV::from(circ);
      assert!(pov.satisfy(&ins, &wit));
      let max_degree = $snark::get_max_degree(pov.get_size());
      // Let the universal parameters take a larger size than expected
      let universal_params: UniversalParams<E> = $snark::setup(max_degree + 10).unwrap();
      println!(
        "Universal parameter size: {}",
        universal_params.powers_of_g.len()
      );
      let (pk, vk) = $snark::index(&universal_params, &pov).unwrap();
      println!("Degree bound: {}", vk.degree_bound);
      println!("Max degree: {}", pk.max_degree);
      println!("Prover key sigma size: {}", pk.sigma_vec.len());
      println!("Prover key d size: {}", pk.d_vec.len());

      let mut proof = $snark::prove(&pk, &ins, &wit)?;
      $snark::verify(&vk, &ins, &proof)?;
      println!(
        "Proof size: {}",
        proof.serialized_size(ark_serialize::Compress::No)
      );
      proof.y = E::ScalarField::zero();
      let result = $snark::verify(&vk, &ins, &proof);
      assert!(result.is_err());
      wit.witness.0[0] = E::ScalarField::zero();
      let result = $snark::prove(&pk, &ins, &wit);
      assert!(result.is_err());
      Ok(())
    }
  };
}

define_run_pov_example!(run_pov_example, VOProofPOV);
define_run_pov_example!(run_pov_pe_example, VOProofPOVProverEfficient);

macro_rules! define_test_simple_pov {
  ($func_name: ident, $exec_name: ident) => {
    #[test]
    fn $func_name() {
      assert!($exec_name::<ark_bls12_381::Bls12_381>().is_ok());
    }
  };
}

define_test_simple_pov!(test_simple_pov, run_pov_example);
define_test_simple_pov!(test_simple_pov_pe, run_pov_pe_example);

fn run_pov_from_r1cs<E: PairingEngine>(scale: usize) {
  let c = TestCircuit::<E::ScalarField> {
    a: Some(generator_of!(E)),
    b: Some(generator_of!(E) * generator_of!(E)),
    num_variables: scale,
    num_constraints: scale,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  let w = vec![c.a.unwrap(); scale - 3];

  let cs = ArkR1CS::<E::ScalarField>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  let r1cs = R1CS::from(cs.into_inner().unwrap());
  println!("R1CS num rows: {}", r1cs.nrows);
  println!("R1CS num cols: {}", r1cs.ncols);
  println!(
    "R1CS non entries: {}, {}, {} (total {}, max {})",
    r1cs.arows.len(),
    r1cs.brows.len(),
    r1cs.crows.len(),
    r1cs.arows.len() + r1cs.brows.len() + r1cs.crows.len(),
    max!(r1cs.arows.len(), r1cs.brows.len(), r1cs.crows.len())
  );

  let instance = R1CSInstance { instance: x };
  let witness = R1CSWitness { witness: w };

  if r1cs.satisfy(&instance, &witness) {
    println!("R1CS satisfied!");
  } else {
    println!("R1CS unsatisfied!");
  }

  let mut circ = FanInTwoCircuit::from(r1cs.clone());
  let input = instance
    .instance
    .clone()
    .into_iter()
    .chain(witness.witness.clone().into_iter())
    .collect();
  circ.evaluate(&input).unwrap();
  let output = circ.get_output().unwrap();
  assert!(output.iter().all(|o| o.is_zero()));
  // assert_eq!(output, vec![E::ScalarField::zero(); r1cs.nrows as usize]);

  let (pov, instance, witness) = pov_triple_from_r1cs_triple(r1cs, instance, witness);
  assert!(pov.satisfy_gate_logics(&witness));
  assert!(pov.satisfy_wiring(&witness));
  assert!(witness.satisfy_instance(&instance));
}

#[test]
fn test_pov_from_r1cs() {
  run_pov_from_r1cs::<ark_bls12_381::Bls12_381>(5);
}

macro_rules! define_run_pov_mt {
  ($func_name:ident, $snark:ident) => {
    fn $func_name<E: PairingEngine<ScalarField = ark_bls12_381::Fr>>(
      scale: usize,
    ) -> Result<(), Error> {
      let c = MerkleTreeCircuit { height: scale };
      let cs = ArkR1CS::<E::ScalarField>::new_ref();
      c.generate_constraints(cs.clone()).unwrap();
      let cs = cs.into_inner().unwrap();
      let x = cs
        .instance_assignment
        .iter()
        .skip(1)
        .map(|x| *x)
        .collect::<Vec<E::ScalarField>>();
      let w = cs.witness_assignment.clone();
      let r1cs = R1CS::from(cs);
      let instance = R1CSInstance { instance: x };
      let witness = R1CSWitness { witness: w };

      println!("R1CS num rows: {}", r1cs.nrows);
      println!("R1CS num cols: {}", r1cs.ncols);
      println!(
        "R1CS non entries: {}, {}, {} (total {}, max {})",
        r1cs.arows.len(),
        r1cs.brows.len(),
        r1cs.crows.len(),
        r1cs.arows.len() + r1cs.brows.len() + r1cs.crows.len(),
        max!(r1cs.arows.len(), r1cs.brows.len(), r1cs.crows.len())
      );

      if r1cs.satisfy(&instance, &witness) {
        println!("R1CS satisfied!");
      } else {
        println!("R1CS unsatisfied!");
      }

      let mut circ = FanInTwoCircuit::from(r1cs.clone());
      let input = instance
        .instance
        .clone()
        .into_iter()
        .chain(witness.witness.clone().into_iter())
        .collect();
      circ.evaluate(&input).unwrap();
      let output = circ.get_output().unwrap();
      assert_eq!(output, vec![E::ScalarField::zero(); r1cs.nrows as usize]);

      let (pov, instance, witness) = pov_triple_from_r1cs_triple(r1cs, instance, witness);
      assert!(pov.satisfy_gate_logics(&witness));
      assert!(pov.satisfy_wiring(&witness));
      assert!(witness.satisfy_instance(&instance));
      println!("Number of addition gates: {}", circ.get_add_num());
      println!("Number of mul gates: {}", circ.get_mul_num());
      println!("Number of const gates: {}", circ.get_const_num());
      println!("Length of witness: {}", witness.witness.0.len());

      let max_degree = $snark::get_max_degree(pov.get_size());
      // Let the universal parameters take a larger size than expected
      let timer = start_timer!(|| "Universal setup");
      let universal_params: UniversalParams<E> = $snark::setup(max_degree + 10).unwrap();
      end_timer!(timer);
      // println!(
      // "Universal parameter size: {}",
      // universal_params.powers_of_g.len()
      // );
      let timer = start_timer!(|| "Indexing");
      let (pk, vk) = $snark::index(&universal_params, &pov).unwrap();
      end_timer!(timer);
      println!("Degree bound: {}", vk.degree_bound);
      println!("Max degree: {}", pk.max_degree);
      println!("Prover key sigma size: {}", pk.sigma_vec.len());
      println!("Prover key d size: {}", pk.d_vec.len());
      // println!("Degree bound: {}", vk.degree_bound);
      // println!("Max degree: {}", pk.max_degree);
      // println!("Prover key matrix size: {}", pk.cap_m_mat.0.len());
      // println!("Prover key u size: {}", pk.u_vec.len());
      // println!("Prover key v size: {}", pk.v_vec.len());
      // println!("Prover key w size: {}", pk.w_vec.len());
      //
      // println!("M A row indices: {:?}", pk.cap_m_mat.0);
      // println!("M A col indices: {:?}", pk.cap_m_mat.1);
      // println!("M A vals: {:?}", to_int!(pk.cap_m_mat.2));
      // let vksize = vk.size.clone();
      // println!("H: {}", vksize.nrows);
      // println!("K: {}", vksize.ncols);

      let timer = start_timer!(|| "Proving");
      let proof = $snark::prove(&pk, &instance, &witness)?;
      end_timer!(timer);
      let timer = start_timer!(|| "Verifying");
      let ret = $snark::verify(&vk, &instance, &proof);
      end_timer!(timer);
      println!(
        "Proof size: {}",
        proof.serialized_size(ark_serialize::Compress::No)
      );
      ret
    }
  };
}

define_run_pov_mt!(run_pov_mt, VOProofPOV);
define_run_pov_mt!(run_pov_pe_mt, VOProofPOVProverEfficient);

macro_rules! define_pov_mt_test_large_scale {
  ($func_name: ident, $exec_name: ident, $scale: literal) => {
    #[test]
    fn $func_name() {
      $exec_name::<ark_bls12_381::Bls12_381>($scale).unwrap();
    }
  };
}

define_pov_mt_test_large_scale!(test_pov_mt_8, run_pov_mt, 8);
define_pov_mt_test_large_scale!(test_pov_mt_16, run_pov_mt, 16);
define_pov_mt_test_large_scale!(test_pov_mt_32, run_pov_mt, 32);
define_pov_mt_test_large_scale!(test_pov_mt_64, run_pov_mt, 64);

define_pov_mt_test_large_scale!(test_pov_pe_mt_8, run_pov_pe_mt, 8);
define_pov_mt_test_large_scale!(test_pov_pe_mt_16, run_pov_pe_mt, 16);
define_pov_mt_test_large_scale!(test_pov_pe_mt_32, run_pov_pe_mt, 32);
define_pov_mt_test_large_scale!(test_pov_pe_mt_64, run_pov_pe_mt, 64);
