use ark_ec::PairingEngine;
use ark_ff::{
  fields::{FftField, Field, FpParameters, PrimeField},
  to_bytes, Fp256,
};
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, uint64::UInt64, R1CSVar};
use ark_relations::{
  lc, ns,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};
use ark_serialize::CanonicalSerialize;
use ark_std::{end_timer, start_timer};
use voproof::cs::{
  r1cs::{R1CSInstance, R1CSWitness, R1CS},
  ConstraintSystem,
};
use voproof::error::Error;
use voproof::kzg::UniversalParams;
use voproof::snarks::{voproof_r1cs::*, voproof_r1cs_prover_efficient::*, SNARK};
use voproof::{generator_of, max};

mod utils;
use utils::mt_circuit::MerkleTreeCircuit;
use utils::test_circuit::TestCircuit;
// use voproof::kzg::{KZG10, UniversalParams, Powers, VerifierKey, Randomness};
//

fn run_r1cs_example<E: PairingEngine>(scale: usize) -> Result<(), Error> {
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
  // println!("R1CS A row indices: {:?}", r1cs.arows);
  // println!("R1CS A col indices: {:?}", r1cs.acols);
  // println!("R1CS A vals: {:?}", to_int!(r1cs.avals));
  // println!("R1CS B row indices: {:?}", r1cs.brows);
  // println!("R1CS B col indices: {:?}", r1cs.bcols);
  // println!("R1CS B vals: {:?}", to_int!(r1cs.bvals));
  // println!("R1CS C row indices: {:?}", r1cs.crows);
  // println!("R1CS C col indices: {:?}", r1cs.ccols);
  // println!("R1CS C vals: {:?}", to_int!(r1cs.cvals));

  let instance = R1CSInstance { instance: x };
  let witness = R1CSWitness { witness: w };

  if r1cs.satisfy(&instance, &witness) {
    println!("R1CS satisfied!");
  } else {
    println!("R1CS unsatisfied!");
  }

  let max_degree = VOProofR1CS::get_max_degree(r1cs.get_size());
  // Let the universal parameters take a larger size than expected
  let timer = start_timer!(|| "Universal setup");
  let universal_params: UniversalParams<E> = VOProofR1CS::setup(max_degree + 10).unwrap();
  end_timer!(timer);
  // println!(
  // "Universal parameter size: {}",
  // universal_params.powers_of_g.len()
  // );
  let timer = start_timer!(|| "Indexing");
  let (pk, vk) = VOProofR1CS::index(&universal_params, &r1cs).unwrap();
  end_timer!(timer);
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
  let proof = VOProofR1CS::prove(&pk, &instance, &witness)?;
  end_timer!(timer);
  let timer = start_timer!(|| "Verifying");
  let ret = VOProofR1CS::verify(&vk, &instance, &proof);
  end_timer!(timer);
  ret
}

fn run_r1cs_pe_example<E: PairingEngine>(scale: usize) -> Result<(), Error> {
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
  // println!("R1CS A row indices: {:?}", r1cs.arows);
  // println!("R1CS A col indices: {:?}", r1cs.acols);
  // println!("R1CS A vals: {:?}", to_int!(r1cs.avals));
  // println!("R1CS B row indices: {:?}", r1cs.brows);
  // println!("R1CS B col indices: {:?}", r1cs.bcols);
  // println!("R1CS B vals: {:?}", to_int!(r1cs.bvals));
  // println!("R1CS C row indices: {:?}", r1cs.crows);
  // println!("R1CS C col indices: {:?}", r1cs.ccols);
  // println!("R1CS C vals: {:?}", to_int!(r1cs.cvals));

  let instance = R1CSInstance { instance: x };
  let witness = R1CSWitness { witness: w };

  if r1cs.satisfy(&instance, &witness) {
    println!("R1CS satisfied!");
  } else {
    println!("R1CS unsatisfied!");
  }

  let max_degree = VOProofR1CSProverEfficient::get_max_degree(r1cs.get_size());
  // Let the universal parameters take a larger size than expected
  let timer = start_timer!(|| "Universal setup");
  let universal_params: UniversalParams<E> =
    VOProofR1CSProverEfficient::setup(max_degree + 10).unwrap();
  end_timer!(timer);
  // println!(
  // "Universal parameter size: {}",
  // universal_params.powers_of_g.len()
  // );
  let timer = start_timer!(|| "Indexing");
  let (pk, vk) = VOProofR1CSProverEfficient::index(&universal_params, &r1cs).unwrap();
  end_timer!(timer);
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
  let proof = VOProofR1CSProverEfficient::prove(&pk, &instance, &witness)?;
  end_timer!(timer);
  let timer = start_timer!(|| "Verifying");
  let ret = VOProofR1CSProverEfficient::verify(&vk, &instance, &proof);
  end_timer!(timer);
  ret
}

macro_rules! define_test_small_scale {
  ($func_name:ident, $exec_name:ident) => {
    #[test]
    fn $func_name() {
      let result = $exec_name::<ark_bls12_381::Bls12_381>(5);
      if !result.is_ok() {
        if let Err(Error::VectorNotEqual(info)) = result {
          println!("{}", info);
        } else {
          println!("{:?}", result);
        }
        assert!(false);
      }
      $exec_name::<ark_bls12_381::Bls12_381>(10).unwrap();
      $exec_name::<ark_bls12_381::Bls12_381>(15).unwrap();
      $exec_name::<ark_bls12_381::Bls12_381>(20).unwrap();
    }
  };
}

define_test_small_scale!(test_simple_r1cs_small_scales, run_r1cs_example);
define_test_small_scale!(test_simple_r1cs_pe_small_scales, run_r1cs_pe_example);

macro_rules! define_test_large_scale {
  ($func_name: ident, $exec_name: ident, $scale: literal) => {
    #[test]
    fn $func_name() {
      assert!($exec_name::<ark_bls12_381::Bls12_381>($scale).is_ok());
    }
  };
}

define_test_large_scale!(test_simple_r1cs_large_scale_1000, run_r1cs_example, 1000);
define_test_large_scale!(test_simple_r1cs_large_scale_2000, run_r1cs_example, 2000);
define_test_large_scale!(test_simple_r1cs_large_scale_4000, run_r1cs_example, 4000);
define_test_large_scale!(test_simple_r1cs_large_scale_8000, run_r1cs_example, 8000);
define_test_large_scale!(test_simple_r1cs_large_scale_16000, run_r1cs_example, 16000);
define_test_large_scale!(test_simple_r1cs_large_scale_32000, run_r1cs_example, 32000);
define_test_large_scale!(test_simple_r1cs_large_scale_64000, run_r1cs_example, 64000);
define_test_large_scale!(
  test_simple_r1cs_large_scale_128000,
  run_r1cs_example,
  128000
);
define_test_large_scale!(
  test_simple_r1cs_large_scale_256000,
  run_r1cs_example,
  256000
);
define_test_large_scale!(
  test_simple_r1cs_large_scale_512000,
  run_r1cs_example,
  512000
);
define_test_large_scale!(
  test_simple_r1cs_large_scale_1024000,
  run_r1cs_example,
  1024000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_1000,
  run_r1cs_pe_example,
  1000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_2000,
  run_r1cs_pe_example,
  2000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_4000,
  run_r1cs_pe_example,
  4000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_8000,
  run_r1cs_pe_example,
  8000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_16000,
  run_r1cs_pe_example,
  16000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_32000,
  run_r1cs_pe_example,
  32000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_64000,
  run_r1cs_pe_example,
  64000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_128000,
  run_r1cs_pe_example,
  128000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_256000,
  run_r1cs_pe_example,
  256000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_512000,
  run_r1cs_pe_example,
  512000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_1024000,
  run_r1cs_pe_example,
  1024000
);

macro_rules! define_run_r1cs_mt_example {
  ($func_name:ident, $snark: ident) => {
    fn $func_name<E: PairingEngine<Fr = Fp256<ark_bls12_381::FrParameters>>>(
      height: u32,
    ) -> Result<(), Error> {
      let c = MerkleTreeCircuit {
        height: height as usize,
      };
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
      println!("R1CS num rows: {}", r1cs.nrows);
      println!("R1CS num cols: {}", r1cs.ncols);
      println!("R1CS num inputs: {}", r1cs.input_size);
      println!("Instance size: {}", x.len());
      println!("Witness size: {}", w.len());
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

      let max_degree = $snark::get_max_degree(r1cs.get_size());
      // Let the universal parameters take a larger size than expected
      let timer = start_timer!(|| "Universal setup");
      let universal_params: UniversalParams<E> = $snark::setup(max_degree + 10).unwrap();
      end_timer!(timer);
      // println!(
      // "Universal parameter size: {}",
      // universal_params.powers_of_g.len()
      // );
      let timer = start_timer!(|| "Indexing");
      let (pk, vk) = $snark::index(&universal_params, &r1cs).unwrap();
      end_timer!(timer);
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
      println!("Proof size: {}", proof.serialized_size());
      ret
    }
  };
}

define_run_r1cs_mt_example!(run_r1cs_mt_example, VOProofR1CS);
define_run_r1cs_mt_example!(run_r1cs_pe_mt_example, VOProofR1CSProverEfficient);

macro_rules! define_mt_test_large_scale {
  ($func_name: ident, $exec_name: ident, $scale: literal) => {
    #[test]
    fn $func_name() {
      $exec_name::<ark_bls12_381::Bls12_381>($scale).unwrap();
    }
  };
}

define_mt_test_large_scale!(test_r1cs_pe_mt_8, run_r1cs_pe_mt_example, 8);
define_mt_test_large_scale!(test_r1cs_pe_mt_16, run_r1cs_pe_mt_example, 16);
define_mt_test_large_scale!(test_r1cs_pe_mt_32, run_r1cs_pe_mt_example, 32);
define_mt_test_large_scale!(test_r1cs_pe_mt_64, run_r1cs_pe_mt_example, 64);
define_mt_test_large_scale!(test_r1cs_mt_8, run_r1cs_mt_example, 8);
define_mt_test_large_scale!(test_r1cs_mt_16, run_r1cs_mt_example, 16);
define_mt_test_large_scale!(test_r1cs_mt_32, run_r1cs_mt_example, 32);
define_mt_test_large_scale!(test_r1cs_mt_64, run_r1cs_mt_example, 64);
