use std::process::exit;

use ark_ec::pairing::Pairing as PairingEngine;
use ark_ff::fields::PrimeField;
use ark_relations::{
  lc,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};
use ark_std::{test_rng, One};
use cs::range::{RangeCheck, RangeCheckInstance, RangeCheckSize, RangeCheckWitness};
use snarks::range_check::VOProofRangeCheck;
use voproof::kzg::UniversalParams;
use voproof::snarks::{voproof_hpr::*, voproof_r1cs::*, SNARK};
use voproof::tools::{fmt_field, to_field, to_int};
use voproof::*;
use voproof::{cs::fibonacci::Fibonacci, error::Error};
use voproof::{
  cs::{
    fibonacci::{FibonacciInstance, FibonacciSize, FibonacciWitness},
    hpr::generate_random_hpr_instance,
    r1cs::{R1CSInstance, R1CSWitness, R1CS},
    ConstraintSystem,
  },
  snarks::fibonacci::VOProofFibonacci,
};
// use voproof::kzg::{KZG10, UniversalParams, Powers, VerifierKey, Randomness};

#[derive(Copy)]
struct TestCircuit<F: PrimeField> {
  pub a: Option<F>,
  pub b: Option<F>,
  pub num_variables: usize,
  pub num_constraints: usize,
}

impl<F: PrimeField> Clone for TestCircuit<F> {
  fn clone(&self) -> Self {
    TestCircuit {
      a: self.a.clone(),
      b: self.b.clone(),
      num_variables: self.num_variables.clone(),
      num_constraints: self.num_constraints.clone(),
    }
  }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit<F> {
  fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
    let a = cs.new_input_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
    let b = cs.new_input_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
    let c = cs.new_input_variable(|| {
      let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
      let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
      Ok(a * b)
    })?;

    for _ in 0..(self.num_variables - 3) {
      let v = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
      cs.enforce_constraint(lc!() + a + b, lc!() + Variable::One, lc!() + v + b)?;
    }

    for _ in 0..self.num_constraints - 1 {
      cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
    }

    cs.enforce_constraint(lc!(), lc!(), lc!())?;

    Ok(())
  }
}

fn run_fibonacci_example<E: PairingEngine>(n: usize) -> Result<(), Error> {
  let a = to_field::<E::ScalarField>(1);
  let b = a;
  let t = (0..n)
    .map(|i| to_field::<E::ScalarField>(i as u64))
    .collect::<Vec<_>>();
  let mut w = vec![a, b];
  for i in 0..n {
    w.push(w[w.len() - 2] + w[w.len() - 1] * t[i]);
    println!("{:?}", w.last().unwrap());
  }
  let c = *w.last().unwrap();

  let x = FibonacciInstance { a, b, c };
  let size = FibonacciSize { n };
  let w = FibonacciWitness {
    witness: w[2..].to_vec(),
  };
  println!("{:?}", w.witness);
  let cs = Fibonacci::<E::ScalarField>::new(n, t);
  let pp: UniversalParams<E> = VOProofFibonacci::setup(VOProofFibonacci::get_max_degree(size))?;
  let (pk, vk) = VOProofFibonacci::index(&pp, &cs)?;
  let proof = VOProofFibonacci::prove(&pk, &x, &w)?;
  VOProofFibonacci::verify(&vk, &x, &proof)
}

fn run_range_check_example<E: PairingEngine>(n: usize, range: usize) -> Result<(), Error> {
  let x = RangeCheckInstance::new();
  let size = RangeCheckSize {
    lookup_size: n,
    range,
  };
  let w = RangeCheckWitness {
    witness: (0..n)
      .map(|i| to_field::<E::ScalarField>(((range as f64) * (i as f64) / (n as f64)) as u64))
      .collect::<Vec<_>>(),
  };
  println!("{:?}", w.witness);
  let cs = RangeCheck::<E::ScalarField>::new(n, range);
  let pp: UniversalParams<E> = VOProofRangeCheck::setup(VOProofRangeCheck::get_max_degree(size))?;
  let (pk, vk) = VOProofRangeCheck::index(&pp, &cs)?;
  let proof = VOProofRangeCheck::prove(&pk, &x, &w)?;
  VOProofRangeCheck::verify(&vk, &x, &proof)
}

fn run_r1cs_example<E: PairingEngine>() -> Result<(), Error> {
  let c = TestCircuit::<E::ScalarField> {
    a: Some(to_field::<E::ScalarField>(3)),
    b: Some(to_field::<E::ScalarField>(2)),
    num_variables: 5,
    num_constraints: 5,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  let w = vec![c.a.unwrap(); 2];

  let cs = ArkR1CS::<E::ScalarField>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  let r1cs = R1CS::from(cs.into_inner().unwrap());
  println!("R1CS num rows: {}", r1cs.nrows);
  println!("R1CS num cols: {}", r1cs.ncols);
  println!("R1CS A row indices: {:?}", r1cs.arows);
  println!("R1CS A col indices: {:?}", r1cs.acols);
  println!("R1CS A vals: {:?}", to_int!(r1cs.avals));
  println!("R1CS B row indices: {:?}", r1cs.brows);
  println!("R1CS B col indices: {:?}", r1cs.bcols);
  println!("R1CS B vals: {:?}", to_int!(r1cs.bvals));
  println!("R1CS C row indices: {:?}", r1cs.crows);
  println!("R1CS C col indices: {:?}", r1cs.ccols);
  println!("R1CS C vals: {:?}", to_int!(r1cs.cvals));

  let instance = R1CSInstance { instance: x };
  let witness = R1CSWitness { witness: w };

  if r1cs.satisfy(&instance, &witness) {
    println!("R1CS satisfied!");
  } else {
    println!("R1CS unsatisfied!");
  }

  let max_degree = VOProofR1CS::get_max_degree(r1cs.get_size());
  // Let the universal parameters take a larger size than expected
  let universal_params: UniversalParams<E> = VOProofR1CS::setup(max_degree + 10).unwrap();
  println!(
    "Universal parameter size: {}",
    universal_params.powers_of_g.len()
  );
  let (pk, vk) = VOProofR1CS::index(&universal_params, &r1cs).unwrap();
  println!("Degree bound: {}", vk.degree_bound);
  println!("Max degree: {}", pk.max_degree);
  println!("Prover key matrix size: {}", pk.cap_m_mat.0.len());
  println!("Prover key u size: {}", pk.u_vec.len());
  println!("Prover key v size: {}", pk.v_vec.len());
  println!("Prover key w size: {}", pk.w_vec.len());

  println!("M A row indices: {:?}", pk.cap_m_mat.0);
  println!("M A col indices: {:?}", pk.cap_m_mat.1);
  println!("M A vals: {:?}", to_int!(pk.cap_m_mat.2));
  let vksize = vk.size.clone();
  println!("H: {}", vksize.nrows);
  println!("K: {}", vksize.ncols);

  let proof = VOProofR1CS::prove(&pk, &instance, &witness)?;
  VOProofR1CS::verify(&vk, &instance, &proof)
}

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
  VOProofHPR::verify(&vk, &instance, &proof)
}

fn main() {
  if let Err(err) = run_range_check_example::<ark_bls12_381::Bls12_381>(5, 10) {
    println!("{}", err);
    exit(-1);
  } else {
    println!("Verification pass");
  }

  if let Err(err) = run_fibonacci_example::<ark_bls12_381::Bls12_381>(5) {
    println!("{}", err);
    exit(-1);
  } else {
    println!("Verification pass");
  }

  if let Err(err) = run_hpr_example::<ark_bls12_381::Bls12_381>(5) {
    println!("{}", err);
  } else {
    println!("Verification pass");
  }

  if let Err(err) = run_r1cs_example::<ark_bls12_381::Bls12_381>() {
    println!("{}", err);
  } else {
    println!("Verification pass");
  }
}
