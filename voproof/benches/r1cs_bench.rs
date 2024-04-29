#![feature(test)]
extern crate test;
use test::Bencher;

use ark_bls12_381::Bls12_381 as E;
use ark_ec::PairingEngine;
use ark_ff::fields::PrimeField;
use ark_relations::{
  lc,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};
use voproof::cs::{
  r1cs::{R1CSInstance, R1CSWitness, R1CS},
  ConstraintSystem,
};
use voproof::kzg::UniversalParams;
use voproof::snarks::{voproof_r1cs::*, voproof_r1cs_prover_efficient::*, SNARK};
use voproof::tools::{to_field, to_int};
use voproof::*;

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

fn computes_max_degree<E: PairingEngine>(scale: usize) -> usize {
  let c = TestCircuit::<E::ScalarField> {
    a: Some(to_field::<E::ScalarField>(3)),
    b: Some(to_field::<E::ScalarField>(2)),
    num_variables: scale,
    num_constraints: scale,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  let w = vec![c.a.unwrap(); scale - 3];

  let cs = ArkR1CS::<E::ScalarField>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  let r1cs = R1CS::from(cs.into_inner().unwrap());

  VOProofR1CS::get_max_degree(r1cs.get_size())
}

fn computes_r1cs<E: PairingEngine>(
  scale: usize,
) -> (
  R1CS<E::ScalarField>,
  R1CSInstance<E::ScalarField>,
  R1CSWitness<E::ScalarField>,
) {
  let c = TestCircuit::<E::ScalarField> {
    a: Some(to_field::<E::ScalarField>(3)),
    b: Some(to_field::<E::ScalarField>(2)),
    num_variables: scale,
    num_constraints: scale,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  let w = vec![c.a.unwrap(); scale - 3];
  let instance = R1CSInstance { instance: x };
  let witness = R1CSWitness { witness: w };

  let cs = ArkR1CS::<E::ScalarField>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  (R1CS::from(cs.into_inner().unwrap()), instance, witness)
}

#[bench]
#[ignore]
fn bench_setup_test_circuit_scale_1000(b: &mut Bencher) {
  let max_degree = computes_max_degree::<E>(1000) + 10;
  // Let the universal parameters take a larger size than expected
  b.iter(|| {
    let _: UniversalParams<E> = VOProofR1CS::setup(max_degree).unwrap();
  });
}

#[bench]
#[ignore]
fn bench_setup_test_circuit_scale_2000(b: &mut Bencher) {
  let max_degree = computes_max_degree::<E>(2000) + 10;
  b.iter(|| {
    let _: UniversalParams<E> = VOProofR1CS::setup(max_degree).unwrap();
  });
}

#[bench]
fn bench_indexer_test_circuit_scale_1000(b: &mut Bencher) {
  let (r1cs, _, _) = computes_r1cs::<E>(1000);

  let max_degree = VOProofR1CS::get_max_degree(r1cs.get_size());
  let universal_params: UniversalParams<E> = VOProofR1CS::setup(max_degree).unwrap();
  b.iter(|| {
    VOProofR1CS::index(&universal_params, &r1cs).unwrap();
  });
}

#[bench]
fn bench_prover_test_circuit_scale_1000(b: &mut Bencher) {
  let (r1cs, instance, witness) = computes_r1cs::<E>(1000);

  let max_degree = VOProofR1CS::get_max_degree(r1cs.get_size());
  let universal_params: UniversalParams<E> = VOProofR1CS::setup(max_degree).unwrap();
  let (pk, vk) = VOProofR1CS::index(&universal_params, &r1cs).unwrap();
  b.iter(|| {
    VOProofR1CS::prove(&pk, &instance, &witness).unwrap();
  });
}

fn bench_prover_test_circuit_scale_4000(b: &mut Bencher) {
  let (r1cs, instance, witness) = computes_r1cs::<E>(4000);

  let max_degree = VOProofR1CS::get_max_degree(r1cs.get_size());
  let universal_params: UniversalParams<E> = VOProofR1CS::setup(max_degree).unwrap();
  let (pk, vk) = VOProofR1CS::index(&universal_params, &r1cs).unwrap();
  b.iter(|| {
    VOProofR1CS::prove(&pk, &instance, &witness).unwrap();
  });
}

#[bench]
fn bench_verifier_test_circuit_scale_1000(b: &mut Bencher) {
  let (r1cs, instance, witness) = computes_r1cs::<E>(1000);

  let max_degree = VOProofR1CS::get_max_degree(r1cs.get_size());
  let universal_params: UniversalParams<E> = VOProofR1CS::setup(max_degree).unwrap();
  let (pk, vk) = VOProofR1CS::index(&universal_params, &r1cs).unwrap();
  let proof = VOProofR1CS::prove(&pk, &instance, &witness).unwrap();
  b.iter(|| {
    VOProofR1CS::verify(&vk, &instance, &proof);
  });
}

#[bench]
fn bench_verifier_pe_test_circuit_scale_1000(b: &mut Bencher) {
  let (r1cs, instance, witness) = computes_r1cs::<E>(1000);

  let max_degree = VOProofR1CSProverEfficient::get_max_degree(r1cs.get_size());
  let universal_params: UniversalParams<E> = VOProofR1CSProverEfficient::setup(max_degree).unwrap();
  let (pk, vk) = VOProofR1CSProverEfficient::index(&universal_params, &r1cs).unwrap();
  let proof = VOProofR1CSProverEfficient::prove(&pk, &instance, &witness).unwrap();
  b.iter(|| {
    VOProofR1CSProverEfficient::verify(&vk, &instance, &proof);
  });
}
