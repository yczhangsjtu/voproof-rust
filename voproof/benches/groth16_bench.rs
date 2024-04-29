#![feature(test)]
extern crate test;
use test::Bencher;

use ark_bls12_381::Bls12_381 as E;
use ark_bls12_381::Fr;
use ark_ec::PairingEngine;
use ark_ff::fields::{PrimeField, Field};
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
use blake2::Blake2s;
use voproof::tools::to_field;
use voproof::*;

#[derive(Copy)]
struct TestCircuit<F: PrimeField> {
  pub a: Option<F>,
  pub b: Option<F>,
  pub num_variables: usize,
  pub num_constraints: usize,
  pub num_public: usize,
}

impl<F: PrimeField> Clone for TestCircuit<F> {
  fn clone(&self) -> Self {
    TestCircuit {
      a: self.a.clone(),
      b: self.b.clone(),
      num_variables: self.num_variables.clone(),
      num_constraints: self.num_constraints.clone(),
      num_public: self.num_public.clone(),
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

    for _ in 0..(self.num_public - 3) {
      let v = cs.new_input_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
      cs.enforce_constraint(lc!() + a + b, lc!() + Variable::One, lc!() + v + b)?;
    }

    for _ in 0..(self.num_variables - self.num_public) {
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

fn computes_universal_parameter_and_circuit<E: PairingEngine>(
  scale: usize,
) -> (
  TestCircuit<E::Fr>,
  Vec::<E::Fr>,
) {
  let rng = &mut ark_std::test_rng();
  let num_public = 50;
  let c = TestCircuit::<E::Fr> {
    a: Some(to_field::<E::Fr>(3).pow(&[100])),
    b: Some(to_field::<E::Fr>(5).pow(&[50])),
    num_variables: scale,
    num_constraints: scale,
    num_public: num_public,
  };
  let mut x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  for _ in 0..num_public-3 {
    x.push(c.a.unwrap());
  }
  let w = vec![c.a.unwrap(); scale-num_public];

  let mut cs = ArkR1CS::<E::Fr>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  cs.inline_all_lcs();
  let matrices = cs.to_matrices().unwrap();
  let (m, n, s) = (
    matrices.num_constraints,
    matrices.num_instance_variables + matrices.num_witness_variables,
    max!(matrices.a_num_non_zero, matrices.b_num_non_zero, matrices.c_num_non_zero),
  );
  (
    c,
    x,
  )
}

#[bench]
fn bench_groth16_verifier_test_circuit_scale_1000(b: &mut Bencher) {
  let (c, x) = computes_universal_parameter_and_circuit::<E>(1000);
  let rng = &mut ark_std::test_rng();
  let params = generate_random_parameters::<E, _, _>(c, rng).unwrap();
  let pvk = prepare_verifying_key(&params.vk);
  let proof = create_random_proof(c, &params, rng).unwrap();
  b.iter(|| {
    assert!(verify_proof(&pvk, &proof, &x).unwrap());
  });
}

