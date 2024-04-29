#![feature(test)]
extern crate test;
use test::Bencher;

use ark_bls12_381::Bls12_381 as E;
use ark_bls12_381::Fr as F;
use ark_ec::pairing::Pairing as PairingEngine;
use ark_ff::fields::PrimeField;
use ark_relations::{
  lc,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};
use voproof::cs::{circuit::fan_in_two::FanInTwoCircuit, pov::*, r1cs::*, ConstraintSystem};
use voproof::error::Error;
use voproof::kzg::UniversalParams;
use voproof::snarks::{voproof_pov::*, voproof_pov_prover_efficient::*, SNARK};
use voproof::tools::{fmt_field, to_field, try_to_int};
use voproof::*;

macro_rules! define_bench_pov_verifier {
  ($func_name:ident, $snark:ident) => {
    #[bench]
    fn $func_name(bencher: &mut Bencher) {
      let mut circ = FanInTwoCircuit::<F>::new();
      let a = circ.add_global_input_variable().unwrap();
      let b = circ.add_global_input_variable().unwrap();
      let c = circ.add_global_input_variable().unwrap();
      let d = circ.add_vars(&a, &b);
      let e = circ.mul_vars(&b, &c);
      let f = circ.mul_vars(&d, &e);
      let g = circ.add_vars(&a, &d);
      let h = circ.mul_vars(&g, &f);
      let o = circ.const_var(to_field::<F>(10));
      let p = circ.mul_vars(&h, &o);
      circ.mark_as_complete().unwrap();
      circ.mark_variable_as_public(&a).unwrap();
      circ.mark_variable_as_public(&p).unwrap();
      circ
        .evaluate(&vec![to_field::<F>(1), to_field::<F>(2), to_field::<F>(3)])
        .unwrap();
      let ins = POVInstance {
        instance: circ.get_instance().unwrap(),
      };
      let mut wit = POVWitness {
        witness: circ.get_witness().unwrap(),
      };
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
      let (pk, vk) = $snark::index(&universal_params, &pov).unwrap();

      let mut proof = $snark::prove(&pk, &ins, &wit).unwrap();
      bencher.iter(|| {
        $snark::verify(&vk, &ins, &proof).unwrap();
      });
    }
  };
}

define_bench_pov_verifier!(bench_pov_verifier, VOProofPOV);
define_bench_pov_verifier!(bench_pov_pe_verifier, VOProofPOVProverEfficient);
