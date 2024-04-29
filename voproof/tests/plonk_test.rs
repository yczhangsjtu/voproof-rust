// use ark_bls12_381::{Bls12_381 as E, Fr as F};
// use ark_ec::{PairingEngine, TEModelParameters};
// use ark_ed_on_bls12_381::EdwardsParameters;
// use ark_poly::univariate::DensePolynomial;
// use ark_poly_commit::kzg10::KZG10;
// use ark_relations::{
//   lc, ns,
//   r1cs::{
//     ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
//     Variable,
//   },
// };
// use ark_serialize::CanonicalSerialize;
// use ark_std::{end_timer, start_timer, Zero};
// use core::marker::PhantomData;
// use plonk::prelude::*;
// use rand_core::OsRng;
// use voproof::cs::{circuit::fan_in_two::FanInTwoCircuit, pov::*, r1cs::*, ConstraintSystem};
// mod utils;
// use utils::mt_circuit::MerkleTreeCircuit;

// /// Benchmark Circuit
// #[derive(derivative::Derivative)]
// #[derivative(Debug, Default)]
// pub struct BenchCircuit<P>
// where
//   P: TEModelParameters<BaseField = F>,
// {
//   /// Number of nodes in the Merkle Path
//   pub size: usize,

//   /// Type Parameter Marker
//   __: PhantomData<(E, P)>,
// }

// impl<P> BenchCircuit<P>
// where
//   P: TEModelParameters<BaseField = F>,
// {
//   #[inline]
//   pub fn new(scale: usize) -> Self {
//     let c = MerkleTreeCircuit { height: scale };
//     let cs = ArkR1CS::<F>::new_ref();
//     c.generate_constraints(cs.clone()).unwrap();
//     let cs = cs.into_inner().unwrap();
//     let x = cs
//       .instance_assignment
//       .iter()
//       .skip(1)
//       .map(|x| *x)
//       .collect::<Vec<F>>();
//     let w = cs.witness_assignment.clone();
//     let r1cs = R1CS::from(cs);
//     let instance = R1CSInstance { instance: x };
//     let witness = R1CSWitness { witness: w };

//     if r1cs.satisfy(&instance, &witness) {
//       println!("R1CS satisfied!");
//     } else {
//       println!("R1CS unsatisfied!");
//     }

//     let mut circ = FanInTwoCircuit::from(r1cs.clone());
//     let input = instance
//       .instance
//       .clone()
//       .into_iter()
//       .chain(witness.witness.clone().into_iter())
//       .collect();
//     circ.evaluate(&input).unwrap();
//     let output = circ.get_output().unwrap();
//     assert_eq!(output, vec![F::zero(); r1cs.nrows as usize]);

//     let (pov, instance, witness) = pov_triple_from_r1cs_triple(r1cs, instance, witness);
//     assert!(pov.satisfy_gate_logics(&witness));
//     assert!(pov.satisfy_wiring(&witness));
//     assert!(witness.satisfy_instance(&instance));
//     println!("Number of addition gates: {}", circ.get_add_num());
//     println!("Number of mul gates: {}", circ.get_mul_num());
//     println!("Number of const gates: {}", circ.get_const_num());

//     Self {
//       size: circ.get_add_num() + circ.get_mul_num(),
//       __: PhantomData,
//     }
//   }
// }

// fn pad_to_power_of_two(a: usize) -> usize {
//   let mut ret = 1;
//   while ret < a {
//     ret *= 2;
//   }
//   ret
// }

// impl<P> Circuit<E, P> for BenchCircuit<P>
// where
//   P: TEModelParameters<BaseField = F>,
// {
//   const CIRCUIT_ID: [u8; 32] = [0xff; 32];

//   #[inline]
//   fn gadget(&mut self, composer: &mut StandardComposer<E, P>) -> Result<(), Error> {
//     while composer.circuit_size() < self.size - 1 {
//       composer.add_dummy_constraints();
//     }
//     Ok(())
//   }

//   #[inline]
//   fn padded_circuit_size(&self) -> usize {
//     pad_to_power_of_two(self.size)
//   }
// }

// /// Generates full benchmark suite for compiling, proving, and verifying.
// fn constraint_system_benchmark(scale: usize) {
//   let label = b"ark".as_slice();

//   let mut circuit = BenchCircuit::<EdwardsParameters>::new(scale);
//   println!("Circuit size: {}", circuit.size);

//   let timer = start_timer!(|| "Universal setup");
//   let pp = KZG10::<E, DensePolynomial<F>>::setup(
//     // +1 per wire, +2 for the permutation poly
//     circuit.padded_circuit_size() + 6,
//     false,
//     &mut OsRng,
//   )
//   .expect("Unable to sample public parameters.");
//   end_timer!(timer);
//   println!("Powers: {}", pp.powers_of_g.len());

//   let timer = start_timer!(|| "Indexing");
//   let (pk_p, verifier_data) = circuit.compile(&pp).expect("Unable to compile circuit.");
//   end_timer!(timer);

//   let timer = start_timer!(|| "Proving");
//   let proof = circuit.gen_proof(&pp, pk_p.clone(), &label).unwrap();
//   end_timer!(timer);
//   println!("Proof size: {}", proof.serialized_size());

//   let VerifierData { key, pi_pos } = verifier_data;

//   let timer = start_timer!(|| "Verifying");
//   plonk::circuit::verify_proof(&pp, key.clone(), &proof, &[], &pi_pos, &label)
//     .expect("Unable to verify benchmark circuit.");
//   end_timer!(timer);
// }

// macro_rules! define_test_plonk_mt {
//   ($func_name:ident, $scale:expr) => {
//     #[test]
//     fn $func_name() {
//       constraint_system_benchmark($scale);
//     }
//   };
// }

// define_test_plonk_mt!(test_plonk_mt_8, 8);
// define_test_plonk_mt!(test_plonk_mt_16, 16);
// define_test_plonk_mt!(test_plonk_mt_32, 32);
// define_test_plonk_mt!(test_plonk_mt_64, 64);
