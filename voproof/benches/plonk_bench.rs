// #![feature(test)]
// extern crate test;
// use test::Bencher;

// use ark_ff::PrimeField;
// use ark_bls12_381::{Bls12_381 as E, Fr as F};
// use ark_ec::{PairingEngine, TEModelParameters};
// use ark_ed_on_bls12_381::EdwardsParameters;
// use ark_poly::univariate::DensePolynomial;
// use ark_poly_commit::kzg10::KZG10;
// use ark_poly_commit::kzg10;
// use ark_poly_commit::PolynomialCommitment;
// use ark_poly_commit::sonic_pc::SonicKZG10;
// use ark_serialize::CanonicalSerialize;
// use ark_std::{end_timer, start_timer, Zero};
// use core::marker::PhantomData;
// use plonk::prelude::*;
// use plonk::proof_system::verifier::Verifier;
// use plonk::circuit::PublicInputValue;
// use rand_core::OsRng;

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
//     Self {
//       size: scale * 1000,
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

// macro_rules! define_bench_plonk_verifier {
//   ($func_name:ident, $scale:expr) => {
//     #[bench]
//     fn $func_name(bencher: &mut Bencher) {
//       let label = b"ark".as_slice();

//       let mut circuit = BenchCircuit::<EdwardsParameters>::new($scale);

//       let pp = KZG10::<E, DensePolynomial<F>>::setup(
//         // +1 per wire, +2 for the permutation poly
//         circuit.padded_circuit_size() + 6,
//         false,
//         &mut OsRng,
//       )
//       .expect("Unable to sample public parameters.");

//       let (pk_p, verifier_data) = circuit.compile(&pp).expect("Unable to compile circuit.");

//       let proof = circuit.gen_proof(&pp, pk_p.clone(), &label).unwrap();
// //
//       let VerifierData { key, pi_pos } = verifier_data;
//       let mut verifier: Verifier<E, EdwardsParameters> = Verifier::new(&label);
//       let padded_circuit_size = key.padded_circuit_size();
//       verifier.verifier_key = Some(key);
//       let (_, sonic_vk) = SonicKZG10::<E, DensePolynomial<F>>::trim(
//           &pp,
//           padded_circuit_size + 6,
//           0,
//           None,
//       )
//       .unwrap();

//       let vk = kzg10::VerifierKey {
//           g: sonic_vk.g,
//           gamma_g: sonic_vk.gamma_g,
//           h: sonic_vk.h,
//           beta_h: sonic_vk.beta_h,
//           prepared_h: sonic_vk.prepared_h,
//           prepared_beta_h: sonic_vk.prepared_beta_h,
//       };

//       let pi = build_pi::<_, EdwardsParameters>(&[], &pi_pos, padded_circuit_size);
// //
//       bencher.iter(|| {
//         // plonk::circuit::verify_proof(&pp, key.clone(), &proof, &[], &pi_pos, &label)
//           // .expect("Unable to verify benchmark circuit.");
//         verifier.verify(
//             &proof,
//             &vk,
//             pi.as_slice()
//         ).unwrap()
//       });
//     }
//   };
// }

// /// Build PI vector for Proof verifications.
// fn build_pi<F, P>(
//     pub_input_values: &[PublicInputValue<P>],
//     pub_input_pos: &[usize],
//     trim_size: usize,
// ) -> Vec<F>
// where
//     F: PrimeField,
//     P: TEModelParameters<BaseField = F>,
// {
//     let mut pi = vec![F::zero(); trim_size];
//     // pub_input_values
//         // .iter()
//         // .flat_map(|pub_input| pub_input.values.clone())
//         // .zip(pub_input_pos.iter().copied())
//         // .for_each(|(value, pos)| {
//             // pi[pos] = -value;
//         // });
//     pi
// }

// define_bench_plonk_verifier!(bench_plonk_verifier_8, 8);
// define_bench_plonk_verifier!(bench_plonk_verifier_16, 16);
// define_bench_plonk_verifier!(bench_plonk_verifier_32, 32);
// define_bench_plonk_verifier!(bench_plonk_verifier_64, 64);
