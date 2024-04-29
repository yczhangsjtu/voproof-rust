//! This is a fork of the KZG implementation of ark_poly_commit.
//! The original implementation does not suit our need. Specifically,
//! the original implementation adds the powers_of_gamma_g to the
//! universal parameter, which is not needed by us. And the `open`
//! method was not public. Finally, the batched check is not the same
//! as that of PLONK.

use ark_ec::scalar_mul::{fixed_base::FixedBase as FixedBaseMSM, variable_base::VariableBaseMSM};
use ark_ec::{
  pairing::Pairing as PairingEngine, AffineRepr as AffineCurve, CurveGroup as ProjectiveCurve,
};
use ark_ff::{One, PrimeField, UniformRand, Zero};
use ark_poly::DenseUVPolynomial as UVPolynomial;
use ark_poly_commit::LabeledPolynomial;
use ark_std::{format, marker::PhantomData, ops::Div};

use ark_std::ops::Mul;
use ark_std::rand::RngCore;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

mod data_structures;
use crate::error::Error;
pub use data_structures::*;

/// `KZG10` is an implementation of the polynomial commitment scheme of
/// [Kate, Zaverucha and Goldbgerg][kzg10]
///
/// [kzg10]: http://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf
pub struct KZG10<E: PairingEngine, P: UVPolynomial<E::ScalarField>> {
  _engine: PhantomData<E>,
  _poly: PhantomData<P>,
}

impl<E, P> KZG10<E, P>
where
  E: PairingEngine,
  P: UVPolynomial<E::ScalarField, Point = E::ScalarField>,
  for<'a, 'b> &'a P: Div<&'b P, Output = P> + Mul<E::ScalarField, Output = P>,
{
  /// Constructs public parameters when given as input the maximum degree `degree`
  /// for the polynomial commitment scheme.
  pub fn setup<R: RngCore>(max_degree: usize, rng: &mut R) -> Result<UniversalParams<E>, Error> {
    if max_degree < 1 {
      return Err(Error::DegreeIsZero);
    }
    let setup_time = start_timer!(|| format!("KZG10::Setup with degree {}", max_degree));
    let beta = E::ScalarField::rand(rng);
    let g = E::G1::rand(rng);
    // let gamma_g = E::G1Projective::rand(rng);
    let h = E::G2::rand(rng);

    let mut powers_of_beta = vec![E::ScalarField::one()];

    let mut cur = beta;
    for _ in 0..max_degree {
      powers_of_beta.push(cur);
      cur *= &beta;
    }

    let window_size = FixedBaseMSM::get_mul_window_size(max_degree + 1);

    let scalar_bits = E::ScalarField::MODULUS_BIT_SIZE;
    let g_time = start_timer!(|| "Generating powers of G");
    let g_table = FixedBaseMSM::get_window_table(scalar_bits as usize, window_size, g);
    let powers_of_g =
      FixedBaseMSM::msm::<E::G1>(scalar_bits as usize, window_size, &g_table, &powers_of_beta);
    end_timer!(g_time);
    let powers_of_g = E::G1::normalize_batch(&powers_of_g);
    let h = h.into_affine();
    let beta_h = h.mul(beta).into_affine();
    let prepared_h = h.into();
    let prepared_beta_h = beta_h.into();

    let pp = UniversalParams {
      powers_of_g,
      h,
      beta_h,
      prepared_h,
      prepared_beta_h,
    };
    end_timer!(setup_time);
    Ok(pp)
  }

  /// Outputs a commitment to `polynomial`.
  pub fn commit_with_coefficients(
    powers: &[E::G1Affine],
    coeffs: &Vec<E::ScalarField>,
  ) -> Result<Commitment<E>, Error> {
    Self::check_degree_is_too_large(coeffs.len() - 1, powers.len())?;

    let commit_time = start_timer!(|| format!(
      // "Committing to polynomial of degree {} with hiding_bound: {:?}",
      "Committing to polynomial of degree {}",
      coeffs.len() - 1,
      // hiding_bound,
    ));

    let (num_leading_zeros, plain_coeffs) = skip_leading_zeros_and_convert_to_bigints_vec(coeffs);

    let msm_time = start_timer!(|| "MSM to compute commitment to plaintext poly");
    let commitment =
      <E::G1 as VariableBaseMSM>::msm_bigint(&powers[num_leading_zeros..], plain_coeffs.as_slice());
    end_timer!(msm_time);
    end_timer!(commit_time);

    Ok(Commitment(commitment.into()))
  }

  /// Outputs a commitment to `polynomial`.
  pub fn commit(powers: &Vec<E::G1Affine>, polynomial: &P) -> Result<Commitment<E>, Error> {
    Self::check_degree_is_too_large(polynomial.degree(), powers.len())?;

    let commit_time = start_timer!(|| format!(
      // "Committing to polynomial of degree {} with hiding_bound: {:?}",
      "Committing to polynomial of degree {}",
      polynomial.degree(),
      // hiding_bound,
    ));

    let (num_leading_zeros, plain_coeffs) = skip_leading_zeros_and_convert_to_bigints(polynomial);

    let msm_time = start_timer!(|| "MSM to compute commitment to plaintext poly");
    let commitment =
      <E::G1 as VariableBaseMSM>::msm_bigint(&powers[num_leading_zeros..], plain_coeffs.as_slice());
    end_timer!(msm_time);
    end_timer!(commit_time);

    Ok(Commitment(commitment.into()))
  }

  pub fn commit_single(g: &E::G1Affine, c: &E::ScalarField) -> Result<Commitment<E>, Error> {
    Ok(Commitment(g.into_group().mul(c).into()))
  }

  /// Compute witness polynomial.
  ///
  /// The witness polynomial w(x) the quotient of the division (p(x) - p(z)) / (x - z)
  /// Observe that this quotient does not change with z because
  /// p(z) is the remainder term. We can therefore omit p(z) when computing the quotient.
  pub fn compute_witness_polynomial(
    p: &P,
    point: &P::Point,
    // randomness: &Randomness<E::ScalarField, P>,
    // ) -> Result<(P, Option<P>), Error> {
  ) -> Result<P, Error> {
    // let witness_polynomial = p / &divisor;
    let mut witness_vector = vec![E::ScalarField::zero(); p.degree()];
    let witness_time =
      start_timer!(|| format!("Computing witness polynomial of degree {}", p.degree()));
    witness_vector[p.degree() - 1] = p.coeffs()[p.degree()];
    for i in (0..witness_vector.len() - 1).rev() {
      witness_vector[i] = p.coeffs()[i + 1] + witness_vector[i + 1] * point;
    }
    end_timer!(witness_time);
    let witness_polynomial = P::from_coefficients_vec(witness_vector);

    // Ok((witness_polynomial, random_witness_polynomial))
    Ok(witness_polynomial)
  }

  pub(crate) fn open_with_witness_polynomial<'a>(
    powers: &Vec<E::G1Affine>,
    // point: P::Point,
    witness_polynomial: &P,
  ) -> Result<Proof<E>, Error> {
    Self::check_degree_is_too_large(witness_polynomial.degree(), powers.len())?;
    let (num_leading_zeros, witness_coeffs) =
      skip_leading_zeros_and_convert_to_bigints(witness_polynomial);

    let witness_comm_time = start_timer!(|| format!(
      "Computing commitment to witness polynomial of degree {}",
      witness_polynomial.degree()
    ));
    let msm_time = start_timer!(|| "MSM to compute commitment to plaintext poly");
    let w = <E::G1 as VariableBaseMSM>::msm_bigint(
      &powers[num_leading_zeros..],
      witness_coeffs.as_slice(),
    );
    end_timer!(msm_time);
    end_timer!(witness_comm_time);

    Ok(Proof { w: w.into_affine() })
  }

  /// On input a polynomial `p` and a point `point`, outputs a proof for the same.
  pub fn open<'a>(powers: &Vec<E::G1Affine>, p: &P, point: &P::Point) -> Result<Proof<E>, Error> {
    Self::check_degree_is_too_large(p.degree(), powers.len())?;
    let open_time = start_timer!(|| format!("Opening polynomial of degree {}", p.degree()));

    let witness_time = start_timer!(|| "Computing witness polynomial");
    let witness_poly = Self::compute_witness_polynomial(p, &point)?;
    end_timer!(witness_time);

    let proof = Self::open_with_witness_polynomial(
      powers,
      // point,
      // rand,
      &witness_poly,
      // hiding_witness_poly.as_ref(),
    );

    end_timer!(open_time);
    proof
  }

  /// On input two list of polynomials `{f1, ..., fm}, {g1, ..., gn}`
  /// two points z, zz, outputs one proof respectively for fi(z) and gi(zz)
  pub(crate) fn batch_open<'a>(
    powers: &Vec<E::G1Affine>,
    fs: &[P],
    gs: &[P],
    z: &P::Point,
    zz: &P::Point,
    rand_xi: &E::ScalarField,
    rand_xi_2: &E::ScalarField,
    // rand: &Randomness<E::ScalarField, P>,
  ) -> Result<(Proof<E>, Proof<E>), Error> {
    for f in fs.iter().chain(gs.iter()) {
      Self::check_degree_is_too_large(f.degree(), powers.len())?;
    }
    let open_time = start_timer!(|| format!("Opening polynomials"));

    let witness_time = start_timer!(|| "Computing witness polynomial");
    let mut witness_poly_f = P::zero();
    let mut xi_power = E::ScalarField::one();
    let mut witness_poly_g = P::zero();
    let mut xi_power_2 = E::ScalarField::one();
    for f in fs.iter() {
      witness_poly_f += &Self::compute_witness_polynomial(f, z)?.mul(xi_power);
      xi_power *= rand_xi;
    }
    for g in gs.iter() {
      witness_poly_g += &Self::compute_witness_polynomial(g, zz)?.mul(xi_power_2);
      xi_power_2 *= rand_xi_2;
    }
    end_timer!(witness_time);

    let proof = Self::open_with_witness_polynomial(
      powers,
      // z,
      // rand,
      &witness_poly_f,
      // hiding_witness_poly.as_ref(),
    )?;

    let proof_2 = Self::open_with_witness_polynomial(
      powers,
      // zz,
      // rand,
      &witness_poly_g,
      // hiding_witness_poly.as_ref(),
    )?;

    end_timer!(open_time);
    Ok((proof, proof_2))
  }

  /// Verifies that `value` is the evaluation at `point` of the polynomial
  /// committed inside `comm`.
  pub fn check(
    vk: &VerifierKey<E>,
    comm: &Commitment<E>,
    point: &E::ScalarField,
    value: &E::ScalarField,
    proof: &Proof<E>,
  ) -> Result<bool, Error> {
    let check_time = start_timer!(|| "Checking evaluation");
    let inner = comm.0.into_group() - &vk.g.mul(value);
    // left hand side = e(C - y G, H) = (f(x) - y) e(G, H)
    let timer = start_timer!(|| "Pairing");
    let lhs = E::pairing(inner, vk.h);
    end_timer!(timer);

    let inner = vk.beta_h.into_group() - &vk.h.mul(point);
    // right hand side = e(W, (x - z) H) = w (x - z) e(G, H)
    let timer = start_timer!(|| "Pairing");
    let rhs = E::pairing(proof.w, inner);
    end_timer!(timer);

    end_timer!(check_time, || format!("Result: {}", lhs == rhs));
    // f(x) - y = w (x - z) => w = (f(x) - y) / (x - z)
    Ok(lhs == rhs)
  }

  /// Check that each `proof_i` in `proofs` is a valid proof of evaluation for
  /// `commitment_i` at `point_i`.
  pub fn batch_check<R: RngCore>(
    vk: &VerifierKey<E>,
    f_commitments: &[Commitment<E>],
    g_commitments: &[Commitment<E>],
    z: &E::ScalarField,
    zz: &E::ScalarField,
    rand_xi: &E::ScalarField,
    rand_xi_2: &E::ScalarField,
    f_values: &[E::ScalarField],
    g_values: &[E::ScalarField],
    proof: &Proof<E>,
    proof_2: &Proof<E>,
    rng: &mut R,
  ) -> Result<bool, Error> {
    let check_time = start_timer!(|| format!(
      "Checking {} evaluation proofs",
      f_commitments.len() + g_commitments.len()
    ));

    let mut total_q = <E::G1>::zero();
    let mut total_q_2 = <E::G1>::zero();

    let combination_time = start_timer!(|| "Combining commitments and proofs");
    // We don't need to sample randomizers from the full field,
    // only from 128-bit strings.
    let randomizer: E::ScalarField = u128::rand(rng).into();
    let mut y = E::ScalarField::zero();
    let mut y_2 = E::ScalarField::zero();
    let mut xi_power = E::ScalarField::one();
    let mut xi_power_2 = E::ScalarField::one();

    for (c, v) in f_commitments.iter().zip(f_values) {
      total_q += &c.0.mul(xi_power);
      y += &(xi_power * v);
      xi_power *= rand_xi;
    }
    total_q -= &vk.g.mul(y);

    for (c, v) in g_commitments.iter().zip(g_values) {
      total_q_2 += &c.0.mul(xi_power_2 * randomizer);
      y_2 += &(xi_power_2 * v);
      xi_power_2 *= rand_xi_2;
    }
    total_q_2 -= &vk.g.mul(y_2 * randomizer);

    let point_f = total_q + &total_q_2 + &proof.w.mul(z) + &proof_2.w.mul(randomizer * zz);
    let point_f = point_f.into_affine();
    let total_w = proof.w + proof_2.w.mul(randomizer).into_affine();
    end_timer!(combination_time);

    let pairing_time = start_timer!(|| "Performing product of pairings");

    let result = E::multi_pairing(
      [point_f.into(), (-total_w).into()],
      [vk.prepared_h.clone(), vk.prepared_beta_h.clone()],
    )
    .0
    .is_one();

    end_timer!(pairing_time);
    end_timer!(check_time, || format!("Result: {}", result));
    Ok(result)
  }

  pub(crate) fn check_degree_is_too_large(degree: usize, num_powers: usize) -> Result<(), Error> {
    let num_coefficients = degree + 1;
    if num_coefficients > num_powers {
      Err(Error::TooManyCoefficients {
        num_coefficients,
        num_powers,
      })
    } else {
      Ok(())
    }
  }

  /*
  pub(crate) fn check_hiding_bound(
      hiding_poly_degree: usize,
      num_powers: usize,
  ) -> Result<(), Error> {
      if hiding_poly_degree == 0 {
          Err(Error::HidingBoundIsZero)
      } else if hiding_poly_degree >= num_powers {
          // The above check uses `>=` because committing to a hiding poly with
          // degree `hiding_poly_degree` requires `hiding_poly_degree + 1`
          // powers.
          Err(Error::HidingBoundToolarge {
              hiding_poly_degree,
              num_powers,
          })
      } else {
          Ok(())
      }
  }
  */

  pub fn check_degrees_and_bounds<'a>(
    supported_degree: usize,
    max_degree: usize,
    enforced_degree_bounds: Option<&[usize]>,
    p: &'a LabeledPolynomial<E::ScalarField, P>,
  ) -> Result<(), Error> {
    if let Some(bound) = p.degree_bound() {
      let enforced_degree_bounds =
        enforced_degree_bounds.ok_or(Error::UnsupportedDegreeBound(bound))?;

      if enforced_degree_bounds.binary_search(&bound).is_err() {
        Err(Error::UnsupportedDegreeBound(bound))
      } else if bound < p.degree() || bound > max_degree {
        return Err(Error::IncorrectDegreeBound {
          poly_degree: p.degree(),
          degree_bound: p.degree_bound().unwrap(),
          supported_degree,
          label: p.label().to_string(),
        });
      } else {
        Ok(())
      }
    } else {
      Ok(())
    }
  }
}

fn skip_leading_zeros_and_convert_to_bigints_vec<F: PrimeField>(
  coeffs: &Vec<F>,
) -> (usize, Vec<F::BigInt>) {
  let mut num_leading_zeros = 0;
  while num_leading_zeros < coeffs.len() && coeffs[num_leading_zeros].is_zero() {
    num_leading_zeros += 1;
  }
  let coeffs = convert_to_bigints(&coeffs[num_leading_zeros..]);
  (num_leading_zeros, coeffs)
}

fn skip_leading_zeros_and_convert_to_bigints<F: PrimeField, P: UVPolynomial<F>>(
  p: &P,
) -> (usize, Vec<F::BigInt>) {
  let mut num_leading_zeros = 0;
  while num_leading_zeros < p.coeffs().len() && p.coeffs()[num_leading_zeros].is_zero() {
    num_leading_zeros += 1;
  }
  let coeffs = convert_to_bigints(&p.coeffs()[num_leading_zeros..]);
  (num_leading_zeros, coeffs)
}

fn convert_to_bigints<F: PrimeField>(p: &[F]) -> Vec<F::BigInt> {
  let to_bigint_time = start_timer!(|| "Converting polynomial coeffs to bigints");
  let coeffs = ark_std::cfg_iter!(p)
    .map(|s| s.into_bigint())
    .collect::<Vec<_>>();
  end_timer!(to_bigint_time);
  coeffs
}

#[cfg(test)]
mod tests {
  #![allow(non_camel_case_types)]
  use crate::kzg::*;
  use crate::*;
  use ark_poly_commit::{PCCommitment, Polynomial};

  use ark_bls12_377::Bls12_377;
  use ark_bls12_381::Bls12_381;
  use ark_ec::pairing::Pairing as PairingEngine;
  use ark_poly::univariate::DensePolynomial as DensePoly;
  use ark_std::test_rng;

  type ScalarField = <ark_bls12_381::Bls12_381 as PairingEngine>::ScalarField;
  type UniPoly_381 = DensePoly<<Bls12_381 as PairingEngine>::ScalarField>;
  type UniPoly_377 = DensePoly<<Bls12_377 as PairingEngine>::ScalarField>;
  type KZG_Bls12_381 = KZG10<Bls12_381, UniPoly_381>;

  impl<E: PairingEngine, P: UVPolynomial<E::ScalarField>> KZG10<E, P> {
    /// Specializes the public parameters for a given maximum degree `d` for polynomials
    /// `d` should be less that `pp.max_degree()`.
    pub(crate) fn trim(
      pp: &UniversalParams<E>,
      mut supported_degree: usize,
    ) -> Result<(Vec<E::G1Affine>, VerifierKey<E>), Error> {
      if supported_degree == 1 {
        supported_degree += 1;
      }
      let powers_of_g = pp.powers_of_g[..=supported_degree].to_vec();

      let vk = VerifierKey {
        g: pp.powers_of_g[0],
        h: pp.h,
        beta_h: pp.beta_h,
        prepared_h: pp.prepared_h.clone(),
        prepared_beta_h: pp.prepared_beta_h.clone(),
      };
      Ok((powers_of_g, vk))
    }
  }

  #[test]
  fn basic_test() {
    let rng = &mut test_rng();
    let p = DensePoly::from_coefficients_slice(&[
      ScalarField::from(1),
      ScalarField::from(2),
      ScalarField::from(3),
      ScalarField::from(0),
      ScalarField::from(7),
      ScalarField::from(9),
    ]);
    let pp = KZG_Bls12_381::setup(10, rng).unwrap();
    let (powers, vk) = KZG_Bls12_381::trim(&pp, 6).unwrap();
    let comm = KZG10::commit(&powers, &p).unwrap();

    let z = ScalarField::from(2);
    println!("z = {}", z);
    let px = p.evaluate(&z);
    println!("p(z) = {}", px);

    let proof = KZG10::open(&powers, &p, &z).unwrap();
    assert!(
      KZG_Bls12_381::check(&vk, &comm, &z, &px, &proof).unwrap(),
      "proof was incorrect for max_degree = {}, polynomial_degree = {}",
      10,
      p.degree(),
    );
  }

  #[test]
  fn add_commitments_test() {
    let rng = &mut test_rng();
    let p = UniPoly_381::from_coefficients_slice(&[
      ScalarField::rand(rng),
      ScalarField::rand(rng),
      ScalarField::rand(rng),
      ScalarField::rand(rng),
      ScalarField::rand(rng),
    ]);
    let f = ScalarField::rand(rng);
    let mut f_p = DensePoly::zero();
    f_p += (f, &p);

    let degree = 4;
    let pp = KZG_Bls12_381::setup(degree, rng).unwrap();
    let (powers, _) = KZG_Bls12_381::trim(&pp, degree).unwrap();

    // let hiding_bound = None;
    // let (comm, _) = KZG10::commit(&powers, &p, hiding_bound, Some(rng)).unwrap();
    // let (f_comm, _) = KZG10::commit(&powers, &f_p, hiding_bound, Some(rng)).unwrap();
    let comm = KZG_Bls12_381::commit(&powers, &p).unwrap();
    let f_comm = KZG10::commit(&powers, &f_p).unwrap();
    let mut f_comm_2 = Commitment::empty();
    f_comm_2 += (f, &comm);

    assert_eq!(f_comm, f_comm_2);
  }

  fn end_to_end_test_template<E, P>() -> Result<(), Error>
  where
    E: PairingEngine,
    P: UVPolynomial<E::ScalarField, Point = E::ScalarField>,
    for<'a, 'b> &'a P: Div<&'b P, Output = P> + Mul<E::ScalarField, Output = P>,
  {
    let rng = &mut test_rng();
    for _ in 0..10 {
      let mut degree = 0;
      while degree <= 1 {
        degree = usize::rand(rng) % 20;
      }
      let pp = KZG10::<E, P>::setup(degree, rng)?;
      let (ck, vk) = KZG10::<E, P>::trim(&pp, degree)?;
      let p = P::rand(degree, rng);
      // let hiding_bound = Some(1);
      // let (comm, rand) = KZG10::<E, P>::commit(&ck, &p, hiding_bound, Some(rng))?;
      let comm = KZG10::<E, P>::commit(&ck, &p)?;
      let point = E::ScalarField::rand(rng);
      let value = p.evaluate(&point);
      let proof = KZG10::<E, P>::open(&ck, &p, &point)?;
      assert!(
        KZG10::<E, P>::check(&vk, &comm, &point, &value, &proof)?,
        // "proof was incorrect for max_degree = {}, polynomial_degree = {}, hiding_bound = {:?}",
        "proof was incorrect for max_degree = {}, polynomial_degree = {}",
        degree,
        p.degree(),
        // hiding_bound,
      );
    }
    Ok(())
  }

  fn linear_polynomial_test_template<E, P>() -> Result<(), Error>
  where
    E: PairingEngine,
    P: UVPolynomial<E::ScalarField, Point = E::ScalarField>,
    for<'a, 'b> &'a P: Div<&'b P, Output = P> + Mul<E::ScalarField, Output = P>,
  {
    let rng = &mut test_rng();
    for _ in 0..10 {
      let degree = 50;
      let pp = KZG10::<E, P>::setup(degree, rng)?;
      let (ck, vk) = KZG10::<E, P>::trim(&pp, 2)?;
      let p = P::rand(1, rng);
      let comm = KZG10::<E, P>::commit(&ck, &p)?;
      let point = E::ScalarField::rand(rng);
      let value = p.evaluate(&point);
      let proof = KZG10::<E, P>::open(&ck, &p, &point)?;
      assert!(
        KZG10::<E, P>::check(&vk, &comm, &point, &value, &proof)?,
        // "proof was incorrect for max_degree = {}, polynomial_degree = {}, hiding_bound = {:?}",
        "proof was incorrect for max_degree = {}, polynomial_degree = {}",
        degree,
        p.degree(),
        // hiding_bound,
      );
    }
    Ok(())
  }

  fn batch_check_test_template<E, P>() -> Result<(), Error>
  where
    E: PairingEngine,
    P: UVPolynomial<E::ScalarField, Point = E::ScalarField>,
    for<'a, 'b> &'a P: Div<&'b P, Output = P> + Mul<E::ScalarField, Output = P>,
  {
    let rng = &mut test_rng();
    let batch_check_test_time = start_timer!(|| "Batch check test time");
    for i in 0..10 {
      let batch_check_test_time_body = start_timer!(|| format!("Batch check test body time {}", i));

      let batch_check_test_time_preamble =
        start_timer!(|| format!("Batch check test preamble time {}", i));
      let degree = usize::rand(rng) % 19 + 1;
      let f_num = usize::rand(rng) % 19 + 1;
      let g_num = usize::rand(rng) % 19 + 1;
      let pp = KZG10::<E, P>::setup(degree, rng)?;
      let (ck, vk) = KZG10::<E, P>::trim(&pp, degree)?;
      let mut fs = Vec::new();
      let mut gs = Vec::new();
      let mut f_comms = Vec::new();
      let mut g_comms = Vec::new();
      let mut f_values = Vec::new();
      let mut g_values = Vec::new();
      let z = E::ScalarField::rand(rng);
      let zz = E::ScalarField::rand(rng);
      end_timer!(batch_check_test_time_preamble);

      let batch_check_test_time_prepare = start_timer!(|| format!(
        "Batch check test prepare polys and comms time {} for {} polys",
        i,
        f_num + g_num
      ));
      for _ in 0..f_num {
        let f = P::rand(degree, rng);
        let comm = KZG10::<E, P>::commit(&ck, &f)?;
        let value = f.evaluate(&z);
        let proof = KZG10::<E, P>::open(&ck, &f, &z)?;

        assert!(KZG10::<E, P>::check(&vk, &comm, &z, &value, &proof)?);
        fs.push(f);
        f_comms.push(comm);
        f_values.push(value);
      }
      for _ in 0..g_num {
        let g = P::rand(degree, rng);
        let comm = KZG10::<E, P>::commit(&ck, &g)?;
        let value = g.evaluate(&zz);
        let proof = KZG10::<E, P>::open(&ck, &g, &zz)?;

        assert!(KZG10::<E, P>::check(&vk, &comm, &zz, &value, &proof)?);
        gs.push(g);
        g_comms.push(comm);
        g_values.push(value);
      }
      end_timer!(batch_check_test_time_prepare);

      let batch_check_test_time_open = start_timer!(|| format!("Batch check test open time {}", i));
      let rand_xi = E::ScalarField::rand(rng);
      let rand_xi_2 = E::ScalarField::rand(rng);
      let (proof, proof_2) =
        KZG10::<E, P>::batch_open(&ck, &fs, &gs, &z, &zz, &rand_xi, &rand_xi_2)?;
      end_timer!(batch_check_test_time_open);

      let batch_check_test_time_check_individual_time =
        start_timer!(|| format!("Batch check test check individual time {}", i));
      let mut total_f = P::zero();
      let mut total_g = P::zero();
      let mut xi_power = E::ScalarField::one();
      let mut xi_power_2 = E::ScalarField::one();
      let mut total_comm_f = Commitment::<E>::empty();
      let mut total_comm_g = Commitment::<E>::empty();
      for (f, comm_f) in fs.iter().zip(&f_comms) {
        total_f += &f.mul(xi_power);
        total_comm_f += (xi_power, &comm_f);
        xi_power *= rand_xi;
      }
      let comm_total_f = KZG10::<E, P>::commit(&ck, &total_f)?;
      assert!(
        comm_total_f == total_comm_f,
        "Sum of f commitment != commit to sum of f"
      );

      for (g, comm_g) in gs.iter().zip(&g_comms) {
        total_g += &g.mul(xi_power_2);
        total_comm_g += (xi_power_2, &comm_g);
        xi_power_2 *= rand_xi_2;
      }
      let comm_total_g = KZG10::<E, P>::commit(&ck, &total_g)?;
      assert!(
        comm_total_g == total_comm_g,
        "Sum of g commitment != commit to sum of g"
      );

      let total_f_eval = total_f.evaluate(&z);
      let total_g_eval = total_g.evaluate(&zz);
      assert!(KZG10::<E, P>::check(
        &vk,
        &comm_total_f,
        &z,
        &total_f_eval,
        &proof
      )?);
      assert!(KZG10::<E, P>::check(
        &vk,
        &comm_total_g,
        &zz,
        &total_g_eval,
        &proof_2
      )?);
      end_timer!(batch_check_test_time_check_individual_time);

      let batch_check_test_check_time =
        start_timer!(|| format!("Batch check test check time {}", i));

      assert!(KZG10::<E, P>::batch_check(
        &vk, &f_comms, &g_comms, &z, &zz, &rand_xi, &rand_xi_2, &f_values, &g_values, &proof,
        &proof_2, rng
      )?);
      end_timer!(batch_check_test_check_time);

      end_timer!(batch_check_test_time_body);
    }
    end_timer!(batch_check_test_time);
    Ok(())
  }

  #[test]
  fn end_to_end_test() {
    end_to_end_test_template::<Bls12_377, UniPoly_377>().expect("test failed for bls12-377");
    end_to_end_test_template::<Bls12_381, UniPoly_381>().expect("test failed for bls12-381");
  }

  #[test]
  fn linear_polynomial_test() {
    linear_polynomial_test_template::<Bls12_377, UniPoly_377>().expect("test failed for bls12-377");
    linear_polynomial_test_template::<Bls12_381, UniPoly_381>().expect("test failed for bls12-381");
  }
  #[test]
  fn batch_check_test() {
    batch_check_test_template::<Bls12_377, UniPoly_377>().expect("test failed for bls12-377");
    batch_check_test_template::<Bls12_381, UniPoly_381>().expect("test failed for bls12-381");
  }

  #[test]
  fn test_degree_is_too_large() {
    let rng = &mut test_rng();

    let max_degree = 123;
    let pp = KZG_Bls12_381::setup(max_degree, rng).unwrap();
    let (powers, _) = KZG_Bls12_381::trim(&pp, max_degree).unwrap();

    let p = DensePoly::<ScalarField>::rand(max_degree + 1, rng);
    assert!(p.degree() > max_degree);
    assert!(KZG_Bls12_381::check_degree_is_too_large(p.degree(), powers.len()).is_err());
  }
}
