///! This file is generated by https://github.com/yczhangsjtu/voproof-scripts/__init__.py
use super::*;

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct POVProverEfficientProverKey<E: PairingEngine> {
  pub verifier_key: POVProverEfficientVerifierKey<E>,
  pub powers: Vec<E::G1Affine>,
  pub max_degree: u64,
  pub sigma_vec: Vec<E::ScalarField>,
    pub d_vec: Vec<E::ScalarField>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct POVProverEfficientVerifierKey<E: PairingEngine> {
  pub cm_sigma_vec: Commitment<E>,
    pub cm_d_vec: Commitment<E>,
  pub kzg_vk: VerifierKey<E>,
  pub size: POVSize,
  pub degree_bound: u64,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct POVProverEfficientProof<E: PairingEngine> {pub cm_u_vec: Commitment<E>,
    pub cm_v_vec: Commitment<E>,
    pub cm_r_vec: Commitment<E>,
    pub cm_t_vec_1: Commitment<E>,
    pub cm_h_vec_1: Commitment<E>,
    pub cm_h_vec_2: Commitment<E>,
    pub y: E::ScalarField,
    pub y_2: E::ScalarField,
    pub cap_w: KZGProof<E>,
    pub cap_w_1: KZGProof<E>,}

pub struct VOProofPOVProverEfficient {}

impl<E: PairingEngine> SNARKProverKey<E> for POVProverEfficientProverKey<E> {}

impl<E: PairingEngine> SNARKVerifierKey<E> for POVProverEfficientVerifierKey<E> {}

impl<E: PairingEngine> SNARKProof<E> for POVProverEfficientProof<E> {}

impl VOProofPOVProverEfficient {
  pub fn get_max_degree(size: POVSize) -> usize {
    ((size.nmul as i64) + 4*(size.n as i64)) as usize
  }
}

impl<E: PairingEngine> SNARK<E> for VOProofPOVProverEfficient {
  type Size = POVSize;
  type CS = POV<E::ScalarField>;
  type PK = POVProverEfficientProverKey<E>;
  type VK = POVProverEfficientVerifierKey<E>;
  type Ins = POVInstance<E::ScalarField>;
  type Wit = POVWitness<E::ScalarField>;
  type Pf = POVProverEfficientProof<E>;

  fn setup(size: usize) -> Result<UniversalParams<E>, Error> {
    let rng = &mut test_rng();
    KZG10::<E, DensePoly<E::ScalarField>>::setup(size, rng)
  }

  fn index(
    pp: &UniversalParams<E>,
    cs: &POV<E::ScalarField>,
  ) -> Result<(POVProverEfficientProverKey<E>, POVProverEfficientVerifierKey<E>), Error> {
    let max_degree = Self::get_max_degree(cs.get_size());
    let cap_d = pp.powers_of_g.len();
    assert!(cap_d > max_degree);

    let powers_of_g = pp.powers_of_g[..].to_vec();
    let size = cs.get_size();
    init_size!(
          cap_c_a,
          nadd,
          size);
        init_size!(
          cap_c_m,
          nmul,
          size);
        init_size!(
          cap_c_total,
          n,
          size);
        define_generator!(
          gamma,
          E);
        define_permutation_vector_from_wires!(
          sigma_vec,
          gamma,
          cs.wires,
          3*cap_c_total);
        define!(
          d_vec,
          cs.consts.clone());
        define_commit_vector!(
          cm_sigma_vec,
          sigma_vec,
          powers_of_g,
          3*cap_c_total);
        define_commit_vector!(
          cm_d_vec,
          d_vec,
          powers_of_g,
          -cap_c_a - cap_c_m + cap_c_total);
        
    let verifier_key = POVProverEfficientVerifierKey::<E> {
      cm_sigma_vec: cm_sigma_vec,
            cm_d_vec: cm_d_vec,
      kzg_vk: VerifierKey {
        g: pp.powers_of_g[0],
        h: pp.h,
        beta_h: pp.beta_h,
        prepared_h: pp.prepared_h.clone(),
        prepared_beta_h: pp.prepared_beta_h.clone(),
      },
      size,
      degree_bound: cap_d as u64,
    };
    Ok((
      POVProverEfficientProverKey::<E> {
        verifier_key: verifier_key.clone(),
        powers: powers_of_g,
        max_degree: max_degree as u64,
        sigma_vec: sigma_vec,
            d_vec: d_vec,
      },
      verifier_key,
    ))
  }
  fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error> {
    let size = pk.verifier_key.size.clone();
    let vk = pk.verifier_key.clone();
    let cap_d = pk.verifier_key.degree_bound as i64;
    let rng = &mut test_rng();
    sample_randomizers!(
          rng,
          delta_vec,
          1,
          delta_vec_1,
          1,
          delta_vec_2,
          1,
          delta_vec_3,
          1);
        init_size!(
          cap_c_a,
          nadd,
          size);
        init_size!(
          cap_c_m,
          nmul,
          size);
        init_size!(
          cap_c_total,
          n,
          size);
        define_sparse_vector!(
          x_vec,
          x.instance.0,
          x.instance.1,
          3*cap_c_total);
        define_vec!(
          a_vec,
          w.witness.0.clone());
        define_vec!(
          b_vec,
          w.witness.1.clone());
        define_vec!(
          c_vec,
          w.witness.2.clone());
        define!(
          n,
          3*cap_c_total);
        define_concat_subvec!(
          u_vec,
          a_vec,
          0,
          cap_c_total,
          b_vec,
          0,
          cap_c_m);
        define_concat_subvec!(
          v_vec,
          b_vec,
          cap_c_m,
          cap_c_total,
          c_vec,
          0,
          cap_c_a + cap_c_m);
        redefine_zero_pad_concat_vector!(
          u_vec,
          n,
          delta_vec);
        define_commit_vector!(
          cm_u_vec,
          u_vec,
          pk.powers,
          n + 1);
        redefine_zero_pad_concat_vector!(
          v_vec,
          n,
          delta_vec_1);
        define_commit_vector!(
          cm_v_vec,
          v_vec,
          pk.powers,
          n + 1);
        define_sparse_zero_one_vector!(
          t_vec,
          x.instance.0,
          3*cap_c_total);
        define_generator!(
          gamma,
          E);
        get_randomness_from_hash!(
          zeta,
          one!(),
          x.instance.0, x.instance.1,
          pk.verifier_key.cm_sigma_vec,
          pk.verifier_key.cm_d_vec,
          cm_u_vec,
          cm_v_vec);
        get_randomness_from_hash!(
          zeta_1,
          scalar_to_field!(
          2),
          x.instance.0, x.instance.1,
          pk.verifier_key.cm_sigma_vec,
          pk.verifier_key.cm_d_vec,
          cm_u_vec,
          cm_v_vec);
        define_accumulate_vector_mul!(
          r_vec,
          i,
          mul!(
          vector_index!(
          u_vec,
          minus_i64!(
          i,
          1)) + vector_index!(
          v_vec,
          minus_i64!(
          i,
          cap_c_m + cap_c_total + 1)) + vector_index!(
          pk.d_vec,
          minus_i64!(
          i,
          cap_c_a + cap_c_m + 2*cap_c_total + 1)) + power_vector_index!(
          gamma,
          3*cap_c_total,
          minus_i64!(
          i,
          1))*zeta + range_index!(
          1,
          3*cap_c_total,
          minus_i64!(
          i,
          1))*zeta_1,
          inverse!(
          vector_index!(
          u_vec,
          minus_i64!(
          i,
          1)) + vector_index!(
          v_vec,
          minus_i64!(
          i,
          cap_c_m + cap_c_total + 1)) + vector_index!(
          pk.d_vec,
          minus_i64!(
          i,
          cap_c_a + cap_c_m + 2*cap_c_total + 1)) + range_index!(
          1,
          3*cap_c_total,
          minus_i64!(
          i,
          1))*zeta_1 + vector_index!(
          pk.sigma_vec,
          minus_i64!(
          i,
          1))*zeta)),
          3*cap_c_total);
        redefine_zero_pad_concat_vector!(
          r_vec,
          n,
          delta_vec_2);
        define_commit_vector!(
          cm_r_vec,
          r_vec,
          pk.powers,
          n + 1);
        define!(
          maxshift,
          cap_c_m + cap_c_total);
        get_randomness_from_hash!(
          alpha,
          one!(),
          x.instance.0, x.instance.1,
          pk.verifier_key.cm_sigma_vec,
          pk.verifier_key.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec);
        define!(
          c,
          power(alpha, 2));
        define!(
          c_1,
          power(alpha, 3));
        define!(
          c_2,
          -power(alpha, 3));
        define_vec!(
          t_vec_1,
          vector_concat!(
          delta_vec_3,
          expression_vector!(
          i,
          c*vector_index!(
          t_vec,
          minus_i64!(
          i + n,
          1))*(vector_index!(
          u_vec,
          minus_i64!(
          i + n,
          1)) + vector_index!(
          v_vec,
          minus_i64!(
          i + n,
          cap_c_m + cap_c_total + 1)) - vector_index!(
          x_vec,
          minus_i64!(
          i + n,
          1))) + c_2*vector_index!(
          r_vec,
          minus_i64!(
          i + n,
          -3*cap_c_total + n + 1))*(vector_index!(
          u_vec,
          minus_i64!(
          i + n,
          -3*cap_c_total + n + 1)) + vector_index!(
          v_vec,
          minus_i64!(
          i + n,
          cap_c_m - 2*cap_c_total + n + 1)) + vector_index!(
          pk.d_vec,
          minus_i64!(
          i + n,
          cap_c_a + cap_c_m - cap_c_total + n + 1)) + range_index!(
          1,
          3*cap_c_total,
          minus_i64!(
          i + n,
          -3*cap_c_total + n + 1))*zeta_1 + vector_index!(
          pk.sigma_vec,
          minus_i64!(
          i + n,
          -3*cap_c_total + n + 1))*zeta) - vector_index!(
          v_vec,
          minus_i64!(
          i + n,
          cap_c_m + 1))*range_index!(
          1,
          cap_c_m,
          minus_i64!(
          i + n,
          cap_c_total + 1)) + vector_index!(
          u_vec,
          minus_i64!(
          i + n,
          cap_c_total + 1))*vector_index!(
          u_vec,
          i + n) + (power(alpha, 3)*delta!(
          i + n,
          -3*cap_c_total + n + 1) + c_1*vector_index!(
          r_vec,
          minus_i64!(
          i + n,
          -3*cap_c_total + n + 2)))*(vector_index!(
          u_vec,
          minus_i64!(
          i + n,
          -3*cap_c_total + n + 1)) + vector_index!(
          v_vec,
          minus_i64!(
          i + n,
          cap_c_m - 2*cap_c_total + n + 1)) + vector_index!(
          pk.d_vec,
          minus_i64!(
          i + n,
          cap_c_a + cap_c_m - cap_c_total + n + 1)) + power_vector_index!(
          gamma,
          3*cap_c_total,
          minus_i64!(
          i + n,
          -3*cap_c_total + n + 1))*zeta + range_index!(
          1,
          3*cap_c_total,
          minus_i64!(
          i + n,
          -3*cap_c_total + n + 1))*zeta_1),
          maxshift + 2)));
        define_commit_vector!(
          cm_t_vec_1,
          t_vec_1,
          pk.powers,
          maxshift + 2);
        get_randomness_from_hash!(
          omega,
          one!(),
          x.instance.0, x.instance.1,
          pk.verifier_key.cm_sigma_vec,
          pk.verifier_key.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec,
          cm_t_vec_1);
        define!(
          c_3,
          omega.inverse().unwrap());
        define_vector_domain_evaluations_dict!(
          _u_vec_left_eval_dict,
          _u_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_2,
          u_vec,
          u_vec,
          omega,
          shiftlength,
          _u_vec_left_eval_dict,
          _u_vec_right_eval_dict);
        define_vector_domain_evaluations_dict!(
          _t_vec_left_eval_dict,
          _t_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_3,
          t_vec,
          u_vec,
          omega,
          shiftlength_1,
          _t_vec_left_eval_dict,
          _u_vec_right_eval_dict);
        define_vector_domain_evaluations_dict!(
          _v_vec_left_eval_dict,
          _v_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_4,
          t_vec,
          v_vec,
          omega,
          shiftlength_2,
          _t_vec_left_eval_dict,
          _v_vec_right_eval_dict);
        define_vector_domain_evaluations_dict!(
          _x_vec_left_eval_dict,
          _x_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_5,
          t_vec,
          x_vec,
          omega,
          shiftlength_3,
          _t_vec_left_eval_dict,
          _x_vec_right_eval_dict);
        define_vector_domain_evaluations_dict!(
          _r_vec_left_eval_dict,
          _r_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_6,
          r_vec,
          u_vec,
          omega,
          shiftlength_4,
          _r_vec_left_eval_dict,
          _u_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_7,
          r_vec,
          v_vec,
          omega,
          shiftlength_5,
          _r_vec_left_eval_dict,
          _v_vec_right_eval_dict);
        define_vector_domain_evaluations_dict!(
          _pk_d_vec_left_eval_dict,
          _pk_d_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_8,
          r_vec,
          pk.d_vec,
          omega,
          shiftlength_6,
          _r_vec_left_eval_dict,
          _pk_d_vec_right_eval_dict);
        define_vector_reverse_omega_shift!(
          v_vec_9,
          r_vec,
          omega,
          shiftlength_7);
        define_vector_domain_evaluations_dict!(
          _pk_sigma_vec_left_eval_dict,
          _pk_sigma_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_10,
          r_vec,
          pk.sigma_vec,
          omega,
          shiftlength_8,
          _r_vec_left_eval_dict,
          _pk_sigma_vec_right_eval_dict);
        define_vector_power_mul!(
          v_vec_11,
          v_vec,
          c_3,
          cap_c_m);
        define_vector_power_mul!(
          v_vec_12,
          v_vec,
          c_3,
          cap_c_a);
        define_vector_power_mul!(
          v_vec_13,
          u_vec,
          c_3,
          cap_c_a);
        define_vector_power_mul!(
          v_vec_14,
          v_vec_9,
          gamma,
          3*cap_c_total);
        define_vector_power_mul!(
          v_vec_15,
          v_vec_9,
          one!(),
          3*cap_c_total);
        define_vector_power_mul!(
          v_vec_16,
          t_vec_1,
          c_3,
          cap_c_m + cap_c_total + 1);
        define!(
          c_4,
          power(omega, cap_c_total));
        define!(
          c_5,
          -power(alpha, 2));
        define!(
          c_6,
          power(alpha, 3)*omega);
        define!(
          c_7,
          power(alpha, 4));
        define!(
          c_8,
          -power(alpha, 3)*zeta);
        define!(
          c_9,
          power(alpha, 3)*zeta);
        define!(
          c_10,
          power(alpha, 3)*zeta_1);
        define!(
          c_11,
          -power(omega, cap_c_m + cap_c_total - 1));
        define!(
          c_12,
          alpha*power(omega, cap_c_a + cap_c_total - 1));
        define!(
          c_13,
          -alpha*power(omega, cap_c_a + cap_c_total - 1));
        define!(
          c_14,
          power(alpha, 3)*omega*zeta);
        define!(
          c_15,
          power(alpha, 3)*omega*zeta_1);
        define!(
          c_16,
          -power(alpha, 3)*zeta_1);
        define!(
          c_17,
          -power(omega, cap_c_m + 4*cap_c_total));
        define_expression_vector!(
          h_vec_1,
          i,
          -power(alpha, 4)*power(omega, 3*cap_c_total - 1)*delta!(
          i - maxshift - n,
          1) + c*vector_index!(
          v_vec_3,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_1)) + c*vector_index!(
          v_vec_4,
          minus_i64!(
          i - maxshift - n,
          cap_c_m + cap_c_total - shiftlength_2 + 1)) + c_1*vector_index!(
          v_vec,
          minus_i64!(
          i - maxshift - n,
          cap_c_m + cap_c_total + 1)) + c_1*vector_index!(
          u_vec,
          minus_i64!(
          i - maxshift - n,
          1)) + c_1*vector_index!(
          pk.d_vec,
          minus_i64!(
          i - maxshift - n,
          cap_c_a + cap_c_m + 2*cap_c_total + 1)) + c_10*range_index!(
          1,
          3*cap_c_total,
          minus_i64!(
          i - maxshift - n,
          1)) + c_11*vector_index!(
          v_vec_11,
          minus_i64!(
          i - maxshift - n,
          2 - cap_c_total)) + c_12*vector_index!(
          v_vec_12,
          minus_i64!(
          i - maxshift - n,
          2 - cap_c_a)) + c_12*vector_index!(
          v_vec_13,
          minus_i64!(
          i - maxshift - n,
          -cap_c_a - cap_c_m + 2)) + c_13*vector_index!(
          v_vec_12,
          minus_i64!(
          i - maxshift - n,
          -cap_c_a - cap_c_total + 2)) + c_14*vector_index!(
          v_vec_14,
          minus_i64!(
          i - maxshift - n,
          -shiftlength_7)) + c_15*vector_index!(
          v_vec_15,
          minus_i64!(
          i - maxshift - n,
          -shiftlength_7)) + c_16*vector_index!(
          v_vec_15,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_7)) + c_17*vector_index!(
          v_vec_16,
          minus_i64!(
          i - maxshift - n,
          -cap_c_m - cap_c_total)) + c_2*vector_index!(
          v_vec_6,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_4)) + c_2*vector_index!(
          v_vec_7,
          minus_i64!(
          i - maxshift - n,
          cap_c_m + cap_c_total - shiftlength_5 + 1)) + c_2*vector_index!(
          v_vec_8,
          minus_i64!(
          i - maxshift - n,
          cap_c_a + cap_c_m + 2*cap_c_total - shiftlength_6 + 1)) + c_4*vector_index!(
          v_vec_2,
          minus_i64!(
          i - maxshift - n,
          -cap_c_total - shiftlength + 1)) + c_5*vector_index!(
          v_vec_5,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_3)) + c_6*vector_index!(
          v_vec_6,
          minus_i64!(
          i - maxshift - n,
          -shiftlength_4)) + c_6*vector_index!(
          v_vec_7,
          minus_i64!(
          i - maxshift - n,
          cap_c_m + cap_c_total - shiftlength_5)) + c_6*vector_index!(
          v_vec_8,
          minus_i64!(
          i - maxshift - n,
          cap_c_a + cap_c_m + 2*cap_c_total - shiftlength_6)) + c_7*vector_index!(
          v_vec_9,
          minus_i64!(
          i - maxshift - n,
          3*cap_c_total - shiftlength_7)) + c_8*vector_index!(
          v_vec_10,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_8)) + c_9*power_vector_index!(
          gamma,
          3*cap_c_total,
          minus_i64!(
          i - maxshift - n,
          1)),
          maxshift + n);
        define_expression_vector!(
          h_vec_2,
          i,
          -power(alpha, 4)*power(omega, 3*cap_c_total - 1)*delta!(
          i + 1,
          1) + c*vector_index!(
          v_vec_3,
          minus_i64!(
          i + 1,
          1 - shiftlength_1)) + c*vector_index!(
          v_vec_4,
          minus_i64!(
          i + 1,
          cap_c_m + cap_c_total - shiftlength_2 + 1)) + c_1*vector_index!(
          v_vec,
          minus_i64!(
          i + 1,
          cap_c_m + cap_c_total + 1)) + c_1*vector_index!(
          u_vec,
          minus_i64!(
          i + 1,
          1)) + c_1*vector_index!(
          pk.d_vec,
          minus_i64!(
          i + 1,
          cap_c_a + cap_c_m + 2*cap_c_total + 1)) + c_10*range_index!(
          1,
          3*cap_c_total,
          minus_i64!(
          i + 1,
          1)) + c_11*vector_index!(
          v_vec_11,
          minus_i64!(
          i + 1,
          2 - cap_c_total)) + c_12*vector_index!(
          v_vec_12,
          minus_i64!(
          i + 1,
          2 - cap_c_a)) + c_12*vector_index!(
          v_vec_13,
          minus_i64!(
          i + 1,
          -cap_c_a - cap_c_m + 2)) + c_13*vector_index!(
          v_vec_12,
          minus_i64!(
          i + 1,
          -cap_c_a - cap_c_total + 2)) + c_14*vector_index!(
          v_vec_14,
          minus_i64!(
          i + 1,
          -shiftlength_7)) + c_15*vector_index!(
          v_vec_15,
          minus_i64!(
          i + 1,
          -shiftlength_7)) + c_16*vector_index!(
          v_vec_15,
          minus_i64!(
          i + 1,
          1 - shiftlength_7)) + c_17*vector_index!(
          v_vec_16,
          minus_i64!(
          i + 1,
          -cap_c_m - cap_c_total)) + c_2*vector_index!(
          v_vec_6,
          minus_i64!(
          i + 1,
          1 - shiftlength_4)) + c_2*vector_index!(
          v_vec_7,
          minus_i64!(
          i + 1,
          cap_c_m + cap_c_total - shiftlength_5 + 1)) + c_2*vector_index!(
          v_vec_8,
          minus_i64!(
          i + 1,
          cap_c_a + cap_c_m + 2*cap_c_total - shiftlength_6 + 1)) + c_4*vector_index!(
          v_vec_2,
          minus_i64!(
          i + 1,
          -cap_c_total - shiftlength + 1)) + c_5*vector_index!(
          v_vec_5,
          minus_i64!(
          i + 1,
          1 - shiftlength_3)) + c_6*vector_index!(
          v_vec_6,
          minus_i64!(
          i + 1,
          -shiftlength_4)) + c_6*vector_index!(
          v_vec_7,
          minus_i64!(
          i + 1,
          cap_c_m + cap_c_total - shiftlength_5)) + c_6*vector_index!(
          v_vec_8,
          minus_i64!(
          i + 1,
          cap_c_a + cap_c_m + 2*cap_c_total - shiftlength_6)) + c_7*vector_index!(
          v_vec_9,
          minus_i64!(
          i + 1,
          3*cap_c_total - shiftlength_7)) + c_8*vector_index!(
          v_vec_10,
          minus_i64!(
          i + 1,
          1 - shiftlength_8)) + c_9*power_vector_index!(
          gamma,
          3*cap_c_total,
          minus_i64!(
          i + 1,
          1)),
          maxshift + n);
        define_commit_vector!(
          cm_h_vec_1,
          h_vec_1,
          pk.powers,
          cap_d);
        define_commit_vector!(
          cm_h_vec_2,
          h_vec_2,
          pk.powers,
          maxshift + n);
        get_randomness_from_hash!(
          z,
          one!(),
          x.instance.0, x.instance.1,
          pk.verifier_key.cm_sigma_vec,
          pk.verifier_key.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec,
          cm_t_vec_1,
          cm_h_vec_1,
          cm_h_vec_2);
        define_eval_vector_expression!(
          y,
          omega/z,
          i,
          vector_index!(
          u_vec,
          i),
          n + 1);
        define!(
          y_1,
          eval_sparse_zero_one_vector!(
          omega/z,
          x.instance.0));
        define_eval_vector_expression!(
          y_2,
          omega/z,
          i,
          vector_index!(
          r_vec,
          i),
          n + 1);
        define!(
          c_18,
          (power(alpha, 3)*one!()*(omega - one!()*z)*(omega*y_2 + one!()*z) - alpha*power(z, -cap_c_m + cap_c_total + 2)*power(omega/z, cap_c_total)*(one!() - power(omega/z, cap_c_a)) + one!()*z*(omega - one!()*z)*(-power(alpha, 3)*one!()*y_2 + power(alpha, 2)*one!()*y_1 + y*power(omega/z, cap_c_total)))/(z*(omega - one!()*z)));
        define!(
          c_19,
          (power(alpha, 2)*(omega - one!()*z)*(alpha*(-one!()*y_2*power(z, cap_c_m - 2*cap_c_total + n) + power(z, cap_c_m - 2*cap_c_total + n - 1)*(omega*y_2 + one!()*z)) + one!()*y_1*power(z, cap_c_m + cap_c_total)) + alpha*power(omega/z, cap_c_total)*(one!() - power(omega/z, cap_c_a))*(one!()*z - power(z, cap_c_total + 1)) + power(z, cap_c_m + 1)*power(omega/z, cap_c_total)*(one!() - power(omega/z, cap_c_m)))/(omega - one!()*z));
        define!(
          c_20,
          power(alpha, 2)*(alpha*(-power(one!(), 2)*y_2*z*zeta_1*(one!() - power(z, 3*cap_c_total))*(gamma*z - one!()) - one!()*(omega*y_2 + one!()*z)*(zeta*(one!() - z)*(one!() - power(gamma*z, 3*cap_c_total)) - zeta_1*(one!() - power(z, 3*cap_c_total))*(gamma*z - one!()))) + z*(one!() - z)*(gamma*z - one!())*(power(alpha, 2)*power(z, 3*cap_c_total - 1)*(one!()*y_2 - power(omega/z, 3*cap_c_total - 1)) - power(one!(), 2)*eval_sparse_vector!(
          z,
          x.instance.0,
          x.instance.1)*y_1))/(z*(one!() - z)*(gamma*z - one!())));
        define!(
          c_21,
          power(alpha, 3)*(-one!()*y_2*power(z, cap_c_a + cap_c_m - cap_c_total + n) + power(z, cap_c_a + cap_c_m - cap_c_total + n - 1)*(omega*y_2 + one!()*z)));
        define!(
          c_22,
          -power(alpha, 3)*power(one!(), 2)*y_2*zeta);
        define!(
          c_23,
          power(z, n)*power(omega/z, 3*cap_c_total)*(one!() - power(omega/z, cap_c_m + cap_c_total + 1))/(omega - one!()*z));
        define!(
          c_24,
          -power(z, -cap_d));
        define!(
          c_25,
          -z);
        define_vec_mut!(
          g_vec,
          expression_vector!(
          i,
          linear_combination_base_zero!(
          c_18,
          vector_index!(
          u_vec,
          i),
          c_19,
          vector_index!(
          v_vec,
          i),
          c_21,
          vector_index!(
          pk.d_vec,
          i),
          c_22,
          vector_index!(
          pk.sigma_vec,
          i),
          c_23,
          vector_index!(
          t_vec_1,
          i),
          c_24,
          vector_index!(
          h_vec_1,
          -cap_d + i + maxshift + n),
          c_25,
          vector_index!(
          h_vec_2,
          i)),
          cap_d));
        add_to_first_item!(
          g_vec,
          c_20);
        define_commitment_linear_combination!(
          cm_g,
          vk,
          c_20,
          cm_u_vec,
          c_18,
          cm_v_vec,
          c_19,
          vk.cm_d_vec,
          c_21,
          vk.cm_sigma_vec,
          c_22,
          cm_t_vec_1,
          c_23,
          cm_h_vec_1,
          c_24,
          cm_h_vec_2,
          c_25);
        define_poly_from_vec!(
          u_vec_poly,
          u_vec);
        define_poly_from_vec!(
          r_vec_poly,
          r_vec);
        define_poly_from_vec!(
          g_poly,
          g_vec);
        check_poly_eval!(
          g_poly,
          z,
          zero!(),
          "g does not evaluate to 0 at z");
        define!(
          fs,
          vec!(
          u_vec_poly,
          r_vec_poly));
        define!(
          gs,
          vec!(
          g_poly));
        get_randomness_from_hash!(
          rand_xi,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec,
          cm_t_vec_1,
          cm_h_vec_1,
          cm_h_vec_2,
          cm_g,
          omega/z,
          y,
          y_2,
          z);
        get_randomness_from_hash!(
          rand_xi_2,
          scalar_to_field!(
          2),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec,
          cm_t_vec_1,
          cm_h_vec_1,
          cm_h_vec_2,
          cm_g,
          omega/z,
          y,
          y_2,
          z);
        define!(
          z1,
          omega/z);
        define!(
          z2,
          z);
        
    let (cap_w, cap_w_1) = KZG10::batch_open(&pk.powers, &fs, &gs, &z1, &z2, &rand_xi, &rand_xi_2)?;
    Ok(POVProverEfficientProof::<E> {
            cm_u_vec: cm_u_vec,
            cm_v_vec: cm_v_vec,
            cm_r_vec: cm_r_vec,
            cm_t_vec_1: cm_t_vec_1,
            cm_h_vec_1: cm_h_vec_1,
            cm_h_vec_2: cm_h_vec_2,
            y: y,
            y_2: y_2,
            cap_w: cap_w,
            cap_w_1: cap_w_1,
        })
  }
  fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error> {
    let size = vk.size.clone();
    let cap_d = vk.degree_bound as i64;
    let rng = &mut test_rng();
    let cm_u_vec = proof.cm_u_vec;
        let cm_v_vec = proof.cm_v_vec;
        let cm_r_vec = proof.cm_r_vec;
        let cm_t_vec_1 = proof.cm_t_vec_1;
        let cm_h_vec_1 = proof.cm_h_vec_1;
        let cm_h_vec_2 = proof.cm_h_vec_2;
        let y = proof.y;
        let y_2 = proof.y_2;
        let cap_w = proof.cap_w;
        let cap_w_1 = proof.cap_w_1;init_size!(
          cap_c_a,
          nadd,
          size);
        init_size!(
          cap_c_m,
          nmul,
          size);
        init_size!(
          cap_c_total,
          n,
          size);
        define!(
          n,
          3*cap_c_total);
        define_generator!(
          gamma,
          E);
        get_randomness_from_hash!(
          zeta,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_u_vec,
          cm_v_vec);
        get_randomness_from_hash!(
          zeta_1,
          scalar_to_field!(
          2),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_u_vec,
          cm_v_vec);
        get_randomness_from_hash!(
          alpha,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec);
        get_randomness_from_hash!(
          omega,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec,
          cm_t_vec_1);
        get_randomness_from_hash!(
          z,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec,
          cm_t_vec_1,
          cm_h_vec_1,
          cm_h_vec_2);
        define!(
          y_1,
          eval_sparse_zero_one_vector!(
          omega/z,
          x.instance.0));
        define!(
          c_18,
          (power(alpha, 3)*one!()*(omega - one!()*z)*(omega*y_2 + one!()*z) - alpha*power(z, -cap_c_m + cap_c_total + 2)*power(omega/z, cap_c_total)*(one!() - power(omega/z, cap_c_a)) + one!()*z*(omega - one!()*z)*(-power(alpha, 3)*one!()*y_2 + power(alpha, 2)*one!()*y_1 + y*power(omega/z, cap_c_total)))/(z*(omega - one!()*z)));
        define!(
          c_19,
          (power(alpha, 2)*(omega - one!()*z)*(alpha*(-one!()*y_2*power(z, cap_c_m - 2*cap_c_total + n) + power(z, cap_c_m - 2*cap_c_total + n - 1)*(omega*y_2 + one!()*z)) + one!()*y_1*power(z, cap_c_m + cap_c_total)) + alpha*power(omega/z, cap_c_total)*(one!() - power(omega/z, cap_c_a))*(one!()*z - power(z, cap_c_total + 1)) + power(z, cap_c_m + 1)*power(omega/z, cap_c_total)*(one!() - power(omega/z, cap_c_m)))/(omega - one!()*z));
        define!(
          c_20,
          power(alpha, 2)*(alpha*(-power(one!(), 2)*y_2*z*zeta_1*(one!() - power(z, 3*cap_c_total))*(gamma*z - one!()) - one!()*(omega*y_2 + one!()*z)*(zeta*(one!() - z)*(one!() - power(gamma*z, 3*cap_c_total)) - zeta_1*(one!() - power(z, 3*cap_c_total))*(gamma*z - one!()))) + z*(one!() - z)*(gamma*z - one!())*(power(alpha, 2)*power(z, 3*cap_c_total - 1)*(one!()*y_2 - power(omega/z, 3*cap_c_total - 1)) - power(one!(), 2)*eval_sparse_vector!(
          z,
          x.instance.0,
          x.instance.1)*y_1))/(z*(one!() - z)*(gamma*z - one!())));
        define!(
          c_21,
          power(alpha, 3)*(-one!()*y_2*power(z, cap_c_a + cap_c_m - cap_c_total + n) + power(z, cap_c_a + cap_c_m - cap_c_total + n - 1)*(omega*y_2 + one!()*z)));
        define!(
          c_22,
          -power(alpha, 3)*power(one!(), 2)*y_2*zeta);
        define!(
          c_23,
          power(z, n)*power(omega/z, 3*cap_c_total)*(one!() - power(omega/z, cap_c_m + cap_c_total + 1))/(omega - one!()*z));
        define!(
          c_24,
          -power(z, -cap_d));
        define!(
          c_25,
          -z);
        define_commitment_linear_combination!(
          cm_g,
          vk,
          c_20,
          cm_u_vec,
          c_18,
          cm_v_vec,
          c_19,
          vk.cm_d_vec,
          c_21,
          vk.cm_sigma_vec,
          c_22,
          cm_t_vec_1,
          c_23,
          cm_h_vec_1,
          c_24,
          cm_h_vec_2,
          c_25);
        define!(
          z1,
          omega/z);
        define!(
          z2,
          z);
        get_randomness_from_hash!(
          rand_xi,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec,
          cm_t_vec_1,
          cm_h_vec_1,
          cm_h_vec_2,
          cm_g,
          omega/z,
          y,
          y_2,
          z);
        get_randomness_from_hash!(
          rand_xi_2,
          scalar_to_field!(
          2),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_u_vec,
          cm_v_vec,
          cm_r_vec,
          cm_t_vec_1,
          cm_h_vec_1,
          cm_h_vec_2,
          cm_g,
          omega/z,
          y,
          y_2,
          z);
        define!(
          f_commitments,
          vec!(
          cm_u_vec,
          cm_r_vec));
        define!(
          g_commitments,
          vec!(
          cm_g));
        define!(
          f_values,
          vec!(
          y,
          y_2));
        define!(
          g_values,
          vec!(
          zero!()));
        
    if KZG10::<E, DensePoly<E::ScalarField>>::batch_check(
      &vk.kzg_vk,
      &f_commitments,
      &g_commitments,
      &z1,
      &z2,
      &rand_xi,
      &rand_xi_2,
      &f_values,
      &g_values,
      &cap_w,
      &cap_w_1,
      rng,
    )? {
      Ok(())
    } else {
      Err(Error::VerificationFail)
    }
  }
}

