///! This file is generated by https://github.com/yczhangsjtu/voproof-scripts/__init__.py
use super::*;

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct POVProverKey<E: PairingEngine> {
  pub verifier_key: POVVerifierKey<E>,
  pub powers: Vec<E::G1Affine>,
  pub max_degree: u64,
  pub sigma_vec: Vec<E::ScalarField>,
    pub d_vec: Vec<E::ScalarField>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct POVVerifierKey<E: PairingEngine> {
  pub cm_sigma_vec: Commitment<E>,
    pub cm_d_vec: Commitment<E>,
  pub kzg_vk: VerifierKey<E>,
  pub size: POVSize,
  pub degree_bound: u64,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct POVProof<E: PairingEngine> {pub cm_w_vec: Commitment<E>,
    pub cm_r_vec: Commitment<E>,
    pub cm_t_vec_1: Commitment<E>,
    pub cm_h_vec_1: Commitment<E>,
    pub cm_h_vec_2: Commitment<E>,
    pub y: E::ScalarField,
    pub y_2: E::ScalarField,
    pub cap_w: KZGProof<E>,
    pub cap_w_1: KZGProof<E>,}

pub struct VOProofPOV {}

impl<E: PairingEngine> SNARKProverKey<E> for POVProverKey<E> {}

impl<E: PairingEngine> SNARKVerifierKey<E> for POVVerifierKey<E> {}

impl<E: PairingEngine> SNARKProof<E> for POVProof<E> {}

impl VOProofPOV {
  pub fn get_max_degree(size: POVSize) -> usize {
    (6*(size.n as i64) - (size.nmul as i64)) as usize
  }
}

impl<E: PairingEngine> SNARK<E> for VOProofPOV {
  type Size = POVSize;
  type CS = POV<E::ScalarField>;
  type PK = POVProverKey<E>;
  type VK = POVVerifierKey<E>;
  type Ins = POVInstance<E::ScalarField>;
  type Wit = POVWitness<E::ScalarField>;
  type Pf = POVProof<E>;

  fn setup(size: usize) -> Result<UniversalParams<E>, Error> {
    let rng = &mut test_rng();
    KZG10::<E, DensePoly<E::ScalarField>>::setup(size, rng)
  }

  fn index(
    pp: &UniversalParams<E>,
    cs: &POV<E::ScalarField>,
  ) -> Result<(POVProverKey<E>, POVVerifierKey<E>), Error> {
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
          cap_c,
          n,
          size);
        define_generator!(
          gamma,
          E);
        define_permutation_vector_from_wires!(
          sigma_vec,
          gamma,
          cs.wires,
          3*cap_c);
        define!(
          d_vec,
          cs.consts.clone());
        define_commit_vector!(
          cm_sigma_vec,
          sigma_vec,
          powers_of_g,
          3*cap_c);
        define_commit_vector!(
          cm_d_vec,
          d_vec,
          powers_of_g,
          cap_c - cap_c_a - cap_c_m);
        
    let verifier_key = POVVerifierKey::<E> {
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
      POVProverKey::<E> {
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
          cap_c,
          n,
          size);
        define_sparse_vector!(
          x_vec,
          x.instance.0,
          x.instance.1,
          3*cap_c);
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
          3*cap_c);
        define_concat_vector!(
          w_vec,
          a_vec,
          b_vec,
          c_vec);
        redefine_zero_pad_concat_vector!(
          w_vec,
          n,
          delta_vec);
        define_commit_vector!(
          cm_w_vec,
          w_vec,
          pk.powers,
          n + 1);
        define_sparse_zero_one_vector!(
          t_vec,
          x.instance.0,
          3*cap_c);
        define_generator!(
          gamma,
          E);
        get_randomness_from_hash!(
          zeta,
          one!(),
          x.instance.0, x.instance.1,
          pk.verifier_key.cm_sigma_vec,
          pk.verifier_key.cm_d_vec,
          cm_w_vec);
        get_randomness_from_hash!(
          zeta_1,
          scalar_to_field!(
          2),
          x.instance.0, x.instance.1,
          pk.verifier_key.cm_sigma_vec,
          pk.verifier_key.cm_d_vec,
          cm_w_vec);
        define_accumulate_vector_mul!(
          r_vec,
          i,
          mul!(
          vector_index!(
          w_vec,
          minus_i64!(
          i,
          1)) + power_vector_index!(
          gamma,
          3*cap_c,
          minus_i64!(
          i,
          1))*zeta + range_index!(
          1,
          3*cap_c,
          minus_i64!(
          i,
          1))*zeta_1,
          inverse!(
          vector_index!(
          w_vec,
          minus_i64!(
          i,
          1)) + range_index!(
          1,
          3*cap_c,
          minus_i64!(
          i,
          1))*zeta_1 + vector_index!(
          pk.sigma_vec,
          minus_i64!(
          i,
          1))*zeta)),
          3*cap_c);
        redefine_zero_pad_concat_vector!(
          r_vec,
          n,
          delta_vec_1);
        define_commit_vector!(
          cm_r_vec,
          r_vec,
          pk.powers,
          n + 1);
        define!(
          maxshift,
          3*cap_c - cap_c_m);
        get_randomness_from_hash!(
          alpha,
          one!(),
          x.instance.0, x.instance.1,
          pk.verifier_key.cm_sigma_vec,
          pk.verifier_key.cm_d_vec,
          cm_w_vec,
          cm_r_vec);
        define!(
          c,
          power(alpha, 3));
        define!(
          c_1,
          power(alpha, 4));
        define!(
          c_2,
          -power(alpha, 4));
        define_vec!(
          t_vec_1,
          vector_concat!(
          delta_vec_2,
          expression_vector!(
          i,
          c*vector_index!(
          t_vec,
          minus_i64!(
          i + n,
          1))*(vector_index!(
          w_vec,
          minus_i64!(
          i + n,
          1)) - vector_index!(
          x_vec,
          minus_i64!(
          i + n,
          1))) + c_2*vector_index!(
          r_vec,
          minus_i64!(
          i + n,
          -3*cap_c + n + 1))*(vector_index!(
          w_vec,
          minus_i64!(
          i + n,
          -3*cap_c + n + 1)) + range_index!(
          1,
          3*cap_c,
          minus_i64!(
          i + n,
          -3*cap_c + n + 1))*zeta_1 + vector_index!(
          pk.sigma_vec,
          minus_i64!(
          i + n,
          -3*cap_c + n + 1))*zeta) + vector_index!(
          w_vec,
          minus_i64!(
          i + n,
          -cap_c_m + n + 1))*vector_index!(
          w_vec,
          minus_i64!(
          i + n,
          -cap_c - cap_c_m + n + 1)) - range_index!(
          1,
          cap_c_m,
          minus_i64!(
          i + n,
          -cap_c_m + n + 1))*vector_index!(
          w_vec,
          minus_i64!(
          i + n,
          -2*cap_c - cap_c_m + n + 1)) + (power(alpha, 4)*delta!(
          i + n,
          -3*cap_c + n + 1) + c_1*vector_index!(
          r_vec,
          minus_i64!(
          i + n,
          -3*cap_c + n + 2)))*(vector_index!(
          w_vec,
          minus_i64!(
          i + n,
          -3*cap_c + n + 1)) + power_vector_index!(
          gamma,
          3*cap_c,
          minus_i64!(
          i + n,
          -3*cap_c + n + 1))*zeta + range_index!(
          1,
          3*cap_c,
          minus_i64!(
          i + n,
          -3*cap_c + n + 1))*zeta_1),
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
          cm_w_vec,
          cm_r_vec,
          cm_t_vec_1);
        define!(
          c_3,
          omega.inverse().unwrap());
        define_vector_domain_evaluations_dict!(
          _w_vec_left_eval_dict,
          _w_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_1,
          w_vec,
          w_vec,
          omega,
          shiftlength,
          _w_vec_left_eval_dict,
          _w_vec_right_eval_dict);
        define_vector_domain_evaluations_dict!(
          _t_vec_left_eval_dict,
          _t_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_2,
          t_vec,
          w_vec,
          omega,
          shiftlength_1,
          _t_vec_left_eval_dict,
          _w_vec_right_eval_dict);
        define_vector_domain_evaluations_dict!(
          _x_vec_left_eval_dict,
          _x_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_3,
          t_vec,
          x_vec,
          omega,
          shiftlength_2,
          _t_vec_left_eval_dict,
          _x_vec_right_eval_dict);
        define_vector_domain_evaluations_dict!(
          _r_vec_left_eval_dict,
          _r_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_4,
          r_vec,
          w_vec,
          omega,
          shiftlength_3,
          _r_vec_left_eval_dict,
          _w_vec_right_eval_dict);
        define_vector_reverse_omega_shift!(
          v_vec_5,
          r_vec,
          omega,
          shiftlength_4);
        define_vector_domain_evaluations_dict!(
          _pk_sigma_vec_left_eval_dict,
          _pk_sigma_vec_right_eval_dict);
        define_vector_poly_mul_shift!(
          v_vec_6,
          r_vec,
          pk.sigma_vec,
          omega,
          shiftlength_5,
          _r_vec_left_eval_dict,
          _pk_sigma_vec_right_eval_dict);
        define_vector_power_mul!(
          v_vec_7,
          w_vec,
          c_3,
          cap_c_m);
        define_vector_power_mul!(
          v_vec_8,
          w_vec,
          c_3,
          cap_c_a);
        define_vector_power_mul!(
          v_vec_9,
          w_vec,
          c_3,
          cap_c - cap_c_a - cap_c_m);
        define_vector_power_mul!(
          v_vec_10,
          pk.d_vec,
          c_3,
          cap_c - cap_c_a - cap_c_m);
        define_vector_power_mul!(
          v_vec_11,
          v_vec_5,
          gamma,
          3*cap_c);
        define_vector_power_mul!(
          v_vec_12,
          v_vec_5,
          one!(),
          3*cap_c);
        define_vector_power_mul!(
          v_vec_13,
          t_vec_1,
          c_3,
          3*cap_c - cap_c_m + 1);
        define!(
          c_4,
          power(omega, 3*cap_c - cap_c_m));
        define!(
          c_5,
          -power(alpha, 3));
        define!(
          c_6,
          power(alpha, 4)*omega);
        define!(
          c_7,
          power(alpha, 5));
        define!(
          c_8,
          -power(alpha, 4)*zeta);
        define!(
          c_9,
          power(alpha, 4)*zeta);
        define!(
          c_10,
          power(alpha, 4)*zeta_1);
        define!(
          c_11,
          -power(omega, 3*cap_c - 1));
        define!(
          c_12,
          alpha*power(omega, 2*cap_c + cap_c_a + cap_c_m - 1));
        define!(
          c_13,
          -alpha*power(omega, 2*cap_c + cap_c_a + cap_c_m - 1));
        define!(
          c_14,
          power(alpha, 2)*power(omega, 3*cap_c - 1));
        define!(
          c_15,
          -power(alpha, 2)*power(omega, 3*cap_c - 1));
        define!(
          c_16,
          power(alpha, 4)*omega*zeta);
        define!(
          c_17,
          power(alpha, 4)*omega*zeta_1);
        define!(
          c_18,
          -power(alpha, 4)*zeta_1);
        define!(
          c_19,
          -power(omega, 6*cap_c - cap_c_m));
        define_expression_vector!(
          h_vec_1,
          i,
          -power(alpha, 5)*power(omega, 3*cap_c - 1)*delta!(
          i - maxshift - n,
          1) + c*vector_index!(
          v_vec_2,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_1)) + c_1*vector_index!(
          w_vec,
          minus_i64!(
          i - maxshift - n,
          1)) + c_10*range_index!(
          1,
          3*cap_c,
          minus_i64!(
          i - maxshift - n,
          1)) + c_11*vector_index!(
          v_vec_7,
          minus_i64!(
          i - maxshift - n,
          -2*cap_c - cap_c_m + 2)) + c_12*vector_index!(
          v_vec_8,
          minus_i64!(
          i - maxshift - n,
          -cap_c_a - cap_c_m + 2)) + c_12*vector_index!(
          v_vec_8,
          minus_i64!(
          i - maxshift - n,
          -cap_c - cap_c_a - cap_c_m + 2)) + c_13*vector_index!(
          v_vec_8,
          minus_i64!(
          i - maxshift - n,
          -2*cap_c - cap_c_a - cap_c_m + 2)) + c_14*vector_index!(
          v_vec_9,
          minus_i64!(
          i - maxshift - n,
          2 - 3*cap_c)) + c_15*vector_index!(
          v_vec_10,
          minus_i64!(
          i - maxshift - n,
          -cap_c + cap_c_a + cap_c_m + 2)) + c_16*vector_index!(
          v_vec_11,
          minus_i64!(
          i - maxshift - n,
          -shiftlength_4)) + c_17*vector_index!(
          v_vec_12,
          minus_i64!(
          i - maxshift - n,
          -shiftlength_4)) + c_18*vector_index!(
          v_vec_12,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_4)) + c_19*vector_index!(
          v_vec_13,
          minus_i64!(
          i - maxshift - n,
          -3*cap_c + cap_c_m)) + c_2*vector_index!(
          v_vec_4,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_3)) + c_4*vector_index!(
          v_vec_1,
          minus_i64!(
          i - maxshift - n,
          -cap_c - shiftlength + 1)) + c_5*vector_index!(
          v_vec_3,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_2)) + c_6*vector_index!(
          v_vec_4,
          minus_i64!(
          i - maxshift - n,
          -shiftlength_3)) + c_7*vector_index!(
          v_vec_5,
          minus_i64!(
          i - maxshift - n,
          3*cap_c - shiftlength_4)) + c_8*vector_index!(
          v_vec_6,
          minus_i64!(
          i - maxshift - n,
          1 - shiftlength_5)) + c_9*power_vector_index!(
          gamma,
          3*cap_c,
          minus_i64!(
          i - maxshift - n,
          1)),
          maxshift + n);
        define_expression_vector!(
          h_vec_2,
          i,
          -power(alpha, 5)*power(omega, 3*cap_c - 1)*delta!(
          i + 1,
          1) + c*vector_index!(
          v_vec_2,
          minus_i64!(
          i + 1,
          1 - shiftlength_1)) + c_1*vector_index!(
          w_vec,
          minus_i64!(
          i + 1,
          1)) + c_10*range_index!(
          1,
          3*cap_c,
          minus_i64!(
          i + 1,
          1)) + c_11*vector_index!(
          v_vec_7,
          minus_i64!(
          i + 1,
          -2*cap_c - cap_c_m + 2)) + c_12*vector_index!(
          v_vec_8,
          minus_i64!(
          i + 1,
          -cap_c_a - cap_c_m + 2)) + c_12*vector_index!(
          v_vec_8,
          minus_i64!(
          i + 1,
          -cap_c - cap_c_a - cap_c_m + 2)) + c_13*vector_index!(
          v_vec_8,
          minus_i64!(
          i + 1,
          -2*cap_c - cap_c_a - cap_c_m + 2)) + c_14*vector_index!(
          v_vec_9,
          minus_i64!(
          i + 1,
          2 - 3*cap_c)) + c_15*vector_index!(
          v_vec_10,
          minus_i64!(
          i + 1,
          -cap_c + cap_c_a + cap_c_m + 2)) + c_16*vector_index!(
          v_vec_11,
          minus_i64!(
          i + 1,
          -shiftlength_4)) + c_17*vector_index!(
          v_vec_12,
          minus_i64!(
          i + 1,
          -shiftlength_4)) + c_18*vector_index!(
          v_vec_12,
          minus_i64!(
          i + 1,
          1 - shiftlength_4)) + c_19*vector_index!(
          v_vec_13,
          minus_i64!(
          i + 1,
          -3*cap_c + cap_c_m)) + c_2*vector_index!(
          v_vec_4,
          minus_i64!(
          i + 1,
          1 - shiftlength_3)) + c_4*vector_index!(
          v_vec_1,
          minus_i64!(
          i + 1,
          -cap_c - shiftlength + 1)) + c_5*vector_index!(
          v_vec_3,
          minus_i64!(
          i + 1,
          1 - shiftlength_2)) + c_6*vector_index!(
          v_vec_4,
          minus_i64!(
          i + 1,
          -shiftlength_3)) + c_7*vector_index!(
          v_vec_5,
          minus_i64!(
          i + 1,
          3*cap_c - shiftlength_4)) + c_8*vector_index!(
          v_vec_6,
          minus_i64!(
          i + 1,
          1 - shiftlength_5)) + c_9*power_vector_index!(
          gamma,
          3*cap_c,
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
          cm_w_vec,
          cm_r_vec,
          cm_t_vec_1,
          cm_h_vec_1,
          cm_h_vec_2);
        define_eval_vector_expression!(
          y,
          omega/z,
          i,
          vector_index!(
          w_vec,
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
          c_20,
          (power(alpha, 4)*one!()*(omega - one!()*z)*(omega*y_2 + one!()*z) + z*(omega - one!()*z)*(-power(alpha, 4)*power(one!(), 2)*y_2 + power(alpha, 3)*power(one!(), 2)*y_1 + y*power(z, -cap_c - cap_c_m + n)*power(omega/z, 3*cap_c - cap_c_m)) + z*(-power(alpha, 2)*one!()*z*power(omega/z, 2*cap_c + cap_c_a + cap_c_m)*(one!() - power(omega/z, cap_c - cap_c_a - cap_c_m)) - alpha*power(omega/z, 2*cap_c + cap_c_m)*(one!() - power(omega/z, cap_c_a))*(-one!()*z + power(z, cap_c + 1) + power(z, 2*cap_c + 1)) + power(z, -2*cap_c - cap_c_m + n + 1)*power(omega/z, 3*cap_c - cap_c_m)*(one!() - power(omega/z, cap_c_m))))/(z*(omega - one!()*z)));
        define!(
          c_21,
          power(alpha, 2)*power(z, 2*cap_c + cap_c_a + cap_c_m + 1)*power(omega/z, 2*cap_c + cap_c_a + cap_c_m)*(one!() - power(omega/z, cap_c - cap_c_a - cap_c_m))/(omega - one!()*z));
        define!(
          c_22,
          power(alpha, 3)*(alpha*(-power(one!(), 2)*y_2*z*zeta_1*(one!() - power(z, 3*cap_c))*(gamma*z - one!()) - one!()*(omega*y_2 + one!()*z)*(zeta*(one!() - z)*(one!() - power(gamma*z, 3*cap_c)) - zeta_1*(one!() - power(z, 3*cap_c))*(gamma*z - one!()))) + z*(one!() - z)*(gamma*z - one!())*(power(alpha, 2)*power(z, 3*cap_c - 1)*(one!()*y_2 - power(omega/z, 3*cap_c - 1)) - power(one!(), 2)*eval_sparse_vector!(
          z,
          x.instance.0,
          x.instance.1)*y_1))/(z*(one!() - z)*(gamma*z - one!())));
        define!(
          c_23,
          -power(alpha, 4)*power(one!(), 2)*y_2*zeta);
        define!(
          c_24,
          power(z, n)*power(omega/z, 3*cap_c)*(one!() - power(omega/z, 3*cap_c - cap_c_m + 1))/(omega - one!()*z));
        define!(
          c_25,
          -power(z, -cap_d));
        define!(
          c_26,
          -z);
        define_vec_mut!(
          g_vec,
          expression_vector!(
          i,
          linear_combination_base_zero!(
          c_20,
          vector_index!(
          w_vec,
          i),
          c_21,
          vector_index!(
          pk.d_vec,
          i),
          c_23,
          vector_index!(
          pk.sigma_vec,
          i),
          c_24,
          vector_index!(
          t_vec_1,
          i),
          c_25,
          vector_index!(
          h_vec_1,
          -cap_d + i + maxshift + n),
          c_26,
          vector_index!(
          h_vec_2,
          i)),
          cap_d));
        add_to_first_item!(
          g_vec,
          c_22);
        define_commitment_linear_combination!(
          cm_g,
          vk,
          c_22,
          cm_w_vec,
          c_20,
          vk.cm_d_vec,
          c_21,
          vk.cm_sigma_vec,
          c_23,
          cm_t_vec_1,
          c_24,
          cm_h_vec_1,
          c_25,
          cm_h_vec_2,
          c_26);
        define_poly_from_vec!(
          w_vec_poly,
          w_vec);
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
          w_vec_poly,
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
          cm_w_vec,
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
          cm_w_vec,
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
    Ok(POVProof::<E> {
            cm_w_vec: cm_w_vec,
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
    let cm_w_vec = proof.cm_w_vec;
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
          cap_c,
          n,
          size);
        define!(
          n,
          3*cap_c);
        define_generator!(
          gamma,
          E);
        get_randomness_from_hash!(
          zeta,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_w_vec);
        get_randomness_from_hash!(
          zeta_1,
          scalar_to_field!(
          2),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_w_vec);
        get_randomness_from_hash!(
          alpha,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_w_vec,
          cm_r_vec);
        get_randomness_from_hash!(
          omega,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_w_vec,
          cm_r_vec,
          cm_t_vec_1);
        get_randomness_from_hash!(
          z,
          one!(),
          x.instance.0, x.instance.1,
          vk.cm_sigma_vec,
          vk.cm_d_vec,
          cm_w_vec,
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
          c_20,
          (power(alpha, 4)*one!()*(omega - one!()*z)*(omega*y_2 + one!()*z) + z*(omega - one!()*z)*(-power(alpha, 4)*power(one!(), 2)*y_2 + power(alpha, 3)*power(one!(), 2)*y_1 + y*power(z, -cap_c - cap_c_m + n)*power(omega/z, 3*cap_c - cap_c_m)) + z*(-power(alpha, 2)*one!()*z*power(omega/z, 2*cap_c + cap_c_a + cap_c_m)*(one!() - power(omega/z, cap_c - cap_c_a - cap_c_m)) - alpha*power(omega/z, 2*cap_c + cap_c_m)*(one!() - power(omega/z, cap_c_a))*(-one!()*z + power(z, cap_c + 1) + power(z, 2*cap_c + 1)) + power(z, -2*cap_c - cap_c_m + n + 1)*power(omega/z, 3*cap_c - cap_c_m)*(one!() - power(omega/z, cap_c_m))))/(z*(omega - one!()*z)));
        define!(
          c_21,
          power(alpha, 2)*power(z, 2*cap_c + cap_c_a + cap_c_m + 1)*power(omega/z, 2*cap_c + cap_c_a + cap_c_m)*(one!() - power(omega/z, cap_c - cap_c_a - cap_c_m))/(omega - one!()*z));
        define!(
          c_22,
          power(alpha, 3)*(alpha*(-power(one!(), 2)*y_2*z*zeta_1*(one!() - power(z, 3*cap_c))*(gamma*z - one!()) - one!()*(omega*y_2 + one!()*z)*(zeta*(one!() - z)*(one!() - power(gamma*z, 3*cap_c)) - zeta_1*(one!() - power(z, 3*cap_c))*(gamma*z - one!()))) + z*(one!() - z)*(gamma*z - one!())*(power(alpha, 2)*power(z, 3*cap_c - 1)*(one!()*y_2 - power(omega/z, 3*cap_c - 1)) - power(one!(), 2)*eval_sparse_vector!(
          z,
          x.instance.0,
          x.instance.1)*y_1))/(z*(one!() - z)*(gamma*z - one!())));
        define!(
          c_23,
          -power(alpha, 4)*power(one!(), 2)*y_2*zeta);
        define!(
          c_24,
          power(z, n)*power(omega/z, 3*cap_c)*(one!() - power(omega/z, 3*cap_c - cap_c_m + 1))/(omega - one!()*z));
        define!(
          c_25,
          -power(z, -cap_d));
        define!(
          c_26,
          -z);
        define_commitment_linear_combination!(
          cm_g,
          vk,
          c_22,
          cm_w_vec,
          c_20,
          vk.cm_d_vec,
          c_21,
          vk.cm_sigma_vec,
          c_23,
          cm_t_vec_1,
          c_24,
          cm_h_vec_1,
          c_25,
          cm_h_vec_2,
          c_26);
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
          cm_w_vec,
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
          cm_w_vec,
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
          cm_w_vec,
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

