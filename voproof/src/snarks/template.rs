use super::*;

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct __NAME__ProverKey<E: PairingEngine> {
  pub verifier_key: __NAME__VerifierKey<E>,
  pub powers: Vec<E::G1Affine>,
  pub max_degree: u64,
  /*{ProverKey}*/
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct __NAME__VerifierKey<E: PairingEngine> {
  /*{VerifierKey}*/
  pub kzg_vk: VerifierKey<E>,
  pub size: __CSNAME__Size,
  pub degree_bound: u64,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct __NAME__Proof<E: PairingEngine> {/*{Proof}*/}

pub struct VOProof__NAME__ {}

impl<E: PairingEngine> SNARKProverKey<E> for __NAME__ProverKey<E> {}

impl<E: PairingEngine> SNARKVerifierKey<E> for __NAME__VerifierKey<E> {}

impl<E: PairingEngine> SNARKProof<E> for __NAME__Proof<E> {}

impl VOProof__NAME__ {
  pub fn get_max_degree(size: __CSNAME__Size) -> usize {
    /*{size}*/
  }
}

impl<E: PairingEngine> SNARK<E> for VOProof__NAME__ {
  type Size = __CSNAME__Size;
  type CS = __CSNAME__<E::Fr>;
  type PK = __NAME__ProverKey<E>;
  type VK = __NAME__VerifierKey<E>;
  type Ins = __CSNAME__Instance<E::Fr>;
  type Wit = __CSNAME__Witness<E::Fr>;
  type Pf = __NAME__Proof<E>;

  fn setup(size: usize) -> Result<UniversalParams<E>, Error> {
    let rng = &mut test_rng();
    KZG10::<E, DensePoly<E::Fr>>::setup(size, rng)
  }

  fn index(
    pp: &UniversalParams<E>,
    cs: &__CSNAME__<E::Fr>,
  ) -> Result<(__NAME__ProverKey<E>, __NAME__VerifierKey<E>), Error> {
    let max_degree = Self::get_max_degree(cs.get_size());
    let cap_d = pp.powers_of_g.len();
    assert!(cap_d > max_degree);

    let powers_of_g = pp.powers_of_g[..].to_vec();
    let size = cs.get_size();
    /*{index}*/
    let verifier_key = __NAME__VerifierKey::<E> {
      /*{index verifier key}*/
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
      __NAME__ProverKey::<E> {
        verifier_key: verifier_key.clone(),
        powers: powers_of_g,
        max_degree: max_degree as u64,
        /*{index prover key}*/
      },
      verifier_key,
    ))
  }
  fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error> {
    let size = pk.verifier_key.size.clone();
    let vk = pk.verifier_key.clone();
    let cap_d = pk.verifier_key.degree_bound as i64;
    let rng = &mut test_rng();
    /*{prove}*/
    let (cap_w, cap_w_1) = KZG10::batch_open(&pk.powers, &fs, &gs, &z1, &z2, &rand_xi, &rand_xi_2)?;
    Ok(__NAME__Proof::<E> {
            /*{proof}*/
        })
  }
  fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error> {
    let size = vk.size.clone();
    let cap_d = vk.degree_bound as i64;
    let rng = &mut test_rng();
    /*{verify}*/
    if KZG10::<E, DensePoly<E::Fr>>::batch_check(
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
