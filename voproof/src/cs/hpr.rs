use super::*;
use crate::tools::*;
use crate::*;
use ark_ff::{Field, PrimeField};
use ark_std::{rand::RngCore, UniformRand};

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct HPR<F: Field> {
  pub arows: Vec<u64>,
  pub acols: Vec<u64>,
  pub avals: Vec<F>,
  pub brows: Vec<u64>,
  pub bcols: Vec<u64>,
  pub bvals: Vec<F>,
  pub crows: Vec<u64>,
  pub ccols: Vec<u64>,
  pub cvals: Vec<F>,
  pub drows: Vec<u64>,
  pub dvals: Vec<F>,
  pub nrows: u64,
  pub ncols: u64,
  pub input_size: u64,
}

impl<F: Field> ConstraintSystem<F, HPRSize> for HPR<F> {
  fn get_size(&self) -> HPRSize {
    let adensity = self.arows.len();
    let bdensity = self.brows.len();
    let cdensity = self.crows.len();
    assert_eq!(adensity, self.acols.len());
    assert_eq!(adensity, self.avals.len());
    assert_eq!(bdensity, self.bcols.len());
    assert_eq!(bdensity, self.bvals.len());
    assert_eq!(cdensity, self.ccols.len());
    assert_eq!(cdensity, self.cvals.len());
    let ddensity = self.drows.len();
    assert_eq!(ddensity, self.dvals.len());
    assert!(self.nrows >= ddensity as u64);
    HPRSize {
      nrows: self.nrows,
      ncols: self.ncols,
      adensity: adensity as u64,
      bdensity: adensity as u64,
      cdensity: adensity as u64,
      ddensity: ddensity as u64,
      input_size: self.input_size as u64,
    }
  }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct HPRSize {
  pub nrows: u64,
  pub ncols: u64,
  pub adensity: u64,
  pub bdensity: u64,
  pub cdensity: u64,
  pub ddensity: u64,
  pub input_size: u64,
}

impl CSSize for HPRSize {}

#[derive(Clone)]
pub struct HPRInstance<F: Field> {
  pub instance: Vec<F>,
}

#[derive(Clone)]
pub struct HPRWitness<F: Field> {
  pub witness: (Vec<F>, Vec<F>, Vec<F>),
}

impl<F: PrimeField> HPR<F> {
  pub fn satisfy(&self, ins: &HPRInstance<F>, wit: &HPRWitness<F>) -> bool {
    if !wit
      .witness
      .0
      .iter()
      .zip(wit.witness.1.iter())
      .zip(wit.witness.2.iter())
      .all(|((a, b), c)| *a * *b == *c)
    {
      return false;
    }
    let ya = sparse_mvp(
      self.nrows as i64,
      self.ncols as i64,
      &self.arows,
      &self.acols,
      &self.avals,
      &wit.witness.0,
    )
    .unwrap();
    let yb = sparse_mvp(
      self.nrows as i64,
      self.ncols as i64,
      &self.brows,
      &self.bcols,
      &self.bvals,
      &wit.witness.1,
    )
    .unwrap();
    let yc = sparse_mvp(
      self.nrows as i64,
      self.ncols as i64,
      &self.crows,
      &self.ccols,
      &self.cvals,
      &wit.witness.2,
    )
    .unwrap();
    let mut y = ya
      .iter()
      .zip(yb.iter())
      .zip(yc.iter())
      .map(|((a, b), c)| *a + *b + *c)
      .collect::<Vec<F>>();
    for (i, a) in self.drows.iter().zip(self.dvals.iter()) {
      y[*i as usize] += a;
    }
    for (i, a) in ins.instance.iter().enumerate() {
      y[i] -= a;
    }
    y.iter().all(|a| a.is_zero())
  }
}

impl<F: Field> Instance<F> for HPRInstance<F> {}
impl<F: Field> Witness<F> for HPRWitness<F> {}

pub fn generate_random_hpr_instance<F: PrimeField, R: RngCore>(
  nrows: u64,
  ncols: u64,
  input_size: u64,
  rng: &mut R,
) -> (HPR<F>, HPRInstance<F>, HPRWitness<F>) {
  let density = (nrows + ncols) * 2;
  let arows = (0..density)
    .map(|_| u64::rand(rng) % nrows)
    .collect::<Vec<u64>>();
  let brows = (0..density)
    .map(|_| u64::rand(rng) % nrows)
    .collect::<Vec<u64>>();
  let crows = (0..density)
    .map(|_| u64::rand(rng) % nrows)
    .collect::<Vec<u64>>();
  let acols = (0..density)
    .map(|_| u64::rand(rng) % ncols)
    .collect::<Vec<u64>>();
  let bcols = (0..density)
    .map(|_| u64::rand(rng) % ncols)
    .collect::<Vec<u64>>();
  let ccols = (0..density)
    .map(|_| u64::rand(rng) % ncols)
    .collect::<Vec<u64>>();
  let avals = (0..density).map(|_| F::rand(rng)).collect::<Vec<F>>();
  let bvals = (0..density).map(|_| F::rand(rng)).collect::<Vec<F>>();
  let cvals = (0..density).map(|_| F::rand(rng)).collect::<Vec<F>>();
  let x = (0..input_size).map(|_| F::rand(rng)).collect::<Vec<F>>();
  let w1 = (0..ncols).map(|_| F::rand(rng)).collect::<Vec<F>>();
  let w2 = (0..ncols).map(|_| F::rand(rng)).collect::<Vec<F>>();
  let w3 = w1
    .iter()
    .zip(w2.iter())
    .map(|(a, b)| *a * *b)
    .collect::<Vec<F>>();
  let y1 = sparse_mvp_vector!((&arows, &acols, &avals), w1, nrows, ncols);
  let y2 = sparse_mvp_vector!((&brows, &bcols, &bvals), w2, nrows, ncols);
  let y3 = sparse_mvp_vector!((&crows, &ccols, &cvals), w3, nrows, ncols);
  let d = y1
    .iter()
    .zip(y2.iter())
    .zip(y3.iter())
    .enumerate()
    .map(|(i, ((a, b), c))| {
      if i < x.len() {
        -*a - b - c + x[i]
      } else {
        -*a - b - c
      }
    })
    .collect::<Vec<F>>();
  let drows = d
    .iter()
    .enumerate()
    .filter(|(_, a)| !a.is_zero())
    .map(|(i, _)| i as u64)
    .collect::<Vec<u64>>();
  let dvals = d
    .iter()
    .enumerate()
    .filter(|(_, a)| !a.is_zero())
    .map(|(_, a)| *a)
    .collect::<Vec<F>>();

  (
    HPR {
      arows,
      acols,
      avals,
      brows,
      bcols,
      bvals,
      crows,
      ccols,
      cvals,
      drows,
      dvals,
      nrows,
      ncols,
      input_size,
    },
    HPRInstance { instance: x },
    HPRWitness {
      witness: (w1, w2, w3),
    },
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_bls12_381::Fr;
  use ark_std::{test_rng, One};

  #[test]
  fn test_generate_random_hpr_instance() {
    let rng = &mut test_rng();
    let (hpr, ins, wit): (HPR<Fr>, HPRInstance<Fr>, HPRWitness<Fr>) =
      generate_random_hpr_instance(5, 10, 2, rng);
    assert!(hpr.satisfy(&ins, &wit));
    let (hpr, ins, wit): (HPR<Fr>, HPRInstance<Fr>, HPRWitness<Fr>) =
      generate_random_hpr_instance(10, 5, 3, rng);
    assert!(hpr.satisfy(&ins, &wit));
    let (hpr, mut ins, wit): (HPR<Fr>, HPRInstance<Fr>, HPRWitness<Fr>) =
      generate_random_hpr_instance(50, 50, 30, rng);
    assert!(hpr.satisfy(&ins, &wit));
    ins.instance[0] += Fr::one();
    assert!(!hpr.satisfy(&ins, &wit));
  }
}
