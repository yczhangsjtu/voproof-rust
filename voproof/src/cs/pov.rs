use super::circuit::fan_in_two::FanInTwoCircuit;
use super::r1cs::{R1CSInstance, R1CSWitness, R1CS};
use super::*;

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct POV<F: Field> {
  pub consts: Vec<F>,
  pub wires: Vec<(u64, u64)>,
  pub nmul: u64,
  pub nadd: u64,
}

impl<F: Field> ConstraintSystem<F, POVSize> for POV<F> {
  fn get_size(&self) -> POVSize {
    POVSize {
      nconsts: self.consts.len() as u64,
      nmul: self.nmul,
      nadd: self.nadd,
      n: self.consts.len() as u64 + self.nmul + self.nadd,
    }
  }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct POVSize {
  pub nconsts: u64,
  pub nmul: u64,
  pub nadd: u64,
  pub n: u64,
}

impl CSSize for POVSize {}

#[derive(Debug, Clone)]
pub struct POVInstance<F: Field> {
  pub instance: (Vec<u64>, Vec<F>),
}

#[derive(Debug, Clone)]
pub struct POVWitness<F: Field> {
  pub witness: (Vec<F>, Vec<F>, Vec<F>),
}

impl<F: Field> Instance<F> for POVInstance<F> {}
impl<F: Field> Witness<F> for POVWitness<F> {}

impl<F: Field> POVWitness<F> {
  pub fn get_value_at(&self, index: usize) -> Option<F> {
    let wit = &self.witness;
    match index {
      _ if index < wit.0.len() => Some(wit.0[index]),
      _ if index < wit.0.len() + wit.1.len() => Some(wit.1[index - wit.0.len()]),
      _ if index < wit.0.len() + wit.1.len() + wit.2.len() => {
        Some(wit.2[index - wit.0.len() - wit.1.len()])
      }
      _ => None,
    }
  }

  pub fn satisfy_instance(&self, ins: &POVInstance<F>) -> bool {
    for (i, v) in ins.instance.0.iter().zip(ins.instance.1.iter()) {
      if let Some(u) = self.get_value_at(*i as usize) {
        if u != *v {
          return false;
        }
      } else {
        return false;
      }
    }
    true
  }
}

impl<F: Field> From<FanInTwoCircuit<F>> for POV<F> {
  fn from(circuit: FanInTwoCircuit<F>) -> POV<F> {
    POV {
      consts: circuit.get_consts(),
      wires: circuit.get_wiring().unwrap(),
      nmul: circuit.get_mul_num() as u64,
      nadd: circuit.get_add_num() as u64,
    }
  }
}

impl<F: Field> POV<F> {
  pub fn satisfy(&self, ins: &POVInstance<F>, wit: &POVWitness<F>) -> bool {
    self.satisfy_gate_logics(wit) && self.satisfy_wiring(wit) && wit.satisfy_instance(ins)
  }

  pub fn satisfy_gate_logics(&self, wit: &POVWitness<F>) -> bool {
    let size = self.get_size();
    for (i, ((a, b), c)) in wit
      .witness
      .0
      .iter()
      .zip(wit.witness.1.iter())
      .zip(wit.witness.2.iter())
      .enumerate()
    {
      match i {
        _ if (i as u64) < size.nmul => {
          if *c != *a * *b {
            return false;
          }
        }
        _ if (i as u64) < size.nmul + size.nadd => {
          if *c != *a + *b {
            return false;
          }
        }
        _ => {
          if *c != self.consts[i - (size.nmul + size.nadd) as usize] {
            return false;
          }
        }
      }
    }
    true
  }

  pub fn satisfy_wiring(&self, wit: &POVWitness<F>) -> bool {
    for (i, j) in self.wires.iter() {
      if let (Some(a), Some(b)) = (wit.get_value_at(*i as usize), wit.get_value_at(*j as usize)) {
        if a != b {
          return false;
        }
      } else {
        return false;
      }
    }
    true
  }
}

pub fn pov_pair_from_r1cs_pair<F: Field>(
  r1cs: R1CS<F>,
  instance: R1CSInstance<F>,
) -> (POV<F>, POVInstance<F>) {
  let mut circ = FanInTwoCircuit::from(r1cs);
  circ.assign_public_io(&instance.instance).unwrap();
  let x = circ.get_instance().unwrap();
  (POV::from(circ), POVInstance { instance: x })
}

pub fn pov_triple_from_r1cs_triple<F: Field>(
  r1cs: R1CS<F>,
  instance: R1CSInstance<F>,
  witness: R1CSWitness<F>,
) -> (POV<F>, POVInstance<F>, POVWitness<F>) {
  let mut circ = FanInTwoCircuit::from(r1cs);
  let input = instance
    .instance
    .into_iter()
    .chain(witness.witness.into_iter())
    .collect();
  circ.evaluate(&input).unwrap();
  let x = circ.get_instance().unwrap();
  let w = circ.get_witness().unwrap();

  (
    POV::from(circ),
    POVInstance { instance: x },
    POVWitness { witness: w },
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::tools::*;
  use crate::*;
  use ark_bls12_381::Bls12_381 as E;
  use ark_ec::pairing::Pairing as PairingEngine;

  #[test]
  fn test_satisfy() {
    _test_satisfy::<E>();
  }

  fn _test_satisfy<E: PairingEngine>() {
    let mut circ = FanInTwoCircuit::<E::ScalarField>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    let o = circ.const_var(to_field::<E::ScalarField>(10));
    let p = circ.mul_vars(&h, &o);
    circ.mark_as_complete().unwrap();
    circ.mark_variable_as_public(&a).unwrap();
    circ.mark_variable_as_public(&p).unwrap();
    circ
      .evaluate(&vec![
        to_field::<E::ScalarField>(1),
        to_field::<E::ScalarField>(2),
        to_field::<E::ScalarField>(3),
      ])
      .unwrap();
    let ins = POVInstance {
      instance: circ.get_instance().unwrap(),
    };
    let wit = POVWitness {
      witness: circ.get_witness().unwrap(),
    };
    println!("{:?}", ins.instance.0);
    println!("{}", fmt_ff_vector!(ins.instance.1));
    println!("{}", fmt_ff_vector!(wit.witness.0));
    println!("{}", fmt_ff_vector!(wit.witness.1));
    println!("{}", fmt_ff_vector!(wit.witness.2));
    println!("{:?}", circ.get_wiring());
    assert_eq!(circ.get_add_num(), 2);
    assert_eq!(circ.get_mul_num(), 4);
    assert_eq!(circ.get_const_num(), 1);
    assert_eq!(wit.witness.0.len(), 7);
    assert_eq!(wit.witness.1.len(), 7);
    assert_eq!(wit.witness.2.len(), 7);
    let pov = POV::from(circ);
    let size = pov.get_size();
    assert_eq!(size.nadd, 2);
    assert_eq!(size.nmul, 4);
    assert_eq!(size.nconsts, 1);
    assert_eq!(size.n, 7);
    assert!(pov.satisfy_gate_logics(&wit));
    assert!(pov.satisfy_wiring(&wit));
    assert!(wit.satisfy_instance(&ins));
    assert!(pov.satisfy(&ins, &wit));
  }
}
