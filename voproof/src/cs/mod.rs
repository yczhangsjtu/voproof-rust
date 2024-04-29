use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

pub trait CSSize {}
pub trait ConstraintSystem<F: Field, S: CSSize> {
  fn get_size(&self) -> S;
}
pub trait Instance<F: Field> {}
pub trait Witness<F: Field> {}

pub mod circuit;
pub mod hpr;
pub mod pov;
pub mod r1cs;
