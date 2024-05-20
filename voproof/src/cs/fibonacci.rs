use std::marker::PhantomData;

use super::*;

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Fibonacci<F: Field> {
  n: usize,
  _phantom: PhantomData<F>,
}

impl<F: Field> Fibonacci<F> {
  pub fn new(n: usize) -> Self {
    Fibonacci {
      n,
      _phantom: PhantomData,
    }
  }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct FibonacciSize {
  pub n: usize,
}

impl CSSize for FibonacciSize {}

impl<F: Field> ConstraintSystem<F, FibonacciSize> for Fibonacci<F> {
  fn get_size(&self) -> FibonacciSize {
    FibonacciSize { n: self.n }
  }
}

#[derive(Clone)]
pub struct FibonacciInstance<F: Field> {
  pub a: F,
  pub b: F,
  pub c: F,
}

#[derive(Clone)]
pub struct FibonacciWitness<F: Field> {
  pub witness: Vec<F>,
}

impl<F: Field> Instance<F> for FibonacciInstance<F> {}
impl<F: Field> Witness<F> for FibonacciWitness<F> {}
