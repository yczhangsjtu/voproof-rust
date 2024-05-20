use super::*;

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Fibonacci<F: Field> {
  pub n: usize,
  pub t: Vec<F>,
}

impl<F: Field> Fibonacci<F> {
  pub fn new(n: usize, t: Vec<F>) -> Self {
    Fibonacci { n, t }
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
