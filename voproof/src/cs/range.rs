use super::*;

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct RangeCheck<F: Field> {
  pub lookup_size: usize,
  pub range: usize,
  pub _phantom: std::marker::PhantomData<F>,
}

impl<F: Field> RangeCheck<F> {
  pub fn new(lookup_size: usize, range: usize) -> Self {
    RangeCheck {
      lookup_size,
      range,
      _phantom: std::marker::PhantomData,
    }
  }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct RangeCheckSize {
  pub lookup_size: usize,
  pub range: usize,
}

impl CSSize for RangeCheckSize {}

impl<F: Field> ConstraintSystem<F, RangeCheckSize> for RangeCheck<F> {
  fn get_size(&self) -> RangeCheckSize {
    RangeCheckSize {
      lookup_size: self.lookup_size,
      range: self.range,
    }
  }
}

#[derive(Clone)]
pub struct RangeCheckInstance<F: Field> {
  phantom: std::marker::PhantomData<F>,
}

impl<F: Field> RangeCheckInstance<F> {
  pub fn new() -> Self {
    RangeCheckInstance {
      phantom: std::marker::PhantomData,
    }
  }
}

#[derive(Clone)]
pub struct RangeCheckWitness<F: Field> {
  pub witness: Vec<F>,
}

impl<F: Field> Instance<F> for RangeCheckInstance<F> {}
impl<F: Field> Witness<F> for RangeCheckWitness<F> {}
