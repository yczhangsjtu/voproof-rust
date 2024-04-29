use crate::error::Error;
use ark_std::collections::HashMap;
use ark_std::fmt::Debug;
use ark_std::ops::{Add, Mul};

pub struct FanInTwoCircuit<F: Add<F, Output = F> + Mul<F, Output = F> + Clone + Debug> {
  add_gates: Vec<AddGate>,
  mul_gates: Vec<MulGate>,
  const_gates: Vec<ConstGate<F>>,
  public_io_wires: Vec<GateWire>,
  num_global_input_variables: usize,
  global_output_variables: Vec<VariableRef>,
  variables: Vec<Variable<F>>,
  assert_equals: Vec<(VariableRef, VariableRef)>,
  add_vars_cache: HashMap<(VariableRef, VariableRef), VariableRef>,
  mul_vars_cache: HashMap<(VariableRef, VariableRef), VariableRef>,
  const_vars_cache: HashMap<String, VariableRef>,
}

#[derive(Clone, Debug)]
pub struct AddGate {
  left: VariableRef,
  right: VariableRef,
  output: VariableRef,
}

#[derive(Clone)]
pub struct MulGate {
  left: VariableRef,
  right: VariableRef,
  output: VariableRef,
}

#[derive(Clone)]
pub struct ConstGate<F> {
  output: VariableRef,
  value: F,
}

pub enum Gate<F: Add<F, Output = F> + Mul<F, Output = F> + Clone> {
  AddGate(AddGate),
  MulGate(MulGate),
  ConstGate(ConstGate<F>),
}

#[derive(Clone, Debug)]
pub enum GateRef {
  Add(usize),
  Mul(usize),
  Const(usize),
}

impl GateRef {
  pub fn get_index(&self) -> usize {
    match self {
      Self::Add(index) => index.clone(),
      Self::Mul(index) => index.clone(),
      Self::Const(index) => index.clone(),
    }
  }
}

#[derive(Clone, Debug)]
pub enum InputWireType {
  Left,
  Right,
}

#[derive(Clone, Debug)]
pub enum WireType {
  Input(InputWireType),
  Output,
}

#[derive(Clone, Debug)]
pub enum InputGateWire {
  Add(usize, InputWireType),
  Mul(usize, InputWireType),
}

#[derive(Clone, Debug)]
pub enum OutputGateWire {
  Add(usize),
  Mul(usize),
  Const(usize),
}

#[derive(Clone, Debug)]
pub enum GateWire {
  Input(InputGateWire),
  Output(OutputGateWire),
}

impl GateWire {
  pub fn get_gate(&self) -> GateRef {
    match self {
      Self::Input(wire) => match wire {
        InputGateWire::Add(index, _) => GateRef::Add(index.clone()),
        InputGateWire::Mul(index, _) => GateRef::Mul(index.clone()),
      },
      Self::Output(wire) => match wire {
        OutputGateWire::Add(index) => GateRef::Add(index.clone()),
        OutputGateWire::Mul(index) => GateRef::Mul(index.clone()),
        OutputGateWire::Const(index) => GateRef::Const(index.clone()),
      },
    }
  }
}

impl From<InputGateWire> for GateWire {
  fn from(wire: InputGateWire) -> Self {
    GateWire::Input(wire)
  }
}

impl From<OutputGateWire> for GateWire {
  fn from(wire: OutputGateWire) -> Self {
    GateWire::Output(wire)
  }
}

#[derive(Debug)]
pub struct Variable<F: Add<F, Output = F> + Mul<F, Output = F> + Clone + Debug> {
  input_wires: Vec<InputGateWire>,
  output_wire: Option<OutputGateWire>,
  value: Option<F>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct VariableRef {
  index: usize,
}

impl<F: Add<F, Output = F> + Mul<F, Output = F> + Clone + Debug + Default> FanInTwoCircuit<F> {
  pub fn new() -> Self {
    FanInTwoCircuit::<F> {
      add_gates: Vec::new(),
      mul_gates: Vec::new(),
      const_gates: Vec::new(),
      public_io_wires: Vec::new(),
      num_global_input_variables: 0,
      global_output_variables: Vec::new(),
      variables: Vec::new(),
      assert_equals: Vec::new(),
      add_vars_cache: HashMap::new(),
      mul_vars_cache: HashMap::new(),
      const_vars_cache: HashMap::new(),
    }
  }

  pub fn get_add_num(&self) -> usize {
    self.add_gates.len()
  }

  pub fn get_mul_num(&self) -> usize {
    self.mul_gates.len()
  }

  pub fn get_const_num(&self) -> usize {
    self.const_gates.len()
  }

  pub fn get_gate_num(&self) -> usize {
    self.get_add_num() + self.get_mul_num() + self.get_const_num()
  }

  pub fn get_consts(&self) -> Vec<F> {
    self
      .const_gates
      .iter()
      .map(|gate| gate.value.clone())
      .collect()
  }

  pub fn get_wiring(&self) -> Result<Vec<(u64, u64)>, Error> {
    self.assert_complete()?;
    let mut ret = Vec::new();
    for var in self.variables.iter() {
      if var.get_wire_num() <= 1 {
        continue;
      }
      let mut indices = var
        .input_wires
        .iter()
        .map(|wire| self.get_wire_global_index(&GateWire::Input(wire.clone())))
        .collect::<Vec<usize>>();
      if let Some(wire) = var.get_output_wire() {
        indices.push(self.get_wire_global_index(&GateWire::Output(wire)));
      }
      for idxes in indices.windows(2) {
        ret.push((idxes[0] as u64, idxes[1] as u64));
      }
    }

    for (a, b) in self.assert_equals.iter() {
      let a = if let Some(a) = self.get_var(a).try_get_any_wire() {
        a
      } else {
        return Err(Error::ConnectedVariablesDoNotHaveWire);
      };
      let b = if let Some(b) = self.get_var(b).try_get_any_wire() {
        b
      } else {
        return Err(Error::ConnectedVariablesDoNotHaveWire);
      };
      ret.push((
        self.get_wire_global_index(&a) as u64,
        self.get_wire_global_index(&b) as u64,
      ));
    }
    Ok(ret)
  }

  pub fn get_var_mut<'a>(&'a mut self, var: &VariableRef) -> &'a mut Variable<F> {
    &mut self.variables[var.index]
  }

  pub fn get_var<'a>(&'a self, var: &VariableRef) -> &'a Variable<F> {
    &self.variables[var.index]
  }

  pub fn try_get_var_value(&self, var: &VariableRef) -> Option<F> {
    self.get_var(var).try_get_value()
  }

  pub fn get_var_value_str_or_empty(&self, var: &VariableRef) -> String {
    if let Some(v) = self.try_get_var_value(var) {
      format!("{:?}", v)
    } else {
      String::from("")
    }
  }

  pub fn get_var_value(&self, var: &VariableRef) -> Result<F, Error> {
    if let Some(v) = self.try_get_var_value(var) {
      Ok(v)
    } else {
      Err(Error::VariableNotSet(var.index.clone()))
    }
  }

  pub fn get_wire_value(&self, wire: &GateWire) -> Result<F, Error> {
    return self.get_var_value(&self.get_var_from_wire(wire));
  }

  pub fn set_var(&mut self, var: &VariableRef, value: F) {
    self.get_var_mut(var).assign(&value);
  }

  pub fn get_gate(&self, gate: &GateRef) -> Gate<F> {
    match gate {
      GateRef::Add(index) => Gate::AddGate(self.add_gates[index.clone()].clone()),
      GateRef::Mul(index) => Gate::MulGate(self.mul_gates[index.clone()].clone()),
      GateRef::Const(index) => Gate::ConstGate(self.const_gates[index.clone()].clone()),
    }
  }

  pub fn add_new_variable(&mut self) -> VariableRef {
    self.variables.push(Variable::new());
    VariableRef {
      index: self.variables.len() - 1,
    }
  }

  pub fn assert_no_gate(&mut self) -> Result<(), Error> {
    if self.add_gates.is_empty() && self.mul_gates.is_empty() && self.const_gates.is_empty() {
      Ok(())
    } else {
      Err(Error::GatesAreNotEmpty)
    }
  }

  pub fn add_global_input_variable(&mut self) -> Result<VariableRef, Error> {
    self.assert_no_gate()?;
    let ret = self.add_new_variable();
    self.num_global_input_variables += 1;
    Ok(ret)
  }

  pub fn add_add_gate(
    &mut self,
    a: &VariableRef,
    b: &VariableRef,
    c: &VariableRef,
  ) -> Result<(), Error> {
    self.add_gates.push(AddGate {
      left: a.clone(),
      right: b.clone(),
      output: c.clone(),
    });
    let gate_index = self.add_gates.len() - 1;
    self
      .get_var_mut(a)
      .add_add_gate(gate_index, WireType::Input(InputWireType::Left))?;
    self
      .get_var_mut(b)
      .add_add_gate(gate_index, WireType::Input(InputWireType::Right))?;
    self
      .get_var_mut(c)
      .add_add_gate(gate_index, WireType::Output)?;
    Ok(())
  }

  pub fn add_mul_gate(
    &mut self,
    a: &VariableRef,
    b: &VariableRef,
    c: &VariableRef,
  ) -> Result<(), Error> {
    self.mul_gates.push(MulGate {
      left: a.clone(),
      right: b.clone(),
      output: c.clone(),
    });
    let gate_index = self.mul_gates.len() - 1;
    self
      .get_var_mut(a)
      .add_mul_gate(gate_index, WireType::Input(InputWireType::Left))?;
    self
      .get_var_mut(b)
      .add_mul_gate(gate_index, WireType::Input(InputWireType::Right))?;
    self
      .get_var_mut(c)
      .add_mul_gate(gate_index, WireType::Output)?;
    Ok(())
  }

  pub fn add_const_gate(&mut self, c: F, var: &VariableRef) -> Result<(), Error> {
    self.const_gates.push(ConstGate {
      output: var.clone(),
      value: c,
    });
    let gate_index = self.const_gates.len() - 1;
    self.get_var_mut(var).add_const_gate(gate_index)?;
    Ok(())
  }

  pub fn add_vars(&mut self, a: &VariableRef, b: &VariableRef) -> VariableRef {
    let (a, b) = if a < b { (a, b) } else { (b, a) };
    let cached = self.add_vars_cache.get(&(a.clone(), b.clone()));
    if let Some(var) = cached {
      var.clone()
    } else {
      let ret = self.add_new_variable();
      self.add_add_gate(a, b, &ret).unwrap();
      self.add_vars_cache.insert((a.clone(), b.clone()), ret.clone());
      ret
    }
  }

  pub fn mul_vars(&mut self, a: &VariableRef, b: &VariableRef) -> VariableRef {
    let (a, b) = if a < b { (a, b) } else { (b, a) };
    let cached = self.mul_vars_cache.get(&(a.clone(), b.clone()));
    if let Some(var) = cached {
      var.clone()
    } else {
      let ret = self.add_new_variable();
      self.add_mul_gate(a, b, &ret).unwrap();
      self.mul_vars_cache.insert((a.clone(), b.clone()), ret.clone());
      ret
    }
  }

  pub fn const_var(&mut self, c: F) -> VariableRef {
    let key = format!("{:?}", c);
    let cached = self.const_vars_cache.get(&key);
    if let Some(var) = cached {
      var.clone()
    } else {
      let ret = self.add_new_variable();
      self.add_const_gate(c, &ret).unwrap();
      self.const_vars_cache.insert(key, ret.clone());
      ret
    }
  }

  pub fn eval_gate(&mut self, gate: &GateRef) -> Result<(), Error> {
    let gate = self.get_gate(gate);
    match gate {
      Gate::AddGate(gate) => self.set_var(
        &gate.output,
        self.get_var_value(&gate.left)? + self.get_var_value(&gate.right)?,
      ),
      Gate::MulGate(gate) => self.set_var(
        &gate.output,
        self.get_var_value(&gate.left)? * self.get_var_value(&gate.right)?,
      ),
      Gate::ConstGate(gate) => self.set_var(&gate.output, gate.value),
    }
    Ok(())
  }

  pub fn mark_as_complete(&mut self) -> Result<(), Error> {
    if self.num_global_input_variables == 0 {
      return Err(Error::CircuitHasNoGlobalInput);
    }
    for (i, var) in self.variables.iter().enumerate() {
      if !var.is_gate_input() && !var.is_gate_output() {
        return Err(Error::VariableNotConnected(i));
      }
      if !var.is_gate_input() {
        self.global_output_variables.push(VariableRef { index: i });
      }
    }
    if !self.is_complete() {
      return Err(Error::AllVariablesAreInputs);
    }
    Ok(())
  }

  pub fn is_complete(&self) -> bool {
    !self.global_output_variables.is_empty()
  }

  pub fn assert_complete(&self) -> Result<(), Error> {
    if !self.is_complete() {
      return Err(Error::CircuitNotComplete);
    }
    Ok(())
  }

  pub fn assert_input_size(&self, input_size: usize) -> Result<(), Error> {
    let expected = self.get_input_size()?;
    if expected != input_size {
      Err(Error::InputSizeNotSupported(expected, input_size))
    } else {
      Ok(())
    }
  }

  pub fn assert_io_size(&self, input_size: usize) -> Result<(), Error> {
    let expected = self.get_io_size()?;
    if expected != input_size {
      Err(Error::InputSizeNotSupported(expected, input_size))
    } else {
      Ok(())
    }
  }

  pub fn mark_wire_as_public(&mut self, gate_wire: &GateWire) {
    self.public_io_wires.push(gate_wire.clone());
  }

  pub fn mark_variable_as_public(&mut self, var: &VariableRef) -> Result<(), Error> {
    // If this variable is an output, then mark the corresponding output wire
    if self.get_var(var).is_gate_output() {
      self.mark_wire_as_public(&self.get_var(var).try_get_output_wire().unwrap().into());
    } else {
      // Otherwise, find arbitrary input wire this variable is assigned to
      self.mark_wire_as_public(&self.get_var(var).try_get_input_wire().unwrap().into());
    }
    Ok(())
  }

  pub fn assign_global_inputs(&mut self, input: &Vec<F>) -> Result<(), Error> {
    self.assert_input_size(input.len())?;
    for (a, var) in input
      .iter()
      .zip(self.variables.iter_mut().take(input.len()))
    {
      var.assign(&a);
    }
    Ok(())
  }

  pub fn get_var_from_wire(&self, wire: &GateWire) -> VariableRef {
    match wire {
      GateWire::Input(InputGateWire::Add(index, InputWireType::Left)) => {
        self.add_gates[index.clone()].left.clone()
      }
      GateWire::Input(InputGateWire::Add(index, InputWireType::Right)) => {
        self.add_gates[index.clone()].right.clone()
      }
      GateWire::Input(InputGateWire::Mul(index, InputWireType::Left)) => {
        self.mul_gates[index.clone()].left.clone()
      }
      GateWire::Input(InputGateWire::Mul(index, InputWireType::Right)) => {
        self.mul_gates[index.clone()].right.clone()
      }
      GateWire::Output(OutputGateWire::Add(index)) => self.add_gates[index.clone()].output.clone(),
      GateWire::Output(OutputGateWire::Mul(index)) => self.mul_gates[index.clone()].output.clone(),
      GateWire::Output(OutputGateWire::Const(index)) => {
        self.const_gates[index.clone()].output.clone()
      }
    }
  }

  pub fn assign_public_io(&mut self, input: &Vec<F>) -> Result<(), Error> {
    self.assert_io_size(input.len())?;
    for (a, wire) in input.iter().zip(self.public_io_wires.clone().iter()) {
      self
        .get_var_mut(&self.get_var_from_wire(wire))
        .assign_no_overwrite(a)?;
    }
    Ok(())
  }

  pub fn evaluate(&mut self, input: &Vec<F>) -> Result<(), Error> {
    self.assign_global_inputs(input)?;
    // We assume that the variables are in topological order, i.e.,
    // if a variable a depends on a variable b, then b should be ordered
    // before a.
    for i in input.len()..self.variables.len() {
      if let Some(gate) = self.variables[i].get_outputing_gate() {
        self.eval_gate(&gate)?
      } else {
        return Err(Error::VariableIsNotOutput(i));
      }
    }
    Ok(())
  }

  pub fn get_input_size(&self) -> Result<usize, Error> {
    self.assert_complete()?;
    Ok(self.num_global_input_variables)
  }

  pub fn get_io_size(&self) -> Result<usize, Error> {
    self.assert_complete()?;
    Ok(self.public_io_wires.len())
  }

  pub fn get_output(&self) -> Result<Vec<F>, Error> {
    self
      .global_output_variables
      .iter()
      .map(|var| -> Result<F, Error> { self.get_var_value(&var) })
      .collect()
  }

  pub fn get_output_size(&self) -> usize {
    self.global_output_variables.len()
  }

  // Get the offset of this wire in the entire string from its gate index
  // consisting of (left mul || left add || left const || right ... || output ...)
  pub fn get_offset(&self, wire: &GateWire) -> usize {
    match wire {
      GateWire::Input(InputGateWire::Add(_, InputWireType::Left)) => self.get_mul_num(),
      GateWire::Input(InputGateWire::Add(_, InputWireType::Right)) => {
        self.get_gate_num() + self.get_mul_num()
      }
      GateWire::Input(InputGateWire::Mul(_, InputWireType::Left)) => 0,
      GateWire::Input(InputGateWire::Mul(_, InputWireType::Right)) => self.get_gate_num(),
      GateWire::Output(OutputGateWire::Add(_)) => self.get_gate_num() * 2 + self.get_mul_num(),
      GateWire::Output(OutputGateWire::Mul(_)) => self.get_gate_num() * 2,
      GateWire::Output(OutputGateWire::Const(_)) => self.get_gate_num() * 3 - self.get_const_num(),
    }
  }

  pub fn get_wire_global_index(&self, wire: &GateWire) -> usize {
    wire.get_gate().get_index() + self.get_offset(&wire)
  }

  pub fn get_instance(&self) -> Result<(Vec<u64>, Vec<F>), Error> {
    Ok((
      self
        .public_io_wires
        .iter()
        .map(|wire| self.get_wire_global_index(&wire) as u64)
        .collect(),
      self
        .public_io_wires
        .iter()
        .map(|wire| -> Result<F, Error> { self.get_wire_value(wire) })
        .collect::<Result<Vec<F>, Error>>()?,
    ))
  }

  pub fn get_witness(&self) -> Result<(Vec<F>, Vec<F>, Vec<F>), Error> {
    Ok((
      self
        .mul_gates
        .iter()
        .map(|gate| self.get_var_value(&gate.left))
        .chain(
          self
            .add_gates
            .iter()
            .map(|gate| self.get_var_value(&gate.left)),
        )
        .chain((0..self.get_const_num()).map(|_| Ok(F::default())))
        .collect::<Result<Vec<F>, Error>>()?,
      self
        .mul_gates
        .iter()
        .map(|gate| self.get_var_value(&gate.right))
        .chain(
          self
            .add_gates
            .iter()
            .map(|gate| self.get_var_value(&gate.right)),
        )
        .chain((0..self.get_const_num()).map(|_| Ok(F::default())))
        .collect::<Result<Vec<F>, Error>>()?,
      self
        .mul_gates
        .iter()
        .map(|gate| self.get_var_value(&gate.output))
        .chain(
          self
            .add_gates
            .iter()
            .map(|gate| self.get_var_value(&gate.output)),
        )
        .chain(
          self
            .const_gates
            .iter()
            .map(|gate| self.get_var_value(&gate.output)),
        )
        .collect::<Result<Vec<F>, Error>>()?,
    ))
  }

  // Must be careful when using this function. Double check that the two
  // input variables are not connected by other links already. Otherwise
  // the resulting POV relation might be invalid
  pub fn assert_equal(&mut self, a: &VariableRef, b: &VariableRef) -> Result<(), Error> {
    if a == b {
      return Err(Error::TryingToConnectTheSameVariable);
    }
    self.assert_equals.push((a.clone(), b.clone()));
    Ok(())
  }
}

impl<F: Add<F, Output = F> + Mul<F, Output = F> + Clone + Debug + Default> core::fmt::Display
  for FanInTwoCircuit<F>
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    for g in self.add_gates.iter() {
      write!(
        f,
        "Var({}) {:?} + Var({}) {:?} = Var({}) {:?}\n",
        g.left.index,
        self.get_var_value_str_or_empty(&g.left),
        g.right.index,
        self.get_var_value_str_or_empty(&g.right),
        g.output.index,
        self.get_var_value_str_or_empty(&g.output),
      )?;
    }
    for g in self.mul_gates.iter() {
      write!(
        f,
        "Var({}) {:?} * Var({}) {:?} = Var({}) {:?}\n",
        g.left.index,
        self.get_var_value_str_or_empty(&g.left),
        g.right.index,
        self.get_var_value_str_or_empty(&g.right),
        g.output.index,
        self.get_var_value_str_or_empty(&g.output),
      )?;
    }
    Ok(())
  }
}

impl<F: Add<F, Output = F> + Mul<F, Output = F> + Clone + Debug> Variable<F> {
  pub fn new() -> Self {
    Variable::<F> {
      input_wires: Vec::new(),
      output_wire: None,
      value: None,
    }
  }

  pub fn get_wire_num(&self) -> usize {
    self.input_wires.len() + if self.is_gate_output() { 1 } else { 0 }
  }

  pub fn assign(&mut self, v: &F) {
    self.value = Some(v.clone());
  }

  pub fn assign_no_overwrite(&mut self, v: &F) -> Result<(), Error> {
    if self.value.is_none() {
      self.value = Some(v.clone());
      Ok(())
    } else {
      Err(Error::VariableAlreadySet(format!("{:?}", v)))
    }
  }

  pub fn try_get_value(&self) -> Option<F> {
    self.value.clone()
  }

  pub fn get_value(&self) -> Result<F, Error> {
    if let Some(v) = self.value.clone() {
      Ok(v.clone())
    } else {
      Err(Error::VariableNotSet(0))
    }
  }

  pub fn try_get_output_wire(&self) -> Option<OutputGateWire> {
    self.output_wire.clone()
  }

  pub fn try_get_input_wire(&self) -> Option<InputGateWire> {
    if self.input_wires.is_empty() {
      None
    } else {
      Some(self.input_wires[0].clone())
    }
  }

  pub fn try_get_any_wire(&self) -> Option<GateWire> {
    if let Some(wire) = self.try_get_input_wire() {
      Some(GateWire::Input(wire))
    } else if let Some(wire) = self.try_get_output_wire() {
      Some(GateWire::Output(wire))
    } else {
      None
    }
  }

  pub fn add_add_gate(&mut self, index: usize, wire_type: WireType) -> Result<(), Error> {
    match wire_type {
      WireType::Input(input_wire_type) => self
        .input_wires
        .push(InputGateWire::Add(index, input_wire_type)),
      WireType::Output => {
        self.assert_not_output()?;
        self.output_wire = Some(OutputGateWire::Add(index));
      }
    };
    Ok(())
  }

  pub fn add_mul_gate(&mut self, index: usize, wire_type: WireType) -> Result<(), Error> {
    match wire_type {
      WireType::Input(input_wire_type) => self
        .input_wires
        .push(InputGateWire::Mul(index, input_wire_type)),
      WireType::Output => {
        self.assert_not_output()?;
        self.output_wire = Some(OutputGateWire::Mul(index));
      }
    }
    Ok(())
  }

  pub fn add_const_gate(&mut self, index: usize) -> Result<(), Error> {
    self.assert_not_output()?;
    self.output_wire = Some(OutputGateWire::Const(index));
    Ok(())
  }

  pub fn is_gate_input(&self) -> bool {
    !self.input_wires.is_empty()
  }

  pub fn is_gate_output(&self) -> bool {
    self.output_wire.is_some()
  }

  pub fn get_output_wire(&self) -> Option<OutputGateWire> {
    self.output_wire.clone()
  }

  pub fn assert_not_output(&self) -> Result<(), Error> {
    if self.is_gate_output() {
      Err(Error::VariableAlreadySetAsOutput)
    } else {
      Ok(())
    }
  }

  pub fn get_outputing_gate(&self) -> Option<GateRef> {
    if let Some(gate_wire) = self.output_wire.clone() {
      match gate_wire {
        OutputGateWire::Add(index) => Some(GateRef::Add(index)),
        OutputGateWire::Mul(index) => Some(GateRef::Mul(index)),
        OutputGateWire::Const(index) => Some(GateRef::Const(index)),
      }
    } else {
      None
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::tools::*;
  use ark_bls12_377::Fr as F;

  #[test]
  fn test_simple_circuit() {
    let mut circ = FanInTwoCircuit::<i32>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    assert!(circ.get_var(&h).is_gate_output());
    circ.mark_as_complete().unwrap();
    assert_eq!(circ.get_output_size(), 1);
    circ.evaluate(&vec![1, 2, 3]).unwrap();
    assert_eq!(circ.get_var(&a).try_get_value().unwrap(), 1);
    assert_eq!(circ.get_var(&b).try_get_value().unwrap(), 2);
    assert_eq!(circ.get_var(&c).try_get_value().unwrap(), 3);
    assert_eq!(circ.get_var(&d).try_get_value().unwrap(), 3);
    assert_eq!(circ.get_var(&e).try_get_value().unwrap(), 6);
    assert_eq!(circ.get_var(&f).try_get_value().unwrap(), 18);
    assert_eq!(circ.get_var(&g).try_get_value().unwrap(), 4);
    assert_eq!(circ.get_var(&h).try_get_value().unwrap(), 72);
    assert_eq!(circ.get_var_value(&h).unwrap(), 72);
    assert_eq!(circ.get_output().unwrap(), vec![72]);
  }

  #[test]
  fn test_circuit_with_const() {
    let mut circ = FanInTwoCircuit::<i32>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    let o = circ.const_var(10);
    let p = circ.mul_vars(&h, &o);
    assert!(circ.get_var(&o).is_gate_output());
    assert!(circ.get_var(&p).is_gate_output());
    circ.mark_as_complete().unwrap();
    assert_eq!(circ.get_output_size(), 1);
    circ.evaluate(&vec![1, 2, 3]).unwrap();
    assert_eq!(circ.get_var(&a).try_get_value().unwrap(), 1);
    assert_eq!(circ.get_var(&b).try_get_value().unwrap(), 2);
    assert_eq!(circ.get_var(&c).try_get_value().unwrap(), 3);
    assert_eq!(circ.get_var(&d).try_get_value().unwrap(), 3);
    assert_eq!(circ.get_var(&e).try_get_value().unwrap(), 6);
    assert_eq!(circ.get_var(&f).try_get_value().unwrap(), 18);
    assert_eq!(circ.get_var(&g).try_get_value().unwrap(), 4);
    assert_eq!(circ.get_var(&h).try_get_value().unwrap(), 72);
    assert_eq!(circ.get_var(&o).try_get_value().unwrap(), 10);
    assert_eq!(circ.get_var(&p).try_get_value().unwrap(), 720);
    assert_eq!(circ.get_var_value(&p).unwrap(), 720);
    assert_eq!(circ.get_output().unwrap(), vec![720]);
  }

  #[test]
  fn test_get_instance() {
    let mut circ = FanInTwoCircuit::<i32>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    circ.mark_as_complete().unwrap();
    circ.mark_variable_as_public(&a).unwrap();
    circ.mark_variable_as_public(&h).unwrap();
    circ.assign_public_io(&vec![1, 72]).unwrap();
    assert_eq!(circ.get_var_value(&a).unwrap(), 1);
    assert_eq!(circ.get_instance().unwrap(), (vec![3, 12], vec![1, 72]));
  }

  #[test]
  fn test_get_instance_with_const() {
    let mut circ = FanInTwoCircuit::<i32>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    let o = circ.const_var(10);
    let p = circ.mul_vars(&h, &o);
    circ.mark_as_complete().unwrap();
    circ.mark_variable_as_public(&a).unwrap();
    circ.mark_variable_as_public(&p).unwrap();
    circ.assign_public_io(&vec![1, 720]).unwrap();
    assert_eq!(circ.get_var_value(&a).unwrap(), 1);
    assert_eq!(circ.get_instance().unwrap(), (vec![4, 17], vec![1, 720]));
  }

  #[test]
  fn test_get_witness() {
    let mut circ = FanInTwoCircuit::<i32>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    circ.mark_as_complete().unwrap();
    circ.mark_variable_as_public(&a).unwrap();
    circ.mark_variable_as_public(&h).unwrap();
    circ.evaluate(&vec![1, 2, 3]).unwrap();
    assert_eq!(
      circ.get_witness().unwrap(),
      (
        vec![2, 3, 4, 1, 1],
        vec![3, 6, 18, 2, 3],
        vec![6, 18, 72, 3, 4]
      )
    );
    assert_eq!(circ.get_instance().unwrap(), (vec![3, 12], vec![1, 72]));
  }

  #[test]
  fn test_get_witness_with_const() {
    let mut circ = FanInTwoCircuit::<i32>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    let o = circ.const_var(10);
    let p = circ.mul_vars(&h, &o);
    circ.mark_as_complete().unwrap();
    circ.mark_variable_as_public(&a).unwrap();
    circ.mark_variable_as_public(&p).unwrap();
    circ.evaluate(&vec![1, 2, 3]).unwrap();
    assert_eq!(
      circ.get_witness().unwrap(),
      (
        vec![2, 3, 4, 72, 1, 1, 0],
        vec![3, 6, 18, 10, 2, 3, 0],
        vec![6, 18, 72, 720, 3, 4, 10]
      )
    );
    assert_eq!(circ.get_instance().unwrap(), (vec![4, 17], vec![1, 720]));
  }

  #[test]
  fn test_get_consts() {
    let mut circ = FanInTwoCircuit::<i32>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    let o = circ.const_var(10);
    circ.mul_vars(&h, &o);
    circ.mark_as_complete().unwrap();
    assert_eq!(circ.get_consts(), vec![10]);
  }

  #[test]
  fn test_get_wiring() {
    let mut circ = FanInTwoCircuit::<i32>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    let o = circ.const_var(10);
    circ.mul_vars(&h, &o);
    circ.mark_as_complete().unwrap();
    assert_eq!(circ.get_var(&a).input_wires.len(), 2);
    assert!(!circ.get_var(&a).is_gate_output());
    assert_eq!(circ.get_var(&b).input_wires.len(), 2);
    assert!(!circ.get_var(&b).is_gate_output());
    assert_eq!(circ.get_var(&c).input_wires.len(), 1);
    assert!(!circ.get_var(&c).is_gate_output());
    assert_eq!(circ.get_var(&d).input_wires.len(), 2);
    assert!(circ.get_var(&d).is_gate_output());
    assert_eq!(circ.get_var(&e).input_wires.len(), 1);
    assert!(circ.get_var(&e).is_gate_output());
    assert_eq!(circ.get_var(&f).input_wires.len(), 1);
    assert!(circ.get_var(&f).is_gate_output());
    assert_eq!(
      circ.get_wiring().unwrap(),
      vec![
        (4, 5),
        (11, 0),
        (1, 12),
        (12, 18),
        (8, 14),
        (9, 15),
        (2, 19),
        (3, 16),
        (10, 20)
      ]
    );
  }

  #[test]
  fn test_get_wiring_with_assert_equals() {
    let mut circ = FanInTwoCircuit::<i32>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    let o = circ.const_var(10);
    let p = circ.mul_vars(&h, &o);
    circ.assert_equal(&a, &p);
    circ.mark_as_complete().unwrap();
    assert_eq!(circ.get_var(&a).input_wires.len(), 2);
    assert!(!circ.get_var(&a).is_gate_output());
    assert_eq!(circ.get_var(&b).input_wires.len(), 2);
    assert!(!circ.get_var(&b).is_gate_output());
    assert_eq!(circ.get_var(&c).input_wires.len(), 1);
    assert!(!circ.get_var(&c).is_gate_output());
    assert_eq!(circ.get_var(&d).input_wires.len(), 2);
    assert!(circ.get_var(&d).is_gate_output());
    assert_eq!(circ.get_var(&e).input_wires.len(), 1);
    assert!(circ.get_var(&e).is_gate_output());
    assert_eq!(circ.get_var(&f).input_wires.len(), 1);
    assert!(circ.get_var(&f).is_gate_output());
    assert_eq!(
      circ.get_wiring().unwrap(),
      vec![
        (4, 5),
        (11, 0),
        (1, 12),
        (12, 18),
        (8, 14),
        (9, 15),
        (2, 19),
        (3, 16),
        (10, 20),
        (4, 17),
      ]
    );
  }

  #[test]
  fn test_simple_field_circuit() {
    let mut circ = FanInTwoCircuit::<F>::new();
    let a = circ.add_global_input_variable().unwrap();
    let b = circ.add_global_input_variable().unwrap();
    let c = circ.add_global_input_variable().unwrap();
    let d = circ.add_vars(&a, &b);
    let e = circ.mul_vars(&b, &c);
    let f = circ.mul_vars(&d, &e);
    let g = circ.add_vars(&a, &d);
    let h = circ.mul_vars(&g, &f);
    assert!(circ.get_var(&h).is_gate_output());
    circ.mark_as_complete().unwrap();
    assert_eq!(circ.get_output_size(), 1);
    circ
      .evaluate(&vec![to_field::<F>(1), to_field::<F>(2), to_field::<F>(3)])
      .unwrap();
    assert_eq!(circ.get_var(&a).try_get_value().unwrap(), to_field::<F>(1));
    assert_eq!(circ.get_var(&b).try_get_value().unwrap(), to_field::<F>(2));
    assert_eq!(circ.get_var(&c).try_get_value().unwrap(), to_field::<F>(3));
    assert_eq!(circ.get_var(&d).try_get_value().unwrap(), to_field::<F>(3));
    assert_eq!(circ.get_var(&e).try_get_value().unwrap(), to_field::<F>(6));
    assert_eq!(circ.get_var(&f).try_get_value().unwrap(), to_field::<F>(18));
    assert_eq!(circ.get_var(&g).try_get_value().unwrap(), to_field::<F>(4));
    assert_eq!(circ.get_var(&h).try_get_value().unwrap(), to_field::<F>(72));
    assert_eq!(circ.get_var_value(&h).unwrap(), to_field::<F>(72));
    assert_eq!(circ.get_output().unwrap(), vec![to_field::<F>(72)]);
  }
}
