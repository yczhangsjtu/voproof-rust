use ark_ff::Field;
use ark_std::collections::HashMap;

pub mod fan_in_two;

use super::r1cs::R1CS;
use fan_in_two::{FanInTwoCircuit, VariableRef};

enum Matrix {
  A,
  B,
  C,
}

impl<F: Field> From<R1CS<F>> for FanInTwoCircuit<F> {
  fn from(r1cs: R1CS<F>) -> FanInTwoCircuit<F> {
    let mut circ = FanInTwoCircuit::new();
    let input_vars: Vec<VariableRef> = (0..r1cs.ncols - 1)
      .map(|_| circ.add_global_input_variable().unwrap())
      .collect();
    let zero = circ.const_var(F::zero());
    let mut value_to_position_lists: HashMap<F, Vec<(usize, usize, Matrix)>> = HashMap::new();
    r1cs
      .arows
      .iter()
      .zip(r1cs.acols.iter())
      .zip(r1cs.avals.iter())
      .filter(|(_, v)| !v.is_zero())
      .for_each(|((ri, ci), v)| {
        value_to_position_lists
          .entry(*v)
          .or_insert(Vec::new())
          .push((*ri as usize, *ci as usize, Matrix::A))
      });
    r1cs
      .brows
      .iter()
      .zip(r1cs.bcols.iter())
      .zip(r1cs.bvals.iter())
      .filter(|(_, v)| !v.is_zero())
      .for_each(|((ri, ci), v)| {
        value_to_position_lists
          .entry(*v)
          .or_insert(Vec::new())
          .push((*ri as usize, *ci as usize, Matrix::B))
      });
    r1cs
      .crows
      .iter()
      .zip(r1cs.ccols.iter())
      .zip(r1cs.cvals.iter())
      .filter(|(_, v)| !v.is_zero())
      .for_each(|((ri, ci), v)| {
        value_to_position_lists
          .entry(-*v)
          .or_insert(Vec::new())
          .push((*ri as usize, *ci as usize, Matrix::C))
      });
    let const_vars = value_to_position_lists
      .keys()
      .map(|v| circ.const_var(*v))
      .collect::<Vec<_>>();
    let mut a_mul_results: Vec<Vec<VariableRef>> = vec![Vec::new(); r1cs.nrows as usize];
    let mut b_mul_results: Vec<Vec<VariableRef>> = vec![Vec::new(); r1cs.nrows as usize];
    let mut c_mul_results: Vec<Vec<VariableRef>> = vec![Vec::new(); r1cs.nrows as usize];
    value_to_position_lists
      .iter()
      .zip(const_vars.iter())
      .for_each(|((v, value), cvar)| {
        let mut mul_results_cache: HashMap<usize, VariableRef> = HashMap::new();
        value.iter().for_each(|(ri, ci, mtype)| {
          let mul_results = match mtype {
            Matrix::A => &mut a_mul_results,
            Matrix::B => &mut b_mul_results,
            Matrix::C => &mut c_mul_results,
          };
          let var = if v.is_zero() {
            zero.clone()
          } else if *ci > 0 {
            // Input vars does not include the leading 1, so minus 1
            // from the index
            if v.is_one() {
              input_vars[*ci - 1].clone()
            } else {
              mul_results_cache
                .entry(*ci - 1)
                .or_insert_with(|| circ.mul_vars(&cvar, &input_vars[*ci - 1]))
                .clone()
            }
          } else {
            // For the first column, directly use the constant variable
            // as the multiplication result
            cvar.clone()
          };
          mul_results[*ri].push(var);
        });
      });
    let a_sum_results: Vec<VariableRef> = a_mul_results
      .iter()
      .map(|row| {
        if row.len() > 0 {
          row
            .iter()
            .skip(1)
            .fold(row[0].clone(), |a, b| circ.add_vars(&a, &b))
        } else {
          zero.clone()
        }
      })
      .collect();
    let b_sum_results: Vec<VariableRef> = b_mul_results
      .iter()
      .map(|row| {
        if row.len() > 0 {
          row
            .iter()
            .skip(1)
            .fold(row[0].clone(), |a, b| circ.add_vars(&a, &b))
        } else {
          zero.clone()
        }
      })
      .collect();
    let c_sum_results: Vec<VariableRef> = c_mul_results
      .iter()
      .map(|row| {
        if row.len() > 0 {
          row
            .iter()
            .skip(1)
            .fold(row[0].clone(), |a, b| circ.add_vars(&a, &b))
        } else {
          zero.clone()
        }
      })
      .collect();
    a_sum_results
      .iter()
      .zip(b_sum_results.iter())
      .zip(c_sum_results.iter())
      .for_each(|((a, b), c)| {
        let m = &circ.mul_vars(&a, &b);
        let a = circ.add_vars(m, c);
        circ.assert_equal(&a, &zero).unwrap();
      });
    circ.mark_as_complete().unwrap();
    input_vars
      .iter()
      .take(r1cs.input_size as usize)
      .for_each(|x| {
        circ.mark_variable_as_public(x).unwrap();
      });
    circ
  }
}
