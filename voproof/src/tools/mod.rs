use crate::{error::Error, kzg::Commitment};
use ark_ec::{
  pairing::Pairing as PairingEngine, scalar_mul::variable_base::VariableBaseMSM,
  CurveGroup as ProjectiveCurve,
};
use ark_ff::PrimeField as Field;
use ark_std::{rand::RngCore, vec};
use sha2::{Digest, Sha256};

pub fn to_field<F: Field>(i: u64) -> F {
  F::from_bigint(i.into()).unwrap()
}

pub fn to_int<F: Field>(e: F) -> u64 {
  let digits = e.into_bigint().into().to_u64_digits();
  match digits.len() {
    0 => 0,
    1 => digits[0],
    _ => {
      println!("{:?}", digits);
      panic!("Number too big!")
    }
  }
}

pub fn try_to_int<F: Field>(e: F) -> Option<u64> {
  let digits = e.into_bigint().into().to_u64_digits();
  match digits.len() {
    0 => Some(0),
    1 => Some(digits[0]),
    _ => None,
  }
}

#[macro_export]
macro_rules! custom_add_literal {
  (-$a: literal, $b: expr) => {
    $b - to_field::<<E as PairingEngine>::ScalarField>($a)
  };

  ($a: literal, $b: expr) => {
    to_field::<<E as PairingEngine>::ScalarField>($a) + $b
  };

  ($a: expr, $b: literal) => {
    to_field::<<E as PairingEngine>::ScalarField>(($b) as u64) + $a
  };
}

#[macro_export]
macro_rules! custom_add {
    ($a: expr, $b: expr) => {
        $a + $b
    };

    ($a: expr, $b: expr, $($c: expr),+) => {
        $a as i64 + $b as i64 $(+ $c as i64)+
    };
}

pub fn custom_add_ff<F: Field>(a: F, b: F) -> F {
  a + b
}

pub fn custom_add_fi<F: Field>(a: F, b: i64) -> F {
  a + to_field::<F>(b as u64)
}

pub fn custom_add_if<F: Field>(a: i64, b: F) -> F {
  custom_add_fi(b, a)
}

pub fn custom_add_three<F: Field>(a: F, b: F, c: F) -> F {
  a + b + c
}

pub fn power<F: Field>(a: F, e: i64) -> F {
  if a.is_zero() || a.is_one() {
    a
  } else if e < 0 {
    a.inverse().unwrap().pow(&[(-e) as u64])
  } else {
    a.pow(&[e as u64])
  }
}

/// Compute the matrix-vector product using the sparse
/// representation of the matrix, where the row indices
/// and column indices start from 0
pub fn sparse_mvp<F: Field>(
  h: i64,
  k: i64,
  rows: &Vec<u64>,
  cols: &Vec<u64>,
  vals: &Vec<F>,
  right: &Vec<F>,
) -> Result<Vec<F>, Error> {
  assert!(h > 0);
  assert!(k > 0);
  assert_eq!(right.len(), k as usize);

  let mut res = vec![F::zero(); h as usize];
  for ((r, c), v) in rows.iter().zip(cols).zip(vals) {
    res[r.clone() as usize] += right[c.clone() as usize] * v;
  }
  Ok(res)
}

pub fn sample_field<F: Field, R: RngCore>(rng: &mut R) -> F {
  F::rand(rng)
}

pub fn sample_vec<F: Field, R: RngCore>(rng: &mut R, k: u64) -> Vec<F> {
  let mut res = Vec::new();
  for _ in 0..k {
    res.push(sample_field(rng));
  }
  res
}

/// Note: use the macro to_bytes![a, b, c] to convert any collection
/// of elements to a single bytes array, as long as a, b, c implement
/// the ToBytes trait.
pub fn hash_to_field<F: Field>(bytes: Vec<u8>) -> F {
  let mut sha = Sha256::new();
  sha.update(bytes);
  let output = sha.finalize();
  F::from_le_bytes_mod_order(&output)
}

pub fn combine_commits<E: PairingEngine>(
  comms: &Vec<Commitment<E>>,
  coeffs: &Vec<E::ScalarField>,
) -> Commitment<E> {
  Commitment {
    0: <E::G1 as VariableBaseMSM>::msm_unchecked(
      &comms.iter().map(|x| x.0).collect::<Vec<_>>()[..],
      coeffs.as_slice(),
    )
    .into_affine(),
  }
}

pub fn evaluate_sparse<F: Field>(x: F, coeffs: &Vec<F>, indices: &Vec<u64>) -> F {
  coeffs.iter().zip(indices).fold(F::zero(), |y, (c, i)| {
    y + c.clone() * power(x, i.clone() as i64)
  })
}

pub fn evaluate_short<F: Field>(x: F, coeffs: &Vec<F>) -> F {
  coeffs.iter().enumerate().fold(F::zero(), |y, (i, c)| {
    y + c.clone() * power(x, i.clone() as i64)
  })
}

pub struct PowerVectorIterator<F: Field> {
  _start: u64,
  _end: u64,
  _alpha: F,
  _length: u64,
  _shifted: u64,
  _i: u64,
  _curr: Option<F>,
}

impl<F: Field> Iterator for PowerVectorIterator<F> {
  type Item = F;
  fn next(&mut self) -> Option<F> {
    if self._end <= self._start || self._i >= self._end {
      return None;
    }
    let ret = if self._i < self._shifted || self._i >= self._length + self._shifted {
      Some(F::zero())
    } else if let Some(curr) = self._curr {
      Some(curr)
    } else {
      let curr = power(self._alpha, (self._i - self._shifted) as i64);
      self._curr = Some(curr);
      Some(curr)
    };

    self._i += 1;
    if let Some(curr) = self._curr {
      self._curr = Some(curr * self._alpha);
    }

    ret
  }
}

pub fn power_iter<F: Field>(
  start: u64,
  end: u64,
  alpha: F,
  length: u64,
  shifted: u64,
) -> PowerVectorIterator<F> {
  if end <= start {
    panic!("Invalid range");
  }
  PowerVectorIterator {
    _start: start,
    _end: end,
    _alpha: alpha,
    _length: length,
    _shifted: shifted,
    _i: start,
    _curr: None,
  }
}

#[macro_export]
macro_rules! to_int {
  ( $v: expr) => {
    $v.iter()
      .map(|e| to_int::<<E as PairingEngine>::ScalarField>(*e))
      .collect::<Vec<_>>()
  };
}

#[macro_export]
macro_rules! to_field {
  ( $v: expr) => {
    $v.iter()
      .map(|e| to_field::<<E as PairingEngine>::ScalarField>(*e))
      .collect::<Vec<_>>()
  };
}

#[macro_export]
macro_rules! scalar_to_field {
  ( $v: expr) => {
    to_field::<E::ScalarField>($v)
  };
}

#[macro_export]
macro_rules! one {
  () => {
    E::ScalarField::one()
  };
}

#[macro_export]
macro_rules! zero {
  () => {
    E::ScalarField::zero()
  };
}

#[macro_export]
macro_rules! minus {
  ($u:expr, $v:expr) => {
    $u - $v
  };
}

#[macro_export]
macro_rules! mul {
  ($u:expr, $v:expr) => {
    $u * $v
  };
}

#[macro_export]
macro_rules! minus_plus_one {
  ($u:expr, $v:expr) => {
    $u - $v + 1
  };
}

#[macro_export]
macro_rules! neg {
  ($u:expr) => {
    -$u
  };
}

#[macro_export]
macro_rules! minus_i64 {
  ($u:expr, $v:expr) => {
    ($u as i64) - ($v) as i64 + 1
  };
}

#[macro_export]
macro_rules! zero_pad {
  ( $u: expr, $n: expr ) => {
    (&$u)
      .iter()
      .map(|a| *a)
      .chain((0..($n as usize - $u.len())).map(|_| <E as PairingEngine>::ScalarField::zero()))
      .collect::<Vec<_>>()
  };
}

#[macro_export]
macro_rules! zero_pad_and_concat {
    ( $u: expr, $n: expr, $( $v: expr ),+ ) => {
        (&$u).iter().map(|a| *a)
          .chain((0..($n as usize-$u.len())).map(|_| <E as PairingEngine>::ScalarField::zero()))
          $(.chain((&$v).iter().map(|a| *a)))+.collect::<Vec<_>>()
    }
}

#[macro_export]
macro_rules! define {
  ( $v: ident, $expr: expr ) => {
    let $v = $expr;
  };
}

#[macro_export]
macro_rules! define_mut {
  ( $v: ident, $expr: expr ) => {
    let mut $v = $expr;
  };
}

#[macro_export]
macro_rules! define_vec {
  ( $v: ident, $expr: expr ) => {
    let $v: Vec<<E as PairingEngine>::ScalarField> = $expr;
  };
}

#[macro_export]
macro_rules! define_vec_mut {
  ( $v: ident, $expr: expr ) => {
    let mut $v: Vec<<E as PairingEngine>::ScalarField> = $expr;
  };
}

#[macro_export]
macro_rules! define_shift_minus_one {
  ( $name:ident, $vec:expr ) => {
    let $name = $vec.len() as i64 - 1;
  };
}

#[macro_export]
macro_rules! concat_matrix_vertically {
  ($result:ident, $h:expr,
   $arows:expr, $brows:expr, $crows:expr,
   $acols:expr, $bcols:expr, $ccols:expr,
   $avals:expr, $bvals:expr, $cvals:expr) => {
    let $result = (
      $arows
        .iter()
        .map(|a| *a)
        .chain($brows.iter().map(|&i| i + $h as u64))
        .chain($crows.iter().map(|&i| i + $h as u64 * 2))
        .collect::<Vec<u64>>(),
      $acols
        .iter()
        .chain($bcols.iter())
        .chain($ccols.iter())
        .map(|a| *a)
        .collect::<Vec<u64>>(),
      $avals
        .iter()
        .chain($bvals.iter())
        .chain($cvals.iter())
        .map(|a| *a)
        .collect::<Vec<E::ScalarField>>(),
    );
  };
}

#[macro_export]
macro_rules! concat_matrix_horizontally {
  ($result:ident, $k:expr,
   $arows:expr, $brows:expr, $crows:expr,
   $acols:expr, $bcols:expr, $ccols:expr,
   $avals:expr, $bvals:expr, $cvals:expr,
   $drows:expr, $dvals:expr) => {
    let $result = (
      $arows
        .iter()
        .chain($brows.iter())
        .chain($crows.iter())
        .chain($drows.iter())
        .map(|a| *a)
        .collect::<Vec<u64>>(),
      $acols
        .iter()
        .map(|&i| i + 1)
        .chain($bcols.iter().map(|&i| i + $k as u64 + 1))
        .chain($ccols.iter().map(|&i| i + $k as u64 * 2 + 1))
        .chain((0..$dvals.len()).map(|_| 0))
        .collect::<Vec<u64>>(),
      $avals
        .iter()
        .chain($bvals.iter())
        .chain($cvals.iter())
        .chain($dvals.iter())
        .map(|a| *a)
        .collect::<Vec<E::ScalarField>>(),
    );
  };
}

#[macro_export]
macro_rules! delta {
  ( $i: expr, $j: expr ) => {{
    if $i == $j {
      <E as PairingEngine>::ScalarField::one()
    } else {
      <E as PairingEngine>::ScalarField::zero()
    }
  }};
}

#[macro_export]
macro_rules! multi_delta {
    ( $i: expr, $( $c:expr, $j:expr ),+ ) => {
        {
            let mut s = <E as PairingEngine>::ScalarField::zero();
            $( if $i == $j {
              s = s + $c;
            } )+
            s
        }
    };
}

#[macro_export]
macro_rules! linear_combination {
    ( $i: expr ) => {
        $i
    };

    ( $i: expr, $( $c:expr, $j:expr ),* ) => {
        {
            let mut s = $i;
            $( s = s + $c * $j; )*
            s
        }
    };
}

#[macro_export]
macro_rules! commitment_linear_combination {
    ( $one: expr, $vk: expr, $( $cm:expr, $c:expr ),* ) => {
        {
            Commitment::<E>(
                sum!(
                    $( ( $cm.0 ).mul($c) ),*,
                    commit_scalar!($vk, $one)
                )
                .into_affine(),
            )
        }
    };
}

#[macro_export]
macro_rules! commitment_linear_combination_no_one {
    ( $( $cm:expr, $c:expr ),+ ) => {
        {
            Commitment::<E>(
                sum!(
                    $( ( $cm.0 ).mul($c.into_bigint()) ),+
                )
                .into_affine(),
            )
        }
    };
}

#[macro_export]
macro_rules! define_commitment_linear_combination {
    ( $name: ident, $vk: expr, $one: expr, $( $cm:expr, $c:expr ),* ) => {
      let $name = {
        let timer = start_timer!(|| "Linearly combining commitments");
        let ret = commitment_linear_combination!($one, $vk, $( $cm, $c ),* );
        end_timer!(timer);
        ret
      };
    };
}

#[macro_export]
macro_rules! define_commitment_linear_combination_no_one {
    ( $name: ident, $( $cm:expr, $c:expr ),+ ) => {
        let $name = commitment_linear_combination_no_one!( $( $cm, $c ),+ );
    };
}

#[macro_export]
macro_rules! linear_combination_base_zero {
    ( $( $c:expr, $j:expr ),+ ) => {
        linear_combination!(E::ScalarField::zero(), $( $c, $j ),+ )
    };
}

#[macro_export]
macro_rules! sample_randomizers {
    ( $rng: expr, $( $ident:ident, $size:expr ),+ ) => {
        $( let $ident = sample_vec::<<E as PairingEngine>::ScalarField, _>($rng, $size); )+
    };
}

#[macro_export]
macro_rules! power_linear_combination {
    ( $alpha: expr, $( $a:expr ),+ ) => {
        {
            let mut s = <E as PairingEngine>::ScalarField::zero();
            let mut _c = <E as PairingEngine>::ScalarField::one();
            $(
                s = s + _c * $a;
                _c = _c * $alpha;
            )+
            s
        }
    };
}

#[macro_export]
macro_rules! vector_index {
  ( $v: expr, $i: expr ) => {{
    if ($i as i64) >= 1i64 && ($i as i64) <= $v.len() as i64 {
      $v[($i as i64 - 1) as usize]
    } else {
      <E as PairingEngine>::ScalarField::zero()
    }
  }};
}

#[macro_export]
macro_rules! power_vector_index {
  ( $a: expr, $n: expr, $i: expr ) => {{
    if $i >= 1 && ($i as i64) <= ($n as i64) {
      power::<<E as PairingEngine>::ScalarField>($a, ($i - 1) as i64)
    } else {
      <E as PairingEngine>::ScalarField::zero()
    }
  }};
}

#[macro_export]
macro_rules! range_index {
  ( $s: expr, $e: expr, $i: expr ) => {{
    if ($i as i64) >= ($s as i64) && ($i as i64) <= ($e as i64) {
      <E as PairingEngine>::ScalarField::one()
    } else {
      <E as PairingEngine>::ScalarField::zero()
    }
  }};
}

#[macro_export]
macro_rules! expression_vector {
  ( $i: ident, $v: expr, $n: expr) => {{
    let timer = start_timer!(|| "Expression vector");
    let ret = (1..=$n).map(|$i| $v).collect::<Vec<_>>();
    end_timer!(timer);
    ret
  }};
}

#[macro_export]
macro_rules! define_expression_vector {
  ( $name:ident, $i: ident, $v: expr, $n: expr) => {
    let $name = expression_vector!($i, $v, $n);
  };
}

#[macro_export]
macro_rules! define_expression_vector_inverse {
  ( $name:ident, $i: ident, $v: expr, $n: expr) => {
    let mut $name = expression_vector!($i, $v, $n);
    let timer = start_timer!(|| "batch inversion");
    batch_inversion(&mut $name);
    end_timer!(timer);
    let $name = $name;
  };
}

#[macro_export]
macro_rules! add_expression_vector_to_vector {
  ( $u:ident, $i: ident, $v: expr) => {
    for $i in (1i64..=$u.len() as i64) {
      $u[($i - 1) as usize] += $v;
    }
  };
}

#[macro_export]
macro_rules! add_vector_to_vector {
  ( $u:ident, $v: expr) => {
    for i in (1i64..=$u.len() as i64) {
      $u[(i - 1) as usize] += vector_index!($v, i);
    }
  };
}

#[macro_export]
macro_rules! accumulate_vector {
    ( $i: ident, $init: expr, $v: expr, $n: expr, $op: tt ) => {
         (1..=$n).scan($init, |acc, $i| {*acc = *acc $op ($v); Some(*acc)})
                 .collect::<Vec<_>>()
    };

    ( $i: ident, $v: expr, $n: expr, $op: tt ) => {
        accumulate_vector!($i, <E as PairingEngine>::ScalarField::zero(), $v, $n, $op)
    };

    ( $v: expr, $init: expr, $op: tt ) => {
        accumulate_vector!(i, $init, $v[i-1], $v.len(), $op)
    };

    ( $v: expr, $op: tt ) => {
        accumulate_vector!(i, <E as PairingEngine>::ScalarField::zero(), $v[i-1], $v.len(), $op)
    };
}

#[macro_export]
macro_rules! accumulate_vector_plus {
    ( $i: ident, $init: expr, $v: expr, $n: expr) => {
        accumulate_vector!($i, $init, $v, $n, +)
    };

    ( $i: ident, $v: expr, $n: expr) => {
        accumulate_vector!($i, $v, $n, +)
    };

    ( $v: expr, $init: expr) => {
        accumulate_vector!($v, $init, +)
    };

    ( $v: expr) => {
        accumulate_vector!($v, +)
    };
}

#[macro_export]
macro_rules! accumulate_vector_mul {
    ( $i: ident, $init: expr, $v: expr, $n: expr) => {
        accumulate_vector!($i, $init, $v, $n, *)
    };

    ( $i: ident, $v: expr, $n: expr) => {
        accumulate_vector!($i, E::ScalarField::one(), $v, $n, *)
    };

    ( $v: expr, $init: expr) => {
        accumulate_vector!(i, $init, $v[i-1], $v.len(), *)
    };

    ( $v: expr) => {
        accumulate_vector!(i, E::ScalarField::one(), $v[i-1], $v.len(), *)
    };
}

#[macro_export]
macro_rules! define_accumulate_vector_mul {
  ( $name: ident, $i: ident, $init: expr, $v: expr, $n: expr) => {
    let $name = accumulate_vector_mul!($i, $init, $v, $n);
  };

  ( $name: ident, $i: ident, $v: expr, $n: expr) => {
    let $name = accumulate_vector_mul!($i, $v, $n);
  };

  ( $name: ident, $v: expr, $init: expr) => {
    let $name = accumulate_vector_mul!($v, $init);
  };

  ( $name: ident, $v: expr) => {
    let $name = accumulate_vector_mul!($v);
  };
}

#[macro_export]
macro_rules! vector_concat {
    ( $u: expr, $( $v: expr ),+ ) => {
        (&$u).iter().map(|a| *a)$(.chain((&$v).iter().map(|a| *a)))+.collect::<Vec<_>>()
    }
}

#[macro_export]
macro_rules! vector_concat_skip {
    ( $m:expr, $u: expr, $( $v: expr ),+ ) => {
        (&$u).iter()
          .skip($m as usize)
          .map(|a| *a)$(.chain((&$v).iter().map(|a| *a)))+.collect::<Vec<_>>()
    }
}

#[macro_export]
macro_rules! define_concat_subvec {
  ($u:ident, $a:expr, $ai:expr, $aj:expr, $b:expr, $bi:expr, $bj:expr) => {
    let $u = (&$a)
      .iter()
      .map(|a| *a)
      .skip($ai as usize)
      .take($aj as usize - $ai as usize)
      .chain(
        (&$b)
          .iter()
          .map(|a| *a)
          .skip($bi as usize)
          .take($bj as usize - $bi as usize),
      )
      .collect::<Vec<_>>();
  };
}

#[macro_export]
macro_rules! concat_and_one {
  ( $u: expr, $v: expr ) => {
    vector_concat!(vec!(one!()), $u, $v)
  };
}

#[macro_export]
macro_rules! max {
    ($h:expr) => ($h);
    ($h:expr, $($v: expr),+) => {
      {
        let a = $h;
        let b = max!($($v),+);
        if a < b { b } else { a }
      }
    };
}

#[macro_export]
macro_rules! min {
    ($h:expr) => ($h);
    ($h:expr, $($v: expr),+) => {
      {
        let a = $h;
        let b = min!($($v),+);
        if a < b { a } else { b }
      }
    };
}

#[macro_export]
macro_rules! sum {
    ($h:expr) => ($h);
    ($h:expr, $($v: expr),+) => {
        ($h + sum!($($v),+))
    };
}

#[macro_export]
macro_rules! define_sum {
    ($name:ident, $($v: expr),+) => {
        define!($name, sum!($($v),+));
    };
}

#[macro_export]
macro_rules! poly_from_vec_clone {
  ($v: expr) => {
    DensePoly::from_coefficients_vec($v.clone())
  };
}

#[macro_export]
macro_rules! poly_from_vec {
  ($v: expr) => {
    DensePoly::from_coefficients_vec($v)
  };
}

#[macro_export]
macro_rules! vector_reverse_omega {
  ($v: expr, $omega:expr) => {{
    let timer = start_timer!(|| "Reverse omega");
    let mut omega_power = <E as PairingEngine>::ScalarField::one();
    let ret = $v
      .iter()
      .map(|c| {
        let res = *c * omega_power;
        omega_power = omega_power * $omega;
        res
      })
      .collect::<Vec<<E as PairingEngine>::ScalarField>>()
      .iter()
      .map(|c| *c)
      .rev()
      .collect::<Vec<<E as PairingEngine>::ScalarField>>();
    end_timer!(timer);
    ret
  }};
}

#[macro_export]
macro_rules! define_vector_reverse_omega_shift {
  ($name: ident, $v: expr, $omega:expr, $shiftname:ident) => {
    define_vec!($name, vector_reverse_omega!($v, $omega));
    define_shift_minus_one!($shiftname, $v);
  };
}

#[macro_export]
macro_rules! int_array_to_power_vector {
  ($v:expr, $gamma:expr) => {
    expression_vector!(i, power($gamma, $v[i - 1] as i64), $v.len())
  };
}

#[macro_export]
macro_rules! define_int_array_to_power_vector {
  ($name:ident, $v:expr, $gamma:expr) => {
    define_vec!($name, int_array_to_power_vector!($v, $gamma));
  };
}

#[macro_export]
macro_rules! define_clone_vector {
  ($name:ident, $v:expr) => {
    define_vec!($name, $v.to_vec());
  };
}

#[macro_export]
macro_rules! define_matrix_vectors {
  ($u:ident, $w:ident, $v:ident, $mat:expr, $gamma:expr) => {
    define_int_array_to_power_vector!($u, $mat.0, $gamma);
    define_int_array_to_power_vector!($w, $mat.1, $gamma);
    define_clone_vector!($v, $mat.2);
  };
}

#[macro_export]
macro_rules! define_commit_vector {
  ($cm:ident, $v:expr, $powers:expr, $deg:expr) => {
    let $cm = commit_vector!($v, $powers, $deg);
  };
}

#[macro_export]
macro_rules! compute_density {
  ($v:expr) => {{
    $v.iter().filter(|a| !a.is_zero()).count()
  }};
}

#[macro_export]
macro_rules! commit_vector {
  ($v:expr, $powers:expr, $deg:expr) => {{
    let timer = start_timer!(|| format!("Commit vector of density {}", compute_density!($v)));
    let ret = vector_to_commitment::<E>(&$powers, &$v, $deg as u64).unwrap();
    end_timer!(timer);
    ret
  }};
}

#[macro_export]
macro_rules! define_hadamard_vector {
  ($name:ident, $u:expr, $v:expr) => {
    define_vec!(
      $name,
      $u.iter()
        .zip($v.iter())
        .map(|(a, b)| *a * *b)
        .collect::<Vec<E::ScalarField>>()
    );
  };
}

#[macro_export]
macro_rules! define_concat_vector {
    ($name:ident, $( $u:expr ),+ ) => {
        define_vec!(
            $name,
            vector_concat!( $($u),+ )
        );
    };
}

#[macro_export]
macro_rules! define_concat_vector_skip {
    ($name:ident, $m:expr, $( $u:expr ),+ ) => {
        define_vec!(
            $name,
            vector_concat_skip!( $m, $($u),+ )
        );
    };
}

#[macro_export]
macro_rules! define_concat_neg_vector {
  ($name:ident, $u:expr, $v:expr ) => {
    let timer = start_timer!(|| "Define concat neg");
    define_vec!(
      $name,
      $u.iter()
        .map(|a| *a)
        .chain($v.iter().map(|a| -*a))
        .collect::<Vec<E::ScalarField>>()
    );
    end_timer!(timer);
  };
}

#[macro_export]
macro_rules! define_concat_uwinverse_vector {
  ($name:ident, $v:expr, $mu:expr, $u:expr, $nu:expr, $w:expr ) => {
    let timer = start_timer!(|| "Define uw inverse");
    define_vec_mut!(
      $name,
      $u.iter()
        .map(|a| *a)
        .zip($w.iter().map(|a| *a))
        .map(|(u, w)| (($mu - u) * ($nu - w)))
        .collect::<Vec<E::ScalarField>>()
    );
    batch_inversion(&mut $name);
    define_concat_vector!($name, $v, $name);
    end_timer!(timer);
  };
}

#[macro_export]
macro_rules! define_uwinverse_vector {
  ($name:ident, $mu:expr, $u:expr, $nu:expr, $w:expr ) => {
    let $name = {
      let timer = start_timer!(|| "Define uw inverse");
      define_vec_mut!(
        $name,
        $u.iter()
          .map(|a| *a)
          .zip($w.iter().map(|a| *a))
          .map(|(u, w)| (($mu - u) * ($nu - w)))
          .collect::<Vec<E::ScalarField>>()
      );
      batch_inversion(&mut $name);
      end_timer!(timer);
      $name
    };
  };
}

#[macro_export]
macro_rules! define_zero_pad_concat_vector {
    ($name:ident, $v:expr, $n:expr, $( $u:expr ),+ ) => {
        let timer = start_timer!(|| "Define zero pad concat vector");
        define_vec!(
            $name,
            zero_pad_and_concat!( $v, $n, $($u),+ )
        );
        end_timer!(timer);
    };
}

#[macro_export]
macro_rules! redefine_zero_pad_concat_vector {
    ($name:ident, $n:expr, $( $u:expr ),+ ) => {
        define_zero_pad_concat_vector!($name, $name, $n, $($u),+);
    };
}

#[macro_export]
macro_rules! define_poly_from_vec {
  ($poly:ident, $v:expr) => {
    let $poly = poly_from_vec!($v);
  };
}

#[macro_export]
macro_rules! sparse_mvp_vector {
  ($mat:expr, $v:expr, $h:expr, $k:expr) => {
    sparse_mvp($h as i64, $k as i64, &$mat.0, &$mat.1, &$mat.2, &$v).unwrap()
  };
}

#[macro_export]
macro_rules! define_sparse_mvp_vector {
  ($name:ident, $mat:expr, $v:expr, $h:expr, $k:expr) => {
    let timer = start_timer!(|| "Sprase MVP");
    define_vec!($name, sparse_mvp_vector!($mat, $v, $h, $k));
    end_timer!(timer);
  };
}

#[macro_export]
macro_rules! define_sparse_mvp_concat_vector {
  ($name:ident, $mat:expr, $v:expr, $h:expr, $k:expr) => {
    let timer = start_timer!(|| "Sprase MVP concat");
    define_concat_vector!($name, sparse_mvp_vector!($mat, $v, $h, $k), $v);
    end_timer!(timer);
  };
}

#[macro_export]
macro_rules! define_left_sparse_mvp_vector {
  ($name:ident, $mat:expr, $v:expr, $h:expr, $k:expr) => {
    let timer = start_timer!(|| "Left Sprase MVP");
    let $name = sparse_mvp($k, $h, &$mat.1, &$mat.0, &$mat.2, &$v).unwrap();
    end_timer!(timer);
  };
}

#[macro_export]
macro_rules! push_to_vec {
    ($buf:expr, $y:expr, $($x:expr),*) => ({
        {
          $y.serialize_uncompressed(&mut $buf)
        }.and({$crate::push_to_vec!($buf, $($x),*)})
    });

    ($buf:expr, $x:expr) => ({
      $x.serialize_uncompressed(&mut $buf)
    })
}

#[macro_export]
macro_rules! to_bytes {
    ($($x:expr),*) => ({
        let mut buf = vec![];
        {$crate::push_to_vec!(buf, $($x),*)}.map(|_| buf).unwrap()
    });
}

#[macro_export]
macro_rules! get_randomness_from_hash {
    ($name:ident, $( $item:expr ),+) => {
      let $name = hash_to_field::<E::ScalarField>(
        to_bytes!( $( $item ),+ )
      );
    }
}

#[macro_export]
macro_rules! vector_mul {
  // Given vectors u, v and field element omega, compute
  // the coefficient vector of f_u(X) f_v(X)
  ($u:expr, $v:expr) => {{
    poly_from_vec_clone!($u)
      .mul(&poly_from_vec_clone!($v))
      .coeffs
  }};
}

#[macro_export]
macro_rules! get_eval {
  ($poly:expr, $evals_dict:expr, $size:expr) => {{
    $evals_dict.entry($size).or_insert_with(|| {
      let timer = start_timer!(|| format!("Forward FFT of size {}", $size));
      let domain = GeneralEvaluationDomain::new($size).unwrap();
      let evals: Evaluations<
        <E as PairingEngine>::ScalarField,
        GeneralEvaluationDomain<<E as PairingEngine>::ScalarField>,
      > = $poly.evaluate_over_domain_by_ref(domain);
      end_timer!(timer);
      evals
    })
  }};
}

#[macro_export]
macro_rules! vector_poly_mul {
  // Given vectors u, v and field element omega, compute
  // the coefficient vector of X^{|u|-1} f_u(omega X^{-1}) f_v(X)
  ($u:expr, $v:expr, $omega:expr, $left_name:expr, $right_name:expr) => {{
    let timer = start_timer!(|| format!(
      "Vector polynomial-multiplication of size {} and {}",
      $u.len(),
      $v.len()
    ));
    let u = poly_from_vec!(vector_reverse_omega!($u, $omega));
    let v = poly_from_vec_clone!($v);
    let size =
      GeneralEvaluationDomain::<<E as PairingEngine>::ScalarField>::compute_size_of_domain(
        $u.len() + $v.len(),
      )
      .unwrap();
    let mut uevals = get_eval!(u, $left_name, size).clone();
    let vevals = get_eval!(v, $right_name, size);
    uevals
      .evals
      .iter_mut()
      .zip(vevals.evals.iter())
      .for_each(|(a, b)| *a *= b);
    // uevals *= &vevals;
    let fft_timer = start_timer!(|| format!("Inverse FFT"));
    let ret = uevals.interpolate();
    end_timer!(fft_timer);
    // let ret = poly_from_vec!(vector_reverse_omega!($u, $omega)).mul(&poly_from_vec_clone!($v));
    end_timer!(timer);
    ret
  }};
}

#[macro_export]
macro_rules! vector_poly_mul_no_dict {
  // Given vectors u, v and field element omega, compute
  // the coefficient vector of X^{|u|-1} f_u(omega X^{-1}) f_v(X)
  ($u:expr, $v:expr, $omega:expr) => {{
    poly_from_vec!(vector_reverse_omega!($u, $omega)).mul(&poly_from_vec_clone!($v))
  }};
}

#[macro_export]
macro_rules! define_vector_domain_evaluations_dict {
  // To cache the evaluations of vectors and save some FFTs
  // Since a vector might be evaluated after "reverse and multily omega"
  // when it appears on the left side of the multiplication, its evaluations
  // are different when it appears on different sides. So one vector needs
  // two evaluation maps. Each map maps the given domain size to the corresponding
  // evaluation
  ($left_name:ident, $right_name:ident) => {
    let mut $left_name: HashMap<
      usize,
      Evaluations<
        <E as PairingEngine>::ScalarField,
        GeneralEvaluationDomain<<E as PairingEngine>::ScalarField>,
      >,
    > = HashMap::new();
    let mut $right_name: HashMap<
      usize,
      Evaluations<
        <E as PairingEngine>::ScalarField,
        GeneralEvaluationDomain<<E as PairingEngine>::ScalarField>,
      >,
    > = HashMap::new();
  };
}

#[macro_export]
macro_rules! define_vector_poly_mul {
  // Given vectors u, v and field element omega, compute
  // the coefficient vector of X^{|u|-1} f_u(omega X^{-1}) f_v(X)
  ($name:ident, $u:expr, $v:expr, $omega:expr, $left_name:expr, $right_name:expr) => {
    let $name = vector_poly_mul!($u, $v, $omega, $left_name, $right_name).coeffs;
  };
}

#[macro_export]
macro_rules! define_vector_poly_mul_shift {
  // Given vectors u, v and field element omega, compute
  // the coefficient vector of X^{|u|-1} f_u(omega X^{-1}) f_v(X)
  ($name:ident, $u:expr, $v:expr, $omega:expr, $shiftname:ident, $left_name:expr, $right_name:expr) => {
    define_vector_poly_mul!($name, $u, $v, $omega, $left_name, $right_name);
    define_shift_minus_one!($shiftname, $u);
  };
}

#[macro_export]
macro_rules! define_vector_poly_mul_no_dict {
  // Given vectors u, v and field element omega, compute
  // the coefficient vector of X^{|u|-1} f_u(omega X^{-1}) f_v(X)
  ($name:ident, $u:expr, $v:expr, $omega:expr) => {
    let $name = vector_poly_mul_no_dict!($u, $v, $omega).coeffs;
  };
}

#[macro_export]
macro_rules! add_to_first_item {
  ($v:expr, $e:expr) => {
    $v[0] += $e;
  };
}

#[macro_export]
macro_rules! vector_power_mul {
  // Given vector v, element alpha, length n, compute
  // the coefficient vector of v * power(alpha, n)
  ($v:expr, $alpha:expr, $n:expr) => {{
    let timer = start_timer!(|| format!("Vector power mul of size {} and {}", $v.len(), $n));

    // The accumulator version
    let alpha_power = power($alpha, $n as i64);
    let ret = (1..($n as usize) + $v.len())
      .scan(<E as PairingEngine>::ScalarField::zero(), |acc, i| {
        *acc = *acc * $alpha + vector_index!($v, i)
          - vector_index!($v, (i as i64) - ($n as i64)) * alpha_power;
        Some(*acc)
      })
      .collect::<Vec<_>>();

    // The Fourier transform version
    // define_expression_vector!(v, i, power_vector_index!($alpha, $n, i), $n);
    // let ret = vector_mul!($v, v);

    // This is the for-loop version, which is not notably faster
    // let alpha_power = power($alpha, $n as i64);
    // let mut ret = vec![E::ScalarField::zero(); ($n as usize) + $v.len() - 1];
    // let mut last = E::ScalarField::zero();
    // for i in 1..($n as usize) + $v.len() {
    // last = last * $alpha;
    // if i <= $v.len() {
    // last += vector_index!($v, i)
    // }
    // if i > $n as usize {
    // last -= vector_index!($v, (i as i64) - ($n as i64)) * alpha_power;
    // }
    // ret[i - 1] = last;
    // }
    end_timer!(timer);
    ret
  }};
}

#[macro_export]
macro_rules! define_vector_power_mul {
  ($name:ident, $v:expr, $alpha:expr, $n:expr) => {
    define_vec!($name, vector_power_mul!($v, $alpha, $n));
  };
}

#[macro_export]
macro_rules! power_power_mul {
  // Given two power vector, compute the coefficient vector
  // of their product
  ($alpha:expr, $n:expr, $beta:expr, $m:expr) => {{
    let alpha_power = power($alpha, $n as i64);
    let mut beta_power = <E as PairingEngine>::ScalarField::one();
    let mut late_beta_power = <E as PairingEngine>::ScalarField::zero();
    let timer = start_timer!(|| format!("Power power mul of size {} and {}", $n, $m));
    let ret = (1..($n as usize) + ($m as usize))
      .scan(<E as PairingEngine>::ScalarField::zero(), |acc, i| {
        *acc = *acc * $alpha + beta_power - late_beta_power * alpha_power;
        beta_power = if i >= ($m as usize) {
          <E as PairingEngine>::ScalarField::zero()
        } else {
          beta_power * $beta
        };
        late_beta_power = if i < ($n as usize) {
          <E as PairingEngine>::ScalarField::zero()
        } else if i == ($n as usize) {
          <E as PairingEngine>::ScalarField::one()
        } else {
          late_beta_power * $beta
        };
        Some(*acc)
      })
      .collect::<Vec<_>>();

    // let ret = if $alpha == $beta {
    // (0..($m + $n) as usize - 1)
    // .map(|k| {
    // let l = max!($m as usize, k + 1) - $m as usize;
    // let r = min!(($n - 1) as usize, k);
    // power($alpha, k as i64) * E::ScalarField::from((r - l + 1) as u128)
    // })
    // .collect::<Vec<_>>()
    // } else {
    // let ratio = $alpha / $beta;
    // let diff_inv = (ratio - E::ScalarField::one()).inverse().unwrap();
    // (0..($m + $n) as usize - 1)
    // .map(|k| {
    // let l = max!($m as usize, k + 1) - $m as usize;
    // let r = min!(($n - 1) as usize, k);
    // power($beta, k as i64)
    // * power(ratio, l as i64)
    // * (power(ratio, (r - l) as i64 + 1) - E::ScalarField::one())
    // * diff_inv
    // })
    // .collect::<Vec<_>>()
    // };
    end_timer!(timer);
    ret
  }};
}

#[macro_export]
macro_rules! define_power_power_mul {
  ($name:ident, $alpha:expr, $n:expr, $beta:expr, $m:expr) => {
    define_vec!($name, power_power_mul!($alpha, $n, $beta, $m));
  };
}

#[macro_export]
macro_rules! eval_vector_expression {
  // Compute f(z), where f has coefficient vector
  // expressed by an expression
  ($z:expr, $i:ident, $expr:expr, $n: expr) => {{
    let timer = start_timer!(|| format!("Eval vector expression of size {}", $n));
    let mut power = <E as PairingEngine>::ScalarField::one();
    let ret = (1..=$n)
      .map(|$i| {
        let ret = $expr * power;
        power = power * $z;
        ret
      })
      .sum::<<E as PairingEngine>::ScalarField>();
    end_timer!(timer);
    ret
  }};
}

#[macro_export]
macro_rules! define_eval_vector_expression {
  // Compute f(z), where f has coefficient vector
  // expressed by an expression
  ($name:ident, $z:expr, $i:ident, $expr:expr, $n: expr) => {
    let $name = {
      let z = $z;
      eval_vector_expression!(z, $i, $expr, $n)
    };
  };
}

#[macro_export]
macro_rules! eval_vector_as_poly {
  ($v:expr, $z:expr) => {
    eval_vector_expression!($z, i, vector_index!($v, i), $v.len())
  };
}

#[macro_export]
macro_rules! generator_of {
  ($e:ident) => {
    <<E as ark_ec::pairing::Pairing>::ScalarField as FftField>::GENERATOR
  };
}

#[macro_export]
macro_rules! define_generator {
  ($gamma:ident, $e:ident) => {
    let $gamma = generator_of!($e);
  };
}

#[macro_export]
macro_rules! init_size {
  ($name:ident, $attr:ident, $size:ident) => {
    let $name: i64 = $size.$attr as i64;
  };
}

#[macro_export]
macro_rules! check_poly_eval {
  ($f:expr, $z:expr, $y:expr, $info:literal) => {
    let y = $f.evaluate(&$z);
    if y != $y.clone() {
      return Err(Error::PolynomialEvaluationUnexpected(
        y.to_string(),
        $y.to_string(),
        $info.to_string(),
      ));
    }
  };
}

pub fn fmt_field<F: Field>(v: &F) -> String {
  if let Some(x) = try_to_int::<F>(v.clone()) {
    format!("Fp256({})", x)
  } else {
    if let Some(x) = try_to_int::<F>(-v.clone()) {
      format!("Fp256(-{})", x)
    } else {
      v.to_string()
    }
  }
}

#[macro_export]
macro_rules! fmt_ff {
  ($a:expr) => {
    fmt_field::<<E as PairingEngine>::ScalarField>($a)
  };
}

#[macro_export]
macro_rules! fmt_ff_vector {
  ($v: expr) => {
    ($v
      .iter()
      .map(|e| fmt_field::<<E as PairingEngine>::ScalarField>(e))
      .collect::<Vec<String>>())
    .join("\n")
  };
}

#[macro_export]
macro_rules! vector_diff {
  ($u: expr, $v: expr) => {{
    assert_eq!($u.len(), $v.len());
    ($u)
      .iter()
      .zip(($v).iter())
      .map(|(a, b)| *a - *b)
      .collect::<Vec<_>>()
  }};
}

#[macro_export]
macro_rules! check_vector_eq {
  ($u:expr, $v:expr, $info:literal) => {
    if $u.len() != $v.len() {
      return Err(Error::VectorNotEqual(format!("{}: length not equal, {} != {}", $info, $u.len(), $v.len())));
    }
    if let Some(i) = $u.iter().zip($v.iter()).position(|(a, b)| *a != *b) {
      return Err(Error::VectorNotEqual(
          format!("{}: unequal at {} (total length {}): {} != {}\nleft = [\n{}\n]\nright = [\n{}\n], diff = [\n{}\n], differ at {} places",
          $info, i, $u.len(), $u[i], $v[i], fmt_ff_vector!($u), fmt_ff_vector!($v),
          fmt_ff_vector!(vector_diff!($u, $v)),
          $u.iter().zip($v.iter()).filter(|(a,b)| *a != *b).count())));
    }
  }
}

#[macro_export]
macro_rules! check_expression_vector_eq {
  ($i:ident, $u:expr, $v:expr, $len:expr, $info:literal) => {
    check_vector_eq!(
      expression_vector!($i, $u, $len),
      expression_vector!($i, $v, $len),
      $info
    );
  };
}

#[macro_export]
macro_rules! eval_sparse_vector {
  ($z:expr, $indices:expr, $vals:expr) => {
    $indices
      .iter()
      .zip($vals.iter())
      .map(|(i, a)| power($z, *i as i64) * *a)
      .sum::<<E as PairingEngine>::ScalarField>()
  };
}

#[macro_export]
macro_rules! eval_sparse_zero_one_vector {
  ($z:expr, $indices:expr) => {
    $indices
      .iter()
      .map(|i| power($z, *i as i64))
      .sum::<<E as PairingEngine>::ScalarField>()
  };
}

#[macro_export]
macro_rules! define_sparse_vector {
  ($v:ident, $indices:expr, $vals:expr, $n:expr) => {
    let $v = {
      let mut $v = vec![<E as PairingEngine>::ScalarField::zero(); $n as usize];
      for (i, a) in $indices.iter().zip($vals.iter()) {
        $v[*i as usize] = *a;
      }
      $v
    };
  };
}

#[macro_export]
macro_rules! define_sparse_zero_one_vector {
  ($v:ident, $indices:expr, $n:expr) => {
    let $v = {
      let mut $v = vec![<E as PairingEngine>::ScalarField::zero(); $n as usize];
      for i in $indices.iter() {
        $v[*i as usize] = <E as PairingEngine>::ScalarField::one();
      }
      $v
    };
  };
}

#[macro_export]
macro_rules! define_permutation_vector_from_wires {
  ($v:ident, $gamma:expr, $index_pairs:expr, $n:expr) => {
    let $v = {
      // Initial value is gamma^{-1}, so the vector will start from one
      let mut $v = accumulate_vector!(_i, $gamma.inverse().unwrap(), $gamma, $n, * );
      for (i, j) in $index_pairs.iter() {
        let t = $v[*i as usize];
        $v[*i as usize] = $v[*j as usize];
        $v[*j as usize] = t;
      }
      $v
    };
  }
}

#[macro_export]
macro_rules! inverse {
  ($a:expr) => {
    $a.inverse().unwrap()
  };
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_bls12_381::Bls12_381 as E;
  use ark_bls12_381::Fr as F;
  use ark_ff::{Field, PrimeField};
  use ark_poly::{
    univariate::DensePolynomial as DensePoly, EvaluationDomain, Evaluations,
    GeneralEvaluationDomain,
  };

  use ark_poly_commit::DenseUVPolynomial as UVPolynomial;
  use ark_std::{collections::HashMap, One, Zero};

  #[test]
  fn test_int_field_transform() {
    for i in 0..1000 {
      assert_eq!(i, to_int::<F>(to_field::<F>(i)));
    }
  }

  #[test]
  fn test_max() {
    assert_eq!(max!(1, 2, 3), 3);
  }

  #[test]
  fn test_sparse_mvp() {
    let rows = vec![1, 0, 3, 2];
    let cols = vec![0, 1, 2, 3];
    let vals = vec![F::from(1), F::from(3), F::from(2), F::from(5)];
    let right = vec![F::from(1), F::from(1), F::from(1), F::from(1)];
    let left = sparse_mvp(4, 4, &rows, &cols, &vals, &right).unwrap();
    assert_eq!(left, vec![F::from(3), F::from(1), F::from(5), F::from(2)]);
  }

  #[test]
  fn test_power_iterator() {
    assert_eq!(
      power_iter::<F>(0, 5, F::one(), 3, 0).collect::<Vec<F>>(),
      vec![F::one(), F::one(), F::one(), F::zero(), F::zero()]
    );
    assert_eq!(
      power_iter::<F>(2, 6, to_field(2), 3, 0).collect::<Vec<F>>(),
      vec![to_field(4), F::zero(), F::zero(), F::zero()]
    );
    assert_eq!(
      power_iter::<F>(2, 6, to_field(2), 3, 3).collect::<Vec<F>>(),
      vec![F::zero(), to_field(1), to_field(2), to_field(4)]
    );
  }

  #[test]
  fn test_linear_combination() {
    assert_eq!(linear_combination!(1), 1);
    assert_eq!(linear_combination!(1, 2, 3), 7);
    assert_eq!(linear_combination!(1, 2, 3, 4, 5), 27);
  }

  #[test]
  fn test_multi_delta() {
    define_vec!(
      v,
      expression_vector!(
        i,
        multi_delta!(i, to_field::<F>(3), 5, to_field::<F>(2), 6),
        10
      )
    );
    assert_eq!(
      v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>(),
      vec![0, 0, 0, 0, 3, 2, 0, 0, 0, 0]
    );
  }

  #[test]
  fn test_delta() {
    define_vec!(v, expression_vector!(i, delta!(i, 5), 10));
    assert_eq!(
      v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>(),
      vec![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    );
  }

  #[test]
  fn test_accumulate_vector() {
    define_vec!(v, accumulate_vector!(i, to_field::<F>(i*i), 10, +));
    assert_eq!(
      v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>(),
      vec![1, 5, 14, 30, 55, 91, 140, 204, 285, 385]
    );
  }

  #[test]
  fn test_vector_index() {
    let v = to_field!(vec![1, 2, 3, 4]);
    define_vec!(v, expression_vector!(i, vector_index!(v, i as i64 - 3), 10));
    assert_eq!(to_int!(v), vec![0, 0, 0, 1, 2, 3, 4, 0, 0, 0]);
  }

  #[test]
  fn test_power_vector_index() {
    define_vec!(
      v,
      expression_vector!(
        i,
        power_vector_index!(to_field::<F>(2), 9, i as i64 - 3),
        10
      )
    );
    assert_eq!(to_int!(v), vec![0, 0, 0, 1, 2, 4, 8, 16, 32, 64]);
    define_vec!(
      v,
      expression_vector!(
        i,
        power_vector_index!(to_field::<F>(2), 4, i as i64 - 3),
        10
      )
    );
    assert_eq!(to_int!(v), vec![0, 0, 0, 1, 2, 4, 8, 0, 0, 0]);
  }

  #[test]
  fn test_range_index() {
    define_vec!(
      v,
      expression_vector!(i, range_index!(1, 9, i as i64 - 3), 10)
    );
    assert_eq!(to_int!(v), vec![0, 0, 0, 1, 1, 1, 1, 1, 1, 1]);
    define_vec!(
      v,
      expression_vector!(i, range_index!(2, 4, i as i64 - 3), 10)
    );
    assert_eq!(to_int!(v), vec![0, 0, 0, 0, 1, 1, 1, 0, 0, 0]);
  }

  #[test]
  fn test_power_linear_combination() {
    assert_eq!(
      power_linear_combination!(to_field::<F>(2), to_field::<F>(1)),
      to_field::<F>(1)
    );
    assert_eq!(
      power_linear_combination!(
        to_field::<F>(2),
        to_field::<F>(1),
        to_field::<F>(2),
        to_field::<F>(3),
        to_field::<F>(4)
      ),
      to_field::<F>(1 + 2 * 2 + 2 * 2 * 3 + 2 * 2 * 2 * 4)
    );
  }

  #[test]
  fn test_sum() {
    assert_eq!(sum!(1, 2, 3), 6);
  }

  #[test]
  fn test_vector_concat() {
    assert_eq!(
      vector_concat!(vec![1, 2, 3u64], vec![4, 5, 6u64]),
      vec![1, 2, 3, 4, 5, 6u64]
    );
    assert_eq!(
      vector_concat!(vec![1, 2, 3u64], vec![4, 5, 6u64], vec![7, 8, 9]),
      vec![1, 2, 3, 4, 5, 6, 7, 8, 9]
    );
  }

  #[test]
  fn test_vector_concat_skip() {
    assert_eq!(
      vector_concat_skip!(2, vec![1, 2, 3u64], vec![4, 5, 6u64]),
      vec![3, 4, 5, 6u64]
    );
    assert_eq!(
      vector_concat_skip!(1, vec![1, 2, 3u64], vec![4, 5, 6u64], vec![7, 8, 9]),
      vec![2, 3, 4, 5, 6, 7, 8, 9]
    );
  }

  #[test]
  fn test_vector_reverse_omega() {
    let omega = to_field::<F>(2);
    let v = to_field!(vec![1, 2, 3, 1]);
    assert_eq!(to_int!(vector_reverse_omega!(v, omega)), vec![8, 12, 4, 1]);
  }

  #[test]
  fn test_int_array_to_power_vector() {
    let gamma = to_field::<F>(2);
    let v = vec![1, 2, 3, 1];
    assert_eq!(
      to_int!(int_array_to_power_vector!(v, gamma)),
      vec![2, 4, 8, 2]
    );
  }

  #[test]
  fn test_vector_poly_mul() {
    let u = to_field!(vec![1, 1, 1, 1]);
    let v = to_field!(vec![1, 2, 3, 4]);
    let omega = to_field::<F>(2);
    define_vector_domain_evaluations_dict!(_u_left_dict, _u_right_dict);
    define_vector_domain_evaluations_dict!(_v_left_dict, _v_right_dict);
    let poly = vector_poly_mul!(u, v, omega, _u_left_dict, _u_right_dict);
    assert_eq!(to_int!(poly.coeffs), vec![8, 20, 34, 49, 24, 11, 4]);
  }

  #[test]
  fn test_vector_power_mul() {
    let v = to_field!(vec![1, 2, 3, 4]);
    let alpha = to_field::<F>(2);
    assert_eq!(
      to_int!(vector_power_mul!(v, alpha, 3)),
      vec![1, 4, 11, 18, 20, 16]
    );
    assert_eq!(
      to_int!(vector_power_mul!(v, alpha, 4)),
      vec![1, 4, 11, 26, 36, 40, 32]
    );
    assert_eq!(
      to_int!(vector_power_mul!(v, alpha, 5)),
      vec![1, 4, 11, 26, 52, 72, 80, 64]
    );
  }

  #[test]
  fn test_power_power_mul() {
    let alpha = to_field::<F>(2);
    let beta = to_field::<F>(3);
    assert_eq!(
      to_int!(power_power_mul!(alpha, 3, beta, 4)),
      vec![1, 5, 19, 57, 90, 108]
    );
    assert_eq!(
      to_int!(power_power_mul!(alpha, 4, beta, 4)),
      vec![1, 5, 19, 65, 114, 180, 216]
    );
    assert_eq!(
      to_int!(power_power_mul!(alpha, 5, beta, 4)),
      vec![1, 5, 19, 65, 130, 228, 360, 432]
    );
    assert_eq!(
      to_int!(power_power_mul!(
        <E as PairingEngine>::ScalarField::one(),
        4,
        <E as PairingEngine>::ScalarField::one(),
        4
      )),
      vec![1, 2, 3, 4, 3, 2, 1]
    );
  }

  #[test]
  fn test_eval_vector_expression() {
    assert_eq!(
      eval_vector_expression!(to_field::<F>(2), i, to_field::<F>(i as u64), 4),
      to_field::<F>(49)
    );
  }

  #[test]
  fn test_eval_vector_as_poly() {
    assert_eq!(
      eval_vector_as_poly!(to_field!(vec![1, 2, 3, 4]), to_field::<F>(2)),
      to_field::<F>(49)
    );
  }

  #[test]
  fn test_add_expression_to_vector() {
    let mut u = vec![0, 1, 2, 3, 4];
    add_expression_vector_to_vector!(u, i, i * i);
    assert_eq!(u, vec![1, 5, 11, 19, 29]);
  }

  #[test]
  fn test_add_vector_to_vector() {
    let mut u = to_field!(vec![0, 1, 2, 3, 4]);
    add_vector_to_vector!(u, to_field!(vec![1, 4, 9, 16, 25]));
    assert_eq!(to_int!(u), vec![1, 5, 11, 19, 29]);
  }

  #[test]
  fn test_zero_pad() {
    assert_eq!(
      to_int!(zero_pad!(to_field!(vec![1, 2, 3u64]), 3)),
      vec![1, 2, 3]
    );
    assert_eq!(
      to_int!(zero_pad!(to_field!(vec![1, 2, 3u64]), 5)),
      vec![1, 2, 3, 0, 0]
    );
  }

  #[test]
  fn test_zero_pad_concat() {
    assert_eq!(
      to_int!(zero_pad_and_concat!(
        to_field!(vec![1, 2, 3u64]),
        3,
        to_field!(vec![4, 5, 6u64])
      )),
      vec![1, 2, 3, 4, 5, 6u64]
    );
    assert_eq!(
      to_int!(zero_pad_and_concat!(
        to_field!(vec![1, 2, 3u64]),
        5,
        to_field!(vec![4, 5, 6u64]),
        to_field!(vec![7, 8, 9])
      )),
      vec![1, 2, 3, 0, 0, 4, 5, 6, 7, 8, 9]
    );
  }

  #[test]
  fn test_eval_sparse_vector() {
    assert_eq!(
      to_int(eval_sparse_vector!(
        to_field::<F>(2),
        vec![0, 2, 5],
        to_field!(vec![1, 2, 3])
      )),
      105
    );
  }

  #[test]
  fn test_eval_sparse_zero_one_vector() {
    assert_eq!(
      to_int(eval_sparse_zero_one_vector!(
        to_field::<F>(3),
        vec![0, 2, 5]
      )),
      253
    );
  }

  #[test]
  fn test_define_permutation_vector_from_wires() {
    let gamma = to_field::<F>(2);
    let index_pairs = vec![(0, 1), (2, 3), (3, 4)];
    define_permutation_vector_from_wires!(v, gamma, index_pairs, 5);
    assert_eq!(to_int!(v), vec![2, 1, 8, 16, 4]);
  }
}
