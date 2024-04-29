use ark_poly_commit::Error as PolyError;
use ark_std::fmt::{self, Debug, Display};

pub trait VOProofError: core::fmt::Debug + core::fmt::Display {
  fn source(&self) -> Option<&(dyn VOProofError + 'static)> {
    None
  }
}

impl<'a, E: VOProofError + 'a> From<E> for Box<dyn VOProofError + 'a> {
  fn from(err: E) -> Self {
    Box::new(err)
  }
}

impl<'a, E: VOProofError + Send + Sync + 'a> From<E> for Box<dyn VOProofError + Send + Sync + 'a> {
  fn from(err: E) -> Box<dyn VOProofError + Send + Sync + 'a> {
    Box::new(err)
  }
}

impl<T: VOProofError> VOProofError for Box<T> {}

impl From<String> for Box<dyn VOProofError + Send + Sync> {
  #[inline]
  fn from(err: String) -> Box<dyn VOProofError + Send + Sync> {
    struct StringError(String);

    impl VOProofError for StringError {}

    impl Display for StringError {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
      }
    }

    impl Debug for StringError {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
      }
    }

    Box::new(StringError(err))
  }
}

impl From<PolyError> for Box<dyn VOProofError + Send + Sync> {
  #[inline]
  fn from(err: PolyError) -> Box<dyn VOProofError + Send + Sync> {
    struct _PolyError(PolyError);

    impl VOProofError for _PolyError {}

    impl Display for _PolyError {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
      }
    }

    impl Debug for _PolyError {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
      }
    }

    Box::new(_PolyError(err))
  }
}

impl<'a> From<&'a str> for Box<dyn VOProofError + Send + Sync> {
  #[inline]
  fn from(err: &'a str) -> Box<dyn VOProofError + Send + Sync> {
    From::from(String::from(err))
  }
}

/// The error type for `VOProof`.
#[derive(Debug)]
pub enum Error {
  /// The query set contains a label for a polynomial that was not provided as
  /// input to the `PC::open`.
  MissingPolynomial {
    /// The label of the missing polynomial.
    label: String,
  },

  /// `Evaluations` does not contain an evaluation for the polynomial labelled
  /// `label` at a particular query.
  MissingEvaluation {
    /// The label of the missing polynomial.
    label: String,
  },

  /// The LHS of the equation is empty.
  MissingLHS {
    /// The label of the equation.
    label: String,
  },

  /// The provided polynomial was meant to be hiding, but `rng` was `None`.
  MissingRng,

  /// The degree provided in setup was too small; degree 0 polynomials
  /// are not supported.
  DegreeIsZero,

  /// The degree of the polynomial passed to `commit` or `open`
  /// was too large.
  TooManyCoefficients {
    /// The number of coefficients in the polynomial.
    num_coefficients: usize,
    /// The maximum number of powers provided in `Powers`.
    num_powers: usize,
  },

  /// The hiding bound was not `None`, but the hiding bound was zero.
  HidingBoundIsZero,

  /// The hiding bound was too large for the given `Powers`.
  HidingBoundToolarge {
    /// The hiding bound
    hiding_poly_degree: usize,
    /// The number of powers.
    num_powers: usize,
  },

  /// The degree provided to `trim` was too large.
  TrimmingDegreeTooLarge,

  /// The provided `enforced_degree_bounds` was `Some<&[]>`.
  EmptyDegreeBounds,

  /// The provided equation contained multiple polynomials, of which least one
  /// had a strict degree bound.
  EquationHasDegreeBounds(String),

  /// The required degree bound is not supported by ck/vk
  UnsupportedDegreeBound(usize),

  /// The degree bound for the `index`-th polynomial passed to `commit`, `open`
  /// or `check` was incorrect, that is, `degree_bound >= poly_degree` or
  /// `degree_bound <= max_degree`.
  IncorrectDegreeBound {
    /// Degree of the polynomial.
    poly_degree: usize,
    /// Degree bound.
    degree_bound: usize,
    /// Maximum supported degree.
    supported_degree: usize,
    /// Index of the offending polynomial.
    label: String,
  },

  /// The inputs to `commit`, `open` or `verify` had incorrect lengths.
  IncorrectInputLength(String),

  /// An invalid number of variables was provided to `setup`
  InvalidNumberOfVariables,

  /// The degree of the `index`-th polynomial passed to `commit`, `open`
  /// or `check` was incorrect, that is, `supported_degree <= poly_degree`
  PolynomialDegreeTooLarge {
    /// Degree of the polynomial.
    poly_degree: usize,
    /// Maximum supported degree.
    supported_degree: usize,
    /// Index of the offending polynomial.
    label: String,
  },

  Unimplemented(String),
  VerificationFail,
  GZNotZero(String),
  PolynomialEvaluationUnexpected(String, String, String),
  VectorNotEqual(String),
  VariableNotSet(usize),
  VariableNotConnected(usize),
  VariableIsNotOutput(usize),
  AllVariablesAreInputs,
  CircuitNotComplete,
  CircuitHasNoGlobalInput,
  GatesAreNotEmpty,
  VariableAlreadySetAsOutput,
  VariableAlreadySet(String),
  InputSizeNotSupported(usize, usize),
  TryingToConnectTheSameVariable,
  ConnectedVariablesDoNotHaveWire,
  MSMError(String),
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
            Error::MissingPolynomial { label } => write!(
                f,
                "`QuerySet` refers to polynomial \"{}\", but it was not provided.",
                label
            ),
            Error::MissingEvaluation { label } => write!(
                f,
                "`QuerySet` refers to polynomial \"{}\", but `Evaluations` does not contain an evaluation for it.",
                label
            ),
            Error::MissingLHS { label } => {
                write!(f, "Equation \"{}\" does not have a LHS.", label)
            },
            Error::MissingRng => write!(f, "hiding commitments require `Some(rng)`"),
            Error::DegreeIsZero => write!(
                f,
                "this scheme does not support committing to degree 0 polynomials"
            ),
            Error::TooManyCoefficients {
                num_coefficients,
                num_powers,
            } => write!(
                f,
                "the number of coefficients in the polynomial ({:?}) is greater than\
                 the maximum number of powers in `Powers` ({:?})",
                num_coefficients, num_powers
            ),
            Error::HidingBoundIsZero => write!(
                f,
                "this scheme does not support non-`None` hiding bounds that are 0"
            ),
            Error::HidingBoundToolarge {
                hiding_poly_degree,
                num_powers,
            } => write!(
                f,
                "the degree of the hiding poly ({:?}) is not less than the maximum number of powers in `Powers` ({:?})",
                hiding_poly_degree, num_powers
            ),
            Error::TrimmingDegreeTooLarge => {
                write!(f, "the degree provided to `trim` was too large")
            }
            Error::EmptyDegreeBounds => {
                write!(f, "provided `enforced_degree_bounds` was `Some<&[]>`")
            }
            Error::EquationHasDegreeBounds(e) => write!(
                f,
                "the eqaution \"{}\" contained degree-bounded polynomials",
                e
            ),
            Error::UnsupportedDegreeBound(bound) => write!(
                f,
                "the degree bound ({:?}) is not supported by the parameters",
                bound,
            ),
            Error::IncorrectDegreeBound {
                poly_degree,
                degree_bound,
                supported_degree,
                label,
            } => write!(
                f,
                "the degree bound ({:?}) for the polynomial {} \
                 (having degree {:?}) is greater than the maximum \
                 supported degree ({:?})",
                degree_bound, label, poly_degree, supported_degree
            ),
            Error::InvalidNumberOfVariables => write!(
                f,
                "An invalid number of variables was provided to `setup`"
            ),
            Error::PolynomialDegreeTooLarge {
                poly_degree,
                supported_degree,
                label,
            } => write!(
                f,
                "the polynomial {} has degree {:?}, but parameters only
                support up to degree ({:?})", label, poly_degree, supported_degree
            ),
            Error::IncorrectInputLength(err) => write!(f, "{}", err),
            Error::Unimplemented(info) => write!(f, "Unimplemented {}", info),
            Error::VerificationFail => write!(f, "VerificationFail"),
            Error::GZNotZero(info) => write!(f, "GZNotZero {}", info),
            Error::PolynomialEvaluationUnexpected(info1, info2, info3) => write!(f, "PolynomialEvaluationUnexpected {} {} {}", info1, info2, info3),
            Error::VectorNotEqual(info) => write!(f, "VectorNotEqual {}", info),
            Error::VariableNotSet(index) => write!(f, "VariableNotSet at index {}", index),
            Error::VariableNotConnected(index) => write!(f, "VariableNotConnected at index {}", index),
            Error::VariableIsNotOutput(index) => write!(f, "VariableIsNotOutput at index {}", index),
            Error::AllVariablesAreInputs => write!(f, "AllVariablesAreInputs: there are probably circular dependence between variables"),
            Error::CircuitNotComplete => write!(f, "CircuitNotComplete"),
            Error::CircuitHasNoGlobalInput => write!(f, "CircuitHasNotGlobalInput"),
            Error::GatesAreNotEmpty => write!(f, "GatesAreNotEmpty: you should not add any gate before finishing adding all the global inputs"),
            Error::VariableAlreadySetAsOutput => write!(f, "VariableAlreadySetAsOutput"),
            Error::VariableAlreadySet(info) => write!(f, "VariableAlreadySet to {}", info),
            Error::InputSizeNotSupported(expected, real) => write!(f, "InputSizeNotSupported, expected {}, got {}", expected, real),
            Error::TryingToConnectTheSameVariable => write!(f, "TryingToConnectTheSameVariable"),
            Error::ConnectedVariablesDoNotHaveWire => write!(f, "ConnectedVariablesDoNotHaveWire"),
            Error::MSMError(info) => write!(f, "MSMError {}", info),
        }
  }
}

impl VOProofError for Error {}
impl From<usize> for Error {
  fn from(e: usize) -> Self {
    Error::MSMError(format!("The shortest length the MSM can perform is {}", e))
  }
}
