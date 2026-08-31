use std::fmt::Debug;
use thiserror::Error;

/// Dedicated error type for the whole LoF pipeline: parsing, elaboration,
/// type checking, unification and evaluation. Each variant carries a canned
/// message (built via `thiserror`) and is produced through a constructor
/// that takes the arguments specific to that failure kind, so callers keep
/// using `?` exactly as they did with `Result<_, String>`.
#[derive(Debug, Error)]
pub enum LofError {
    #[error("Unbound {kind}: {name}")]
    UnboundName { kind: &'static str, name: String },

    #[error("Type mismatch in {context}: expected {expected}, found {found}")]
    TypeMismatch {
        context: String,
        expected: String,
        found: String,
    },

    #[error("Type check error: {0}")]
    TypeCheckError(String),

    #[error("Arity mismatch in {context}: expected {expected} argument(s), found {found}")]
    ArityMismatch {
        context: String,
        expected: usize,
        found: usize,
    },

    #[error("Unification error: {term1} and {term2} do not unify")]
    UnificationFailure { term1: String, term2: String },

    #[error("Occurs check failed: {subject} contains a cyclical reference to itself")]
    OccursCheckCyclic { subject: String },

    #[error("Occurs check failed: variable {variable} occurs in substitution body {term}")]
    OccursCheckInTerm { variable: String, term: String },

    #[error("Conflicting substitution for variable {variable}: {term1} vs {term2}")]
    ConflictingSubstitution {
        variable: String,
        term1: String,
        term2: String,
    },

    #[error("{construct} is not supported in {theory}")]
    UnsupportedConstruct {
        theory: &'static str,
        construct: String,
    },

    #[error("Expected {expected} AST node, found {found}")]
    InvalidAstNode {
        expected: &'static str,
        found: String,
    },

    #[error("'{0}' is a reserved keyword and cannot be used as an identifier")]
    ReservedKeyword(String),

    #[error("Parse error ({kind:?}) near: {remaining}")]
    Nom {
        kind: nom::error::ErrorKind,
        remaining: String,
    },

    #[error("Parser needs more input: {0}")]
    IncompleteInput(String),

    #[error("Error parsing file '{filepath}'. Unparsed remainder starting at: {remaining}")]
    LeftoverInput { filepath: String, remaining: String },

    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Failed to parse config file: {0}")]
    Yaml(#[from] serde_yaml::Error),

    #[error("Invalid value '{value}' for config field '{field}'. Must be one of: {allowed}")]
    InvalidConfigValue {
        field: &'static str,
        value: String,
        allowed: &'static str,
    },

    #[error("{0}")]
    Aggregate(String),

    #[error("{0}")]
    Unsupported(String),

    #[error("{0}")]
    Other(String),
}

/// Truncates a parser input excerpt so `Nom`/`ReservedKeyword` messages stay readable.
fn excerpt(input: &str) -> String {
    let s: String = input.chars().take(60).collect();
    if s.chars().count() < input.chars().count() {
        format!("{s}…")
    } else {
        s
    }
}

impl LofError {
    pub fn unbound_variable(name: impl Into<String>) -> Self {
        LofError::UnboundName {
            kind: "variable",
            name: name.into(),
        }
    }

    pub fn unbound_predicate(name: impl Into<String>) -> Self {
        LofError::UnboundName {
            kind: "predicate",
            name: name.into(),
        }
    }

    pub fn type_mismatch<A: Debug + ?Sized, B: Debug + ?Sized>(
        context: impl Into<String>,
        expected: &A,
        found: &B,
    ) -> Self {
        LofError::TypeMismatch {
            context: context.into(),
            expected: format!("{:?}", expected),
            found: format!("{:?}", found),
        }
    }

    pub fn type_check_error<T: Debug + ?Sized>(term: &T) -> Self {
        LofError::TypeCheckError(format!("{:?}", term))
    }

    pub fn arity_mismatch(
        context: impl Into<String>,
        expected: usize,
        found: usize,
    ) -> Self {
        LofError::ArityMismatch {
            context: context.into(),
            expected,
            found,
        }
    }

    pub fn unification_failure<T: Debug + ?Sized>(term1: &T, term2: &T) -> Self {
        LofError::UnificationFailure {
            term1: format!("{:?}", term1),
            term2: format!("{:?}", term2),
        }
    }

    pub fn occurs_check_cyclic(subject: impl Into<String>) -> Self {
        LofError::OccursCheckCyclic {
            subject: subject.into(),
        }
    }

    pub fn occurs_check_in_term<T: Debug + ?Sized>(
        variable: impl Into<String>,
        term: &T,
    ) -> Self {
        LofError::OccursCheckInTerm {
            variable: variable.into(),
            term: format!("{:?}", term),
        }
    }

    pub fn conflicting_substitution<T: Debug + ?Sized>(
        variable: impl Into<String>,
        term1: &T,
        term2: &T,
    ) -> Self {
        LofError::ConflictingSubstitution {
            variable: variable.into(),
            term1: format!("{:?}", term1),
            term2: format!("{:?}", term2),
        }
    }

    pub fn unsupported_construct<T: Debug + ?Sized>(
        theory: &'static str,
        construct: &T,
    ) -> Self {
        LofError::UnsupportedConstruct {
            theory,
            construct: format!("{:?}", construct),
        }
    }

    pub fn invalid_ast_node<T: Debug + ?Sized>(expected: &'static str, found: &T) -> Self {
        LofError::InvalidAstNode {
            expected,
            found: format!("{:?}", found),
        }
    }

    pub fn reserved_keyword(word: &str) -> Self {
        LofError::ReservedKeyword(word.to_string())
    }

    pub fn parse_error(input: &str, kind: nom::error::ErrorKind) -> Self {
        LofError::Nom {
            kind,
            remaining: excerpt(input),
        }
    }

    pub fn leftover_input(filepath: impl Into<String>, remaining: impl Into<String>) -> Self {
        LofError::LeftoverInput {
            filepath: filepath.into(),
            remaining: remaining.into(),
        }
    }

    pub fn invalid_config_value(
        field: &'static str,
        value: impl Into<String>,
        allowed: &'static str,
    ) -> Self {
        LofError::InvalidConfigValue {
            field,
            value: value.into(),
            allowed,
        }
    }

    pub fn aggregate(errors: Vec<LofError>) -> Self {
        LofError::Aggregate(
            errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }

    pub fn unsupported(msg: impl Into<String>) -> Self {
        LofError::Unsupported(msg.into())
    }

    pub fn custom(msg: impl Into<String>) -> Self {
        LofError::Other(msg.into())
    }
}

impl<'a> nom::error::ParseError<&'a str> for LofError {
    fn from_error_kind(input: &'a str, kind: nom::error::ErrorKind) -> Self {
        LofError::parse_error(input, kind)
    }

    fn append(_input: &'a str, _kind: nom::error::ErrorKind, other: Self) -> Self {
        other
    }
}

/// Two errors are equal if they render the same message. This exists so
/// `Result<T, LofError>` stays comparable with `assert_eq!` in tests (the
/// `Io`/`Yaml` variants wrap types that aren't `PartialEq` themselves), not
/// for any production control flow — nothing in the crate branches on it.
impl PartialEq for LofError {
    fn eq(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

impl From<nom::Err<LofError>> for LofError {
    fn from(err: nom::Err<LofError>) -> Self {
        match err {
            nom::Err::Error(e) | nom::Err::Failure(e) => e,
            nom::Err::Incomplete(needed) => {
                LofError::IncompleteInput(format!("{:?}", needed))
            }
        }
    }
}
