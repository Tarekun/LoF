//! Dedicated error type for the whole lean_parser pipeline: lexing,
//! parsing, and I/O. Each variant carries a canned message (via
//! `thiserror`) plus enough position information to point a user at the
//! exact spot in the source. Constructed through helper methods so call
//! sites keep using `?` the same way they would with `Result<T, String>`.

use std::fmt::Debug;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LeanError {
    #[error("{line}:{col}: lexical error: {message}")]
    Lex {
        message: String,
        offset: u32,
        line: u32,
        col: u32,
    },

    #[error("{line}:{col}: expected {expected}, found {found}")]
    Expected {
        expected: String,
        found: String,
        offset: u32,
        line: u32,
        col: u32,
    },

    #[error("{line}:{col}: parse error ({kind:?}) near `{found}`")]
    Nom {
        kind: nom::error::ErrorKind,
        found: String,
        offset: u32,
        line: u32,
        col: u32,
    },

    #[error("{line}:{col}: unexpected trailing input: `{found}`")]
    Leftover {
        found: String,
        offset: u32,
        line: u32,
        col: u32,
    },

    #[error("{line}:{col}: recursion limit exceeded")]
    RecursionLimit { offset: u32, line: u32, col: u32 },

    #[error("error in '{path}': {source}")]
    InFile {
        path: String,
        #[source]
        source: Box<LeanError>,
    },

    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("{0}")]
    Aggregate(String),

    #[error("internal parser invariant violated: {0}")]
    Internal(String),
}

impl LeanError {
    pub fn lex(
        message: impl Into<String>,
        offset: u32,
        line: u32,
        col: u32,
    ) -> Self {
        LeanError::Lex {
            message: message.into(),
            offset,
            line,
            col,
        }
    }

    pub fn expected(
        expected: impl Into<String>,
        found: impl Into<String>,
        offset: u32,
        line: u32,
        col: u32,
    ) -> Self {
        LeanError::Expected {
            expected: expected.into(),
            found: found.into(),
            offset,
            line,
            col,
        }
    }

    pub fn leftover(
        found: impl Into<String>,
        offset: u32,
        line: u32,
        col: u32,
    ) -> Self {
        LeanError::Leftover {
            found: found.into(),
            offset,
            line,
            col,
        }
    }

    pub fn recursion_limit(offset: u32, line: u32, col: u32) -> Self {
        LeanError::RecursionLimit { offset, line, col }
    }

    pub fn in_file(path: impl Into<String>, source: LeanError) -> Self {
        LeanError::InFile {
            path: path.into(),
            source: Box::new(source),
        }
    }

    pub fn internal<T: Debug + ?Sized>(what: &T) -> Self {
        LeanError::Internal(format!("{:?}", what))
    }

    /// The byte offset this error points at, used by `ParseError::or`
    /// (see `tokens.rs`) to keep the *farthest* failure out of an `alt`.
    /// `None` for variants (I/O, JSON, aggregate) with no source position.
    pub fn offset(&self) -> Option<u32> {
        match self {
            LeanError::Lex { offset, .. }
            | LeanError::Expected { offset, .. }
            | LeanError::Nom { offset, .. }
            | LeanError::Leftover { offset, .. }
            | LeanError::RecursionLimit { offset, .. } => Some(*offset),
            LeanError::InFile { source, .. } => source.offset(),
            LeanError::Io(_)
            | LeanError::Json(_)
            | LeanError::Aggregate(_)
            | LeanError::Internal(_) => None,
        }
    }
}

/// Two errors are equal if they render the same message. This exists so
/// `Result<T, LeanError>` stays comparable with `assert_eq!` in tests (the
/// `Io`/`Json` variants wrap types that aren't `PartialEq` themselves),
/// not for any production control flow.
impl PartialEq for LeanError {
    fn eq(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn offset_extracts_position_from_positioned_variants() {
        let e = LeanError::expected("a def", "an identifier", 12, 2, 3);
        assert_eq!(e.offset(), Some(12));
    }

    #[test]
    fn offset_is_none_for_positionless_variants() {
        let e = LeanError::Aggregate("multiple errors".to_string());
        assert_eq!(e.offset(), None);
    }

    #[test]
    fn in_file_delegates_offset_to_its_source() {
        let inner = LeanError::lex("bad escape", 5, 1, 5);
        let wrapped = LeanError::in_file("foo.lean", inner);
        assert_eq!(wrapped.offset(), Some(5));
    }

    #[test]
    fn equality_is_message_based() {
        let a = LeanError::lex("unterminated string", 0, 1, 0);
        let b = LeanError::lex("unterminated string", 0, 1, 0);
        assert_eq!(a, b, "identical messages should compare equal");
    }
}
