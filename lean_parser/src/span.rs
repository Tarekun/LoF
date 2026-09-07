//! Source spans: byte offsets plus line/column, attached to every AST node
//! so the JSON output carries real source positions.

use serde::{Deserialize, Serialize};

/// A half-open byte range `[start, end)` into the source file, plus the
/// line/column of both endpoints. Lines are 1-based; columns are 0-based
/// and counted in Unicode scalar values (matching Lean's own convention),
/// not bytes or grapheme clusters.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

impl Span {
    /// A span with no real source position, used for synthesised nodes
    /// (e.g. recovery placeholders) that don't correspond to real tokens.
    pub const DUMMY: Span = Span {
        start: 0,
        end: 0,
        line: 0,
        col: 0,
        end_line: 0,
        end_col: 0,
    };

    pub fn new(
        start: u32,
        end: u32,
        line: u32,
        col: u32,
        end_line: u32,
        end_col: u32,
    ) -> Span {
        Span {
            start,
            end,
            line,
            col,
            end_line,
            end_col,
        }
    }

    /// Merge two spans into one covering both: the start of `a` through
    /// the end of `b`. Assumes `a` occurs at or before `b` in the source.
    pub fn merge(a: Span, b: Span) -> Span {
        Span {
            start: a.start,
            end: b.end,
            line: a.line,
            col: a.col,
            end_line: b.end_line,
            end_col: b.end_col,
        }
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn merge_takes_start_of_a_and_end_of_b() {
        let a = Span::new(0, 5, 1, 0, 1, 5);
        let b = Span::new(10, 15, 2, 2, 2, 7);
        let m = Span::merge(a, b);
        assert_eq!(
            m,
            Span::new(0, 15, 1, 0, 2, 7),
            "merge should start where `a` starts and end where `b` ends"
        );
    }

    #[test]
    fn dummy_span_is_all_zero() {
        assert_eq!(Span::DUMMY, Span::new(0, 0, 0, 0, 0, 0));
    }
}
