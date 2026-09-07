//! The recursive-descent-over-tokens parser. `commons` holds shared
//! combinators (identifiers, indentation verifiers, span-tracking);
//! `precedence`/`terms` build expressions; `patterns` reinterprets terms
//! as patterns; `decls`/`tactics` build declarations and tactic blocks;
//! `api` ties it all together into `parse_module`.

pub mod api;
pub mod commons;
pub mod decls;
pub mod patterns;
pub mod precedence;
pub mod tactics;
pub mod terms;

use crate::error::LeanError;
use crate::lexer::token::Token;

/// The maximum term/tactic nesting depth before `Ctx::deeper` bails with
/// `LeanError::RecursionLimit`, as cheap insurance against a stack
/// overflow on adversarial or deeply-parenthesised input.
const MAX_DEPTH: u16 = 256;

/// Indentation/layout context, threaded explicitly through every parser
/// method (the way `LofParser` in the `language` crate threads `&self`)
/// rather than stored as mutable state. This is `Copy` on purpose: nom
/// combinators (`alt`, `opt`, `many0`, ...) clone their input and
/// context constantly, and keeping `Ctx` a small `Copy` value avoids any
/// aliasing subtlety about "which branch's context wins".
///
/// The single rule this implements is Lean's `withPosition` + `colGt`:
/// *a construct anchored at column `min_col` may only be continued by
/// tokens at column strictly greater than `min_col`*. See
/// `commons::col_gt`/`col_ge` for the verifiers, and the doc comments on
/// `parser::decls::parse_module_loop`, `parser::tactics::by_block`, and
/// `parser::terms::match_alts` for how each construct uses it.
#[derive(Debug, Clone, Copy)]
pub struct Ctx {
    /// Tokens continuing the current construct must satisfy
    /// `col > min_col`.
    pub min_col: u32,
    /// When set, alternatives (`|`) of the innermost `match` must have
    /// their `|` at `col >= alt_col`; a nested `match`'s alternatives
    /// are only accepted at a column strictly greater than this.
    pub alt_col: Option<u32>,
    pub depth: u16,
}

impl Ctx {
    pub fn top() -> Ctx {
        Ctx {
            min_col: 0,
            alt_col: None,
            depth: 0,
        }
    }

    pub fn anchored_at(self, col: u32) -> Ctx {
        Ctx {
            min_col: col,
            ..self
        }
    }

    pub fn with_alts(self, col: u32) -> Ctx {
        Ctx {
            alt_col: Some(col),
            ..self
        }
    }

    /// One level of recursion; fails with `LeanError::RecursionLimit`
    /// once `MAX_DEPTH` is exceeded. `at` supplies the position for the
    /// error message.
    pub fn deeper(self, at: &Token) -> Result<Ctx, LeanError> {
        if self.depth >= MAX_DEPTH {
            return Err(LeanError::recursion_limit(at.start, at.line, at.col));
        }
        Ok(Ctx {
            depth: self.depth + 1,
            ..self
        })
    }
}

/// Holds the original source text alongside the parser methods, so
/// constructs that keep raw text verbatim (an `Unknown` tactic's body,
/// an `Error` node's source slice) can recover it from token spans.
/// Parser methods are `&self` (mirroring `LofParser` in the `language`
/// crate) purely so they can reach `self.src`; there is no other mutable
/// or shared state.
pub struct LeanParser<'a> {
    pub src: &'a str,
}

impl<'a> LeanParser<'a> {
    pub fn new(src: &'a str) -> LeanParser<'a> {
        LeanParser { src }
    }

    /// The raw source text spanned by `[start, end)` byte offsets, used
    /// to recover verbatim text for `Unknown` tactics and `Error` nodes.
    pub fn text_between(&self, start: u32, end: u32) -> String {
        self.src[start as usize..end as usize].to_string()
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn ctx_top_has_no_indentation_requirement() {
        let c = Ctx::top();
        assert_eq!(c.min_col, 0);
        assert_eq!(c.alt_col, None);
        assert_eq!(c.depth, 0);
    }

    #[test]
    fn anchored_at_only_changes_min_col() {
        let c = Ctx::top().with_alts(3).anchored_at(5);
        assert_eq!(c.min_col, 5);
        assert_eq!(c.alt_col, Some(3), "with_alts should be preserved");
    }

    #[test]
    fn deeper_increments_depth_until_the_limit() {
        let tok =
            Token::new(crate::lexer::token::TokenKind::Eof, 0, 0, 1, 0, false);
        let mut c = Ctx::top();
        for _ in 0..MAX_DEPTH {
            c = c.deeper(&tok).unwrap();
        }
        assert!(c.deeper(&tok).is_err(), "depth limit should be enforced");
    }
}
