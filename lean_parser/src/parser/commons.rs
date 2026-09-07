//! Shared combinators: indentation verifiers (Lean's `colGt`/`colGe`
//! equivalents) and span-tracking.

use nom::Offset;

use crate::error::LeanError;
use crate::lexer::token::TokenKind;
use crate::span::Span;
use crate::tokens::{peek_tok, span_of, PResult, Tokens};

/// Zero-width: succeeds (consuming nothing) iff the next token's column
/// is strictly greater than `anchor`. Fails at `Eof` so every
/// indentation-anchored construct is guaranteed to terminate at end of
/// file. Per the nom-7 gotcha documented in `tokens.rs`: never make this
/// the *entire* body of a `many0`/`many1` -- always pair it with
/// something that consumes a token (`preceded(col_gt(a), tactic)`, not
/// `many0(col_gt(a))`).
pub fn col_gt<'a>(anchor: u32) -> impl FnMut(Tokens<'a>) -> PResult<'a, ()> {
    move |i: Tokens<'a>| {
        let t = peek_tok(i).expect("Tokens should never be empty");
        if matches!(t.kind, TokenKind::Eof) || t.col <= anchor {
            return Err(nom::Err::Error(LeanError::expected(
                format!("a token at column > {anchor}"),
                if matches!(t.kind, TokenKind::Eof) {
                    "end of input".to_string()
                } else {
                    format!("a token at column {}", t.col)
                },
                t.start,
                t.line,
                t.col,
            )));
        }
        Ok((i, ()))
    }
}

/// Zero-width: like `col_gt`, but `col >= anchor`.
pub fn col_ge<'a>(anchor: u32) -> impl FnMut(Tokens<'a>) -> PResult<'a, ()> {
    move |i: Tokens<'a>| {
        let t = peek_tok(i).expect("Tokens should never be empty");
        if matches!(t.kind, TokenKind::Eof) || t.col < anchor {
            return Err(nom::Err::Error(LeanError::expected(
                format!("a token at column >= {anchor}"),
                if matches!(t.kind, TokenKind::Eof) {
                    "end of input".to_string()
                } else {
                    format!("a token at column {}", t.col)
                },
                t.start,
                t.line,
                t.col,
            )));
        }
        Ok((i, ()))
    }
}

/// Zero-width: like `col_gt`, but `col == anchor`.
pub fn col_eq<'a>(anchor: u32) -> impl FnMut(Tokens<'a>) -> PResult<'a, ()> {
    move |i: Tokens<'a>| {
        let t = peek_tok(i).expect("Tokens should never be empty");
        if matches!(t.kind, TokenKind::Eof) || t.col != anchor {
            return Err(nom::Err::Error(LeanError::expected(
                format!("a token at column {anchor}"),
                if matches!(t.kind, TokenKind::Eof) {
                    "end of input".to_string()
                } else {
                    format!("a token at column {}", t.col)
                },
                t.start,
                t.line,
                t.col,
            )));
        }
        Ok((i, ()))
    }
}

/// Zero-width: succeeds iff the next token is on source line `line`.
/// Used to tell a same-line `by exact foo` apart from a `by` block whose
/// tactics start on a following line.
pub fn same_line<'a>(line: u32) -> impl FnMut(Tokens<'a>) -> PResult<'a, ()> {
    move |i: Tokens<'a>| {
        let t = peek_tok(i).expect("Tokens should never be empty");
        if t.line == line {
            Ok((i, ()))
        } else {
            Err(nom::Err::Error(LeanError::expected(
                format!("a token on line {line}"),
                format!("a token on line {}", t.line),
                t.start,
                t.line,
                t.col,
            )))
        }
    }
}

/// The column of the next token (used to establish a new indentation
/// anchor, e.g. the first tactic in a `by` block or the first `|` of a
/// `match`).
pub fn anchor_col(i: Tokens<'_>) -> u32 {
    peek_tok(i).expect("Tokens should never be empty").col
}

/// The line of the next token.
pub fn anchor_line(i: Tokens<'_>) -> u32 {
    peek_tok(i).expect("Tokens should never be empty").line
}

/// Runs `f`, then computes the `Span` covering every token it consumed
/// (from the first token of `i` through the last token consumed before
/// `rest`). If `f` consumed nothing, the span degenerates to that of the
/// next token (zero-width, e.g. an empty binder list).
pub fn spanned<'a, O>(
    mut f: impl FnMut(Tokens<'a>) -> PResult<'a, O>,
) -> impl FnMut(Tokens<'a>) -> PResult<'a, (O, Span)> {
    move |i: Tokens<'a>| {
        let start_span =
            span_of(peek_tok(i).expect("Tokens should never be empty"));
        let (rest, val) = f(i)?;
        let consumed = i.offset(&rest);
        let end_span = if consumed == 0 {
            start_span
        } else {
            span_of(&i.toks[consumed - 1])
        };
        Ok((rest, (val, Span::merge(start_span, end_span))))
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::lexer::lex;

    #[test]
    fn col_gt_succeeds_when_strictly_greater() {
        let toks = lex("  x").unwrap(); // 'x' is at column 2
        let input = Tokens::new(&toks);
        assert!(col_gt(1)(input).is_ok());
        assert!(col_gt(2)(input).is_err());
    }

    #[test]
    fn col_ge_succeeds_when_equal_or_greater() {
        let toks = lex("  x").unwrap();
        let input = Tokens::new(&toks);
        assert!(col_ge(2)(input).is_ok());
        assert!(col_ge(3)(input).is_err());
    }

    #[test]
    fn col_verifiers_fail_at_eof() {
        let toks = lex("").unwrap();
        let input = Tokens::new(&toks);
        assert!(col_gt(0)(input).is_err());
        assert!(col_ge(0)(input).is_err());
    }

    #[test]
    fn spanned_covers_all_consumed_tokens() {
        use crate::tokens::any_tok;
        let toks = lex("a b c").unwrap();
        let input = Tokens::new(&toks);
        let (_, (_, span)) = spanned(|i| {
            let (i, _) = any_tok(i)?;
            let (i, _) = any_tok(i)?;
            Ok((i, ()))
        })(input)
        .unwrap();
        // covers tokens 'a' (col 0) through 'b' (col 2, 1 char wide)
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 3);
    }

    #[test]
    fn spanned_degenerates_to_next_token_when_nothing_consumed() {
        let toks = lex("a").unwrap();
        let input = Tokens::new(&toks);
        let (_, (_, span)) =
            spanned(|i: Tokens<'_>| Ok((i, ())))(input).unwrap();
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 1);
    }
}
