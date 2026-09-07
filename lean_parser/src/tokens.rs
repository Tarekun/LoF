//! `Tokens<'a>`: a newtype over `&[Token]` implementing just enough of
//! nom 7's input traits to run its combinators over a token slice
//! instead of `&str`, plus the small `tag`-equivalent helper parsers
//! (`sym`, `kw`, `tok_if`, ...) that stand in for `nom::bytes::tag`
//! (which only works over character streams and cannot be implemented
//! here -- see the module-level notes below).
//!
//! # Why not implement `Compare`?
//!
//! `Compare<&[TokenKind]>` would be the "obvious" `tag`-equivalent, but
//! it's the wrong shape: the grammar wants to match tokens *by kind*
//! ("any identifier", "the symbol `→`"), while `Token` carries spans and
//! `TokenKind::Ident(String)` compares by payload. Matching by
//! `Compare` would mean building a throwaway `Vec<TokenKind>` at every
//! call site. The `sym`/`kw`/`tok_if` factories below match by kind
//! directly and are the idiomatic way to do this over a custom nom
//! input type.
//!
//! # nom-7 gotchas (see also `error.rs`, `parser/commons.rs`)
//!
//! - `InputTake::take_split` returns `(remaining, taken)` -- the
//!   opposite order from most of the rest of the crate's APIs. Getting
//!   it backwards silently reverses everything built on it; see the
//!   unit test below.
//! - `alt`/`tuple` cap out at 21 elements per call; the term-atom
//!   alternation in `parser::terms` nests to stay under that.
//! - A zero-width parser (like the column verifiers in
//!   `parser::commons`) must never be the *entire* body of `many0`/
//!   `many1` -- nom's no-progress guard turns that into a hard error
//!   rather than looping forever, which is correct, but means such
//!   verifiers must always be `preceded`/`terminated` around something
//!   that actually consumes a token.
//! - The `sym`/`kw`/`tok_if` factories return `FnMut` closures; they
//!   must be constructed fresh at each call site (`sym(Sym::Comma)`),
//!   not hoisted into a shared `let` and reused across combinators.
//! - `nom::Err::Incomplete` is unreachable here (there are no streaming
//!   combinators in play), but `LeanError`'s `From<nom::Err<_>>` still
//!   has to account for it.

use nom::{IResult, InputIter, InputLength, InputTake, Offset, Slice};
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};

use crate::error::LeanError;
use crate::lexer::token::{Keyword, Sym, Token, TokenKind};
use crate::span::Span;

/// The nom input type this crate's parsers run over: a borrowed slice of
/// already-lexed tokens. Deliberately a bare newtype over a slice (no
/// extra state) so `Offset`/`Clone`/`Copy` stay one-liners; parser
/// context that *isn't* part of "where am I in the token stream" (the
/// indentation anchor, recursion depth, ...) is threaded separately as
/// `parser::Ctx`, not stuffed in here.
#[derive(Debug, Clone, Copy)]
pub struct Tokens<'a> {
    pub toks: &'a [Token],
}

impl<'a> Tokens<'a> {
    pub fn new(toks: &'a [Token]) -> Tokens<'a> {
        Tokens { toks }
    }

    pub fn first(&self) -> &'a Token {
        // Safe to call `Eof` guaranteed by the lexer's terminal
        // sentinel: `toks` is only ever empty if that invariant is
        // violated, which callers should treat as an internal bug
        // rather than pattern-matching `Option` at every use site.
        self.toks.first().expect(
            "Tokens should never be empty: the lexer always appends an \
             Eof sentinel, and the top-level parse loop stops at Eof \
             rather than consuming it",
        )
    }
}

pub type PResult<'a, T> = IResult<Tokens<'a>, T, LeanError>;

impl<'a> InputLength for Tokens<'a> {
    fn input_len(&self) -> usize {
        self.toks.len()
    }
}

impl<'a> InputTake for Tokens<'a> {
    fn take(&self, count: usize) -> Self {
        Tokens {
            toks: &self.toks[..count],
        }
    }

    // NOTE the return order: (remaining, taken) -- reversed from most
    // other nom-adjacent APIs in this crate. See the unit test below.
    fn take_split(&self, count: usize) -> (Self, Self) {
        let (prefix, suffix) = self.toks.split_at(count);
        (Tokens { toks: suffix }, Tokens { toks: prefix })
    }
}

impl<'a> InputIter for Tokens<'a> {
    type Item = &'a Token;
    type Iter = std::iter::Enumerate<std::slice::Iter<'a, Token>>;
    type IterElem = std::slice::Iter<'a, Token>;

    fn iter_indices(&self) -> Self::Iter {
        self.toks.iter().enumerate()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.toks.iter()
    }

    fn position<P: Fn(Self::Item) -> bool>(&self, p: P) -> Option<usize> {
        self.toks.iter().position(p)
    }

    fn slice_index(&self, count: usize) -> Result<usize, nom::Needed> {
        if self.toks.len() >= count {
            Ok(count)
        } else {
            Err(nom::Needed::new(count - self.toks.len()))
        }
    }
}

impl<'a> Offset for Tokens<'a> {
    fn offset(&self, second: &Self) -> usize {
        // Valid because `second` is always a suffix of `self` in this
        // crate's usage (produced by `take_split`/`Slice`).
        self.toks.len() - second.toks.len()
    }
}

impl<'a> Slice<RangeFull> for Tokens<'a> {
    fn slice(&self, _range: RangeFull) -> Self {
        *self
    }
}
impl<'a> Slice<Range<usize>> for Tokens<'a> {
    fn slice(&self, range: Range<usize>) -> Self {
        Tokens {
            toks: &self.toks[range],
        }
    }
}
impl<'a> Slice<RangeTo<usize>> for Tokens<'a> {
    fn slice(&self, range: RangeTo<usize>) -> Self {
        Tokens {
            toks: &self.toks[range],
        }
    }
}
impl<'a> Slice<RangeFrom<usize>> for Tokens<'a> {
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        Tokens {
            toks: &self.toks[range],
        }
    }
}

impl<'a> nom::error::ParseError<Tokens<'a>> for LeanError {
    fn from_error_kind(input: Tokens<'a>, kind: nom::error::ErrorKind) -> Self {
        let t = input.first();
        LeanError::Nom {
            kind,
            found: describe(t),
            offset: t.start,
            line: t.line,
            col: t.col,
        }
    }

    fn append(
        _input: Tokens<'a>,
        _kind: nom::error::ErrorKind,
        other: Self,
    ) -> Self {
        other
    }

    /// nom's default `or` (used by `alt`) keeps whichever error `append`
    /// last produced -- effectively "the last branch tried" -- which for
    /// an `alt`-heavy grammar almost always reports the least useful
    /// failure (e.g. always "expected application" no matter what
    /// actually went wrong). Keeping the *farthest*-advanced failure
    /// instead is the single highest-leverage error-quality fix for this
    /// design.
    fn or(self, other: Self) -> Self {
        match (self.offset(), other.offset()) {
            (Some(a), Some(b)) => {
                if b >= a {
                    other
                } else {
                    self
                }
            }
            (None, _) => other,
            (_, None) => self,
        }
    }
}

impl<'a> nom::error::ContextError<Tokens<'a>> for LeanError {
    fn add_context(
        _input: Tokens<'a>,
        _ctx: &'static str,
        other: Self,
    ) -> Self {
        // Contexts aren't rendered separately (the farthest-error `or`
        // above already produces a reasonable message); this impl exists
        // only so `nom::error::context` type-checks if ever used.
        other
    }
}

impl<'a> From<nom::Err<LeanError>> for LeanError {
    fn from(err: nom::Err<LeanError>) -> Self {
        match err {
            nom::Err::Error(e) | nom::Err::Failure(e) => e,
            nom::Err::Incomplete(needed) => {
                // Unreachable in practice: nothing in this crate uses
                // streaming combinators, so `Incomplete` should never be
                // produced. Surface it as an internal-invariant error
                // rather than panicking outright.
                debug_assert!(
                    false,
                    "nom::Err::Incomplete should be unreachable: {needed:?}"
                );
                LeanError::internal(&format!(
                    "unexpected nom::Err::Incomplete({needed:?})"
                ))
            }
        }
    }
}

fn describe(t: &Token) -> String {
    match &t.kind {
        TokenKind::Ident(s) => format!("identifier `{s}`"),
        TokenKind::DotIdent(s) => format!("`.{s}`"),
        TokenKind::MetaIdent(s) => format!("`?{s}`"),
        TokenKind::Nat { raw, .. } => format!("numeral `{raw}`"),
        TokenKind::Str(_) => "a string literal".to_string(),
        TokenKind::Char(_) => "a character literal".to_string(),
        TokenKind::Keyword(k) => format!("`{k:?}`"),
        TokenKind::Sym(s) => format!("`{s:?}`"),
        TokenKind::DocComment(_) => "a doc comment".to_string(),
        TokenKind::Attr(_) => "an attribute".to_string(),
        TokenKind::Eof => "end of input".to_string(),
    }
}

pub fn span_of(t: &Token) -> Span {
    Span::new(t.start, t.end, t.line, t.col, t.line, t.col + 1)
}

/// True when the next token is `Eof` (without consuming it).
pub fn at_eof(i: Tokens<'_>) -> bool {
    matches!(i.first().kind, TokenKind::Eof)
}

/// Peeks at the next token without consuming it. `None` only if `toks`
/// is empty, which should never happen (see `Tokens::first`).
pub fn peek_tok<'a>(i: Tokens<'a>) -> Option<&'a Token> {
    i.toks.first()
}

/// Consumes exactly one token, whatever it is (used by the Pratt loop
/// to step over an already-recognised operator token).
pub fn any_tok(i: Tokens<'_>) -> PResult<'_, &Token> {
    if at_eof(i) {
        let t = i.first();
        return Err(nom::Err::Error(LeanError::expected(
            "a token",
            "end of input",
            t.start,
            t.line,
            t.col,
        )));
    }
    let (rest, taken) = i.take_split(1);
    Ok((rest, &taken.toks[0]))
}

/// Matches exactly one token whose `TokenKind` satisfies `pred`,
/// reporting `what` on failure. This is the general-purpose building
/// block `sym`/`kw`/`ident`/... are all defined in terms of.
pub fn tok_if<'a>(
    what: &'static str,
    pred: fn(&TokenKind) -> bool,
) -> impl FnMut(Tokens<'a>) -> PResult<'a, &'a Token> {
    move |i: Tokens<'a>| {
        let t = i.first();
        if pred(&t.kind) {
            let (rest, taken) = i.take_split(1);
            Ok((rest, &taken.toks[0]))
        } else {
            Err(nom::Err::Error(LeanError::expected(
                what,
                describe(t),
                t.start,
                t.line,
                t.col,
            )))
        }
    }
}

/// Matches exactly one symbol token.
pub fn sym<'a>(s: Sym) -> impl FnMut(Tokens<'a>) -> PResult<'a, &'a Token> {
    move |i: Tokens<'a>| {
        let t = i.first();
        match &t.kind {
            TokenKind::Sym(found) if *found == s => {
                let (rest, taken) = i.take_split(1);
                Ok((rest, &taken.toks[0]))
            }
            _ => Err(nom::Err::Error(LeanError::expected(
                format!("`{s:?}`"),
                describe(t),
                t.start,
                t.line,
                t.col,
            ))),
        }
    }
}

/// Matches exactly one keyword token.
pub fn kw<'a>(k: Keyword) -> impl FnMut(Tokens<'a>) -> PResult<'a, &'a Token> {
    move |i: Tokens<'a>| {
        let t = i.first();
        match &t.kind {
            TokenKind::Keyword(found) if *found == k => {
                let (rest, taken) = i.take_split(1);
                Ok((rest, &taken.toks[0]))
            }
            _ => Err(nom::Err::Error(LeanError::expected(
                format!("`{k:?}`"),
                describe(t),
                t.start,
                t.line,
                t.col,
            ))),
        }
    }
}

/// Matches one identifier, returning `(name, span)`.
pub fn ident(i: Tokens<'_>) -> PResult<'_, (String, Span)> {
    let t = i.first();
    match &t.kind {
        TokenKind::Ident(name) => {
            let (rest, taken) = i.take_split(1);
            Ok((rest, (name.clone(), span_of(&taken.toks[0]))))
        }
        _ => Err(nom::Err::Error(LeanError::expected(
            "an identifier",
            describe(t),
            t.start,
            t.line,
            t.col,
        ))),
    }
}

/// Matches one leading-dot identifier (`.succ`), returning
/// `(name, span)`.
pub fn dot_ident(i: Tokens<'_>) -> PResult<'_, (String, Span)> {
    let t = i.first();
    match &t.kind {
        TokenKind::DotIdent(name) => {
            let (rest, taken) = i.take_split(1);
            Ok((rest, (name.clone(), span_of(&taken.toks[0]))))
        }
        _ => Err(nom::Err::Error(LeanError::expected(
            "a `.identifier`",
            describe(t),
            t.start,
            t.line,
            t.col,
        ))),
    }
}

/// Matches one synthetic-hole identifier (`?m`), returning
/// `(name, span)`.
pub fn meta_ident(i: Tokens<'_>) -> PResult<'_, (String, Span)> {
    let t = i.first();
    match &t.kind {
        TokenKind::MetaIdent(name) => {
            let (rest, taken) = i.take_split(1);
            Ok((rest, (name.clone(), span_of(&taken.toks[0]))))
        }
        _ => Err(nom::Err::Error(LeanError::expected(
            "a `?metavariable`",
            describe(t),
            t.start,
            t.line,
            t.col,
        ))),
    }
}

/// Matches one natural-number literal, returning `(value, raw, span)`.
pub fn nat_lit(i: Tokens<'_>) -> PResult<'_, (u64, String, Span)> {
    let t = i.first();
    match &t.kind {
        TokenKind::Nat { value, raw } => {
            let (rest, taken) = i.take_split(1);
            Ok((rest, (*value, raw.clone(), span_of(&taken.toks[0]))))
        }
        _ => Err(nom::Err::Error(LeanError::expected(
            "a numeral",
            describe(t),
            t.start,
            t.line,
            t.col,
        ))),
    }
}

/// Matches one string literal, returning `(value, span)`.
pub fn str_lit(i: Tokens<'_>) -> PResult<'_, (String, Span)> {
    let t = i.first();
    match &t.kind {
        TokenKind::Str(value) => {
            let (rest, taken) = i.take_split(1);
            Ok((rest, (value.clone(), span_of(&taken.toks[0]))))
        }
        _ => Err(nom::Err::Error(LeanError::expected(
            "a string literal",
            describe(t),
            t.start,
            t.line,
            t.col,
        ))),
    }
}

/// Matches one char literal, returning `(value, span)`.
pub fn char_lit(i: Tokens<'_>) -> PResult<'_, (char, Span)> {
    let t = i.first();
    match &t.kind {
        TokenKind::Char(value) => {
            let (rest, taken) = i.take_split(1);
            Ok((rest, (*value, span_of(&taken.toks[0]))))
        }
        _ => Err(nom::Err::Error(LeanError::expected(
            "a character literal",
            describe(t),
            t.start,
            t.line,
            t.col,
        ))),
    }
}

/// Matches one doc comment, returning `(text, span)`.
pub fn doc_comment(i: Tokens<'_>) -> PResult<'_, (String, Span)> {
    let t = i.first();
    match &t.kind {
        TokenKind::DocComment(text) => {
            let (rest, taken) = i.take_split(1);
            Ok((rest, (text.clone(), span_of(&taken.toks[0]))))
        }
        _ => Err(nom::Err::Error(LeanError::expected(
            "a doc comment",
            describe(t),
            t.start,
            t.line,
            t.col,
        ))),
    }
}

/// Matches one attribute, returning `(raw_text, span)`.
pub fn attr(i: Tokens<'_>) -> PResult<'_, (String, Span)> {
    let t = i.first();
    match &t.kind {
        TokenKind::Attr(text) => {
            let (rest, taken) = i.take_split(1);
            Ok((rest, (text.clone(), span_of(&taken.toks[0]))))
        }
        _ => Err(nom::Err::Error(LeanError::expected(
            "an attribute",
            describe(t),
            t.start,
            t.line,
            t.col,
        ))),
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::lexer::lex;
    use nom::branch::alt;
    use nom::error::ErrorKind;
    use nom::multi::many1;

    #[test]
    fn take_split_returns_remaining_then_taken() {
        let toks = lex("a b c").unwrap();
        let input = Tokens::new(&toks);
        let (remaining, taken) = input.take_split(2);
        assert_eq!(taken.toks.len(), 2, "taken should be the first 2 tokens");
        assert_eq!(
            remaining.toks.len(),
            toks.len() - 2,
            "remaining should be everything else"
        );
        assert_eq!(taken.toks[0], toks[0]);
        assert_eq!(remaining.toks[0], toks[2]);
    }

    #[test]
    fn offset_measures_tokens_consumed() {
        let toks = lex("a b c").unwrap();
        let input = Tokens::new(&toks);
        let (rest, _taken) = input.take_split(2);
        assert_eq!(input.offset(&rest), 2);
    }

    #[test]
    fn ident_and_sym_helpers_compose_under_a_real_nom_pipeline() {
        let toks = lex("+ - +").unwrap();
        let input = Tokens::new(&toks);
        let (rest, matched) =
            many1(alt((sym(Sym::Add), sym(Sym::Sub))))(input).unwrap();
        assert_eq!(matched.len(), 3);
        assert!(at_eof(rest));
    }

    #[test]
    fn tok_if_reports_the_expected_description_on_mismatch() {
        let toks = lex("123").unwrap();
        let input = Tokens::new(&toks);
        let err = ident(input).unwrap_err();
        match err {
            nom::Err::Error(LeanError::Expected { expected, .. }) => {
                assert_eq!(expected, "an identifier");
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn parse_error_or_keeps_the_farthest_failure() {
        let near = LeanError::expected("a", "b", 0, 1, 0);
        let far = LeanError::expected("c", "d", 10, 2, 3);
        assert_eq!(
            nom::error::ParseError::<Tokens>::or(near.clone(), far.clone()),
            far,
            "or() should keep whichever error is farther into the input"
        );
        assert_eq!(
            nom::error::ParseError::<Tokens>::or(far.clone(), near.clone()),
            far,
            "argument order shouldn't matter -- the farther offset wins"
        );
    }

    // `LeanError` doesn't derive `Clone`; re-derive it just for this
    // test module so the `or()` test above can reuse `near`/`far`.
    impl Clone for LeanError {
        fn clone(&self) -> Self {
            match self {
                LeanError::Expected {
                    expected,
                    found,
                    offset,
                    line,
                    col,
                } => LeanError::Expected {
                    expected: expected.clone(),
                    found: found.clone(),
                    offset: *offset,
                    line: *line,
                    col: *col,
                },
                other => LeanError::Internal(other.to_string()),
            }
        }
    }

    #[test]
    fn from_error_kind_points_at_the_next_token() {
        let toks = lex("x").unwrap();
        let input = Tokens::new(&toks);
        let e = <LeanError as nom::error::ParseError<Tokens>>::from_error_kind(
            input,
            ErrorKind::Alt,
        );
        assert_eq!(e.offset(), Some(0));
    }
}
