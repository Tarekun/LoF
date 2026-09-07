//! Tactic parsing: `by` blocks and the closed set of modelled tactics
//! (`intro`/`exact`/`apply`, matching the `language` crate's own
//! interactive-tactic vocabulary), plus `<;>` sequencing and a raw-text
//! `Unknown` catch-all for anything else so a real-world `by` block
//! doesn't force its whole surrounding declaration into an `Error` node.

use nom::branch::alt;
use nom::InputTake;

use crate::ast::tactic::{Tactic, TacticKind};
use crate::error::LeanError;
use crate::lexer::token::{Sym, TokenKind};
use crate::parser::commons::{col_ge, spanned};
use crate::parser::{Ctx, LeanParser};
use crate::span::Span;
use crate::tokens::{any_tok, peek_tok, span_of, sym, PResult, Tokens};

/// Matches one identifier token whose text is exactly `word` -- the
/// mechanism for recognising tactic names (`intro`, `exact`, `apply`),
/// which are ordinary identifiers in Lean's grammar, not reserved
/// keywords.
fn ident_eq<'a>(
    word: &'static str,
) -> impl FnMut(Tokens<'a>) -> PResult<'a, ()> {
    move |i: Tokens<'a>| {
        let t = i.first();
        match &t.kind {
            TokenKind::Ident(s) if s == word => {
                let (rest, _) = i.take_split(1);
                Ok((rest, ()))
            }
            _ => Err(nom::Err::Error(LeanError::expected(
                format!("'{word}'"),
                format!("{:?}", t.kind),
                t.start,
                t.line,
                t.col,
            ))),
        }
    }
}

const BRACKET_OPENERS: &[Sym] = &[
    Sym::LParen,
    Sym::LBrace,
    Sym::LBracket,
    Sym::LAngle,
    Sym::LStrictImp,
];
const BRACKET_CLOSERS: &[Sym] = &[
    Sym::RParen,
    Sym::RBrace,
    Sym::RBracket,
    Sym::RAngle,
    Sym::RStrictImp,
];

impl<'a> LeanParser<'a> {
    /// Parses the tactic sequence of a `by` block. Lean's `tacticSeq`
    /// rule: the anchor is the *first* tactic's column, and every
    /// subsequent tactic must either be separated by an explicit `;` or
    /// start at `col >= anchor` -- this lets a single-line `by exact
    /// foo` and a multi-line indented block both fall out of the same
    /// rule (in the single-line case the "block" just happens to
    /// contain one tactic, since the next token after it is either
    /// unrelated punctuation or a dedented follow-on construct).
    pub fn by_block(
        &self,
        ctx: Ctx,
        by_span: Span,
        i: Tokens<'a>,
    ) -> PResult<'a, Vec<Tactic>> {
        let first_tok = peek_tok(i).expect("Tokens should never be empty");
        if matches!(first_tok.kind, TokenKind::Eof) {
            return Err(nom::Err::Error(LeanError::expected(
                "at least one tactic after 'by'",
                "end of input",
                first_tok.start,
                first_tok.line,
                first_tok.col,
            )));
        }
        let anchor = first_tok.col;
        if first_tok.newline_before && anchor <= ctx.min_col {
            return Err(nom::Err::Error(LeanError::expected(
                "an indented tactic block after 'by'",
                format!("a token at column {anchor}"),
                first_tok.start,
                first_tok.line,
                first_tok.col,
            )));
        }
        // `by_span` is kept for a future revision that spans from `by`.
        let _ = by_span;
        // Anchor tactic-body term parsing at `anchor` itself (not
        // `anchor - 1`): a term inside e.g. `exact`/`apply`'s argument
        // may continue onto a more-indented line, but a token sitting
        // at exactly the anchor column is the *next tactic*, not a
        // continuation of this one -- `col_gt` must exclude it.
        let tctx = ctx.anchored_at(anchor.max(ctx.min_col));
        let (mut rest, first) = self.tactic(tctx, i)?;
        let mut tactics = vec![first];
        loop {
            let sep = alt((
                nom::combinator::map(sym(Sym::Semi), |_| ()),
                col_ge(anchor),
            ))(rest);
            let Ok((after_sep, ())) = sep else { break };
            match self.tactic(tctx, after_sep) {
                Ok((after_tac, t)) => {
                    tactics.push(t);
                    rest = after_tac;
                }
                Err(_) => break,
            }
        }
        Ok((rest, tactics))
    }

    /// One tactic, with `<;>` sequencing (which binds tighter than the
    /// newline/`;` sequencing in `by_block`) folded in as a left-nested
    /// `SeqFocus`.
    fn tactic(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Tactic> {
        let (mut rest, mut lhs) = self.tactic_primitive(ctx, i)?;
        loop {
            match sym(Sym::SeqFocus)(rest) {
                Ok((after_op, _)) => {
                    let (after_rhs, rhs) =
                        self.tactic_primitive(ctx, after_op)?;
                    let span = Span::merge(lhs.span, rhs.span);
                    lhs = Tactic::new(
                        TacticKind::SeqFocus {
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                        span,
                    );
                    rest = after_rhs;
                }
                Err(_) => break,
            }
        }
        Ok((rest, lhs))
    }

    fn tactic_primitive(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Tactic> {
        alt((
            |i| self.intro_tactic(i),
            move |i| self.exact_tactic(ctx, i),
            move |i| self.apply_tactic(ctx, i),
            move |i| self.unknown_tactic(ctx, i),
        ))(i)
    }

    fn intro_tactic(&self, i: Tokens<'a>) -> PResult<'a, Tactic> {
        let (i, (names, span)) = spanned(|i| {
            let (i, _) = ident_eq("intro")(i)?;
            // Bound the name list to the same source line as `intro`
            // itself: without this, `intro` (whose argument grammar is
            // just "one or more identifiers", indistinguishable at the
            // token level from another tactic's own name) would happily
            // swallow the next line's tactic name too when tactics are
            // separated only by indentation rather than an explicit
            // `;` (e.g. `by\n  intro n\n  exact foo n`).
            let line = crate::parser::commons::anchor_line(i);
            nom::multi::many1(nom::sequence::preceded(
                crate::parser::commons::same_line(line),
                move |i| self.binder_name(i),
            ))(i)
        })(i)?;
        Ok((i, Tactic::new(TacticKind::Intro { names }, span)))
    }

    fn exact_tactic(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Tactic> {
        let (i, (term, span)) = spanned(|i| {
            let (i, _) = ident_eq("exact")(i)?;
            self.term(ctx, 0, i)
        })(i)?;
        Ok((i, Tactic::new(TacticKind::Exact { term }, span)))
    }

    fn apply_tactic(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Tactic> {
        let (i, (term, span)) = spanned(|i| {
            let (i, _) = ident_eq("apply")(i)?;
            self.term(ctx, 0, i)
        })(i)?;
        Ok((i, Tactic::new(TacticKind::Apply { term }, span)))
    }

    /// Catch-all for any tactic not in the small modelled set above
    /// (`simp`, `rfl`, `induction n with ...`, `constructor`, ...).
    /// Consumes tokens verbatim, starting at the tactic name, until
    /// (at bracket depth 0) it hits `;`, `<;>`, end of input, or a
    /// dedent below the enclosing `by`-block's anchor -- tracking
    /// bracket depth so e.g. `simp [foo, bar]` isn't mistaken for two
    /// tactics at a stray `;` that doesn't exist here, and so a `,`- or
    /// `;`-bearing argument list isn't split early.
    fn unknown_tactic(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Tactic> {
        let t0 = peek_tok(i).expect("Tokens should never be empty");
        let name = match &t0.kind {
            TokenKind::Ident(s) => s.clone(),
            _ => {
                return Err(nom::Err::Error(LeanError::expected(
                    "a tactic",
                    format!("{:?}", t0.kind),
                    t0.start,
                    t0.line,
                    t0.col,
                )))
            }
        };
        let start_span = span_of(t0);
        // Consume the tactic-name token itself unconditionally: it
        // always belongs to this tactic no matter its column (it's
        // what the `by_block`/`col_ge(anchor)` separator logic already
        // used to admit it in the first place). The dedent check below
        // must only ever look at *subsequent* tokens -- applying it to
        // this first token too would compare its column against
        // `ctx.min_col == anchor` with `<=`, which is always true for
        // the tactic's own leading token and would make this parser
        // "succeed" without consuming anything, looping forever in
        // `by_block`.
        let (mut rest, _) = any_tok(i)?;
        let mut depth: i32 = 0;
        let mut last_span = start_span;
        loop {
            let t = peek_tok(rest).expect("Tokens should never be empty");
            if matches!(t.kind, TokenKind::Eof) {
                break;
            }
            if depth == 0 {
                if matches!(
                    t.kind,
                    TokenKind::Sym(Sym::Semi) | TokenKind::Sym(Sym::SeqFocus)
                ) {
                    break;
                }
                if t.newline_before && t.col <= ctx.min_col {
                    break;
                }
            }
            if let TokenKind::Sym(s) = &t.kind {
                if BRACKET_OPENERS.contains(s) {
                    depth += 1;
                } else if BRACKET_CLOSERS.contains(s) {
                    depth -= 1;
                }
            }
            last_span = span_of(t);
            let (r2, _) = any_tok(rest)?;
            rest = r2;
        }
        if depth != 0 {
            return Err(nom::Err::Error(LeanError::expected(
                "balanced brackets in tactic",
                "unbalanced brackets",
                t0.start,
                t0.line,
                t0.col,
            )));
        }
        let span = Span::merge(start_span, last_span);
        let text = self.text_between(span.start, span.end);
        Ok((rest, Tactic::new(TacticKind::Unknown { name, text }, span)))
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::lexer::lex;

    fn parse_by(src: &str) -> Vec<Tactic> {
        let toks = lex(src).unwrap();
        let p = LeanParser::new(src);
        let (rest, ((), by_span)) = spanned(crate::tokens::kw(
            crate::lexer::token::Keyword::By,
        ))(Tokens::new(&toks))
        .map(|(rest, (_, span))| (rest, ((), span)))
        .unwrap();
        let (rest, tactics) = p.by_block(Ctx::top(), by_span, rest).unwrap();
        assert!(
            crate::tokens::at_eof(rest),
            "leftover input: {:?}",
            rest.toks
        );
        tactics
    }

    #[test]
    fn single_line_exact() {
        let tactics = parse_by("by exact foo");
        assert_eq!(tactics.len(), 1);
        assert!(matches!(tactics[0].kind, TacticKind::Exact { .. }));
    }

    #[test]
    fn intro_then_exact_on_separate_lines() {
        let tactics = parse_by("by\n  intro n\n  exact foo n");
        assert_eq!(tactics.len(), 2);
        assert!(matches!(tactics[0].kind, TacticKind::Intro { .. }));
        assert!(matches!(tactics[1].kind, TacticKind::Exact { .. }));
    }

    #[test]
    fn apply_then_exact() {
        let tactics = parse_by("by\n  apply pq\n  exact p");
        assert_eq!(tactics.len(), 2);
        assert!(matches!(tactics[0].kind, TacticKind::Apply { .. }));
    }

    #[test]
    fn semicolon_separated_tactics_on_one_line() {
        let tactics = parse_by("by intro n; exact foo n");
        assert_eq!(tactics.len(), 2);
    }

    #[test]
    fn unknown_tactic_is_captured_verbatim() {
        let tactics = parse_by("by simp");
        match &tactics[0].kind {
            TacticKind::Unknown { name, text } => {
                assert_eq!(name, "simp");
                assert_eq!(text, "simp");
            }
            other => panic!("expected Unknown, got {other:?}"),
        }
    }

    #[test]
    fn unknown_tactic_with_bracketed_argument_list() {
        let tactics = parse_by("by simp [foo, bar]");
        match &tactics[0].kind {
            TacticKind::Unknown { name, text } => {
                assert_eq!(name, "simp");
                assert_eq!(text, "simp [foo, bar]");
            }
            other => panic!("expected Unknown, got {other:?}"),
        }
    }

    #[test]
    fn seq_focus_sequencing() {
        let tactics = parse_by("by intro n <;> exact foo n");
        assert_eq!(tactics.len(), 1);
        assert!(matches!(tactics[0].kind, TacticKind::SeqFocus { .. }));
    }
}
