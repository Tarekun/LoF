//! Ties the parser together: `parse_module` runs the top-level
//! declaration loop with error recovery, producing a `Module` that is
//! always well-formed JSON even when parts of the source didn't parse
//! (see `ast::decl::DeclKind::Error`).

use nom::Offset;

use crate::ast::decl::{Decl, DeclKind, Modifiers, Module};
use crate::error::LeanError;
use crate::lexer::token::{Keyword, Token, TokenKind};
use crate::parser::{Ctx, LeanParser};
use crate::span::Span;
use crate::tokens::{any_tok, at_eof, peek_tok, span_of, Tokens};

/// Parses a full module's token stream into a `Module`. Never returns
/// `Err` itself (parse failures become `DeclKind::Error` nodes) --
/// `Result` is kept in the signature so a genuinely unrecoverable
/// situation (there is none today) has somewhere to go, and so callers
/// don't need to special-case this function relative to `lex`.
pub fn parse_module(
    name: &str,
    src: &str,
    toks: &[Token],
) -> Result<Module, LeanError> {
    let p = LeanParser::new(src);
    let input = Tokens::new(toks);
    let start_span =
        span_of(peek_tok(input).expect("Tokens should never be empty"));
    let (decls, end_span) = parse_decls_with_recovery(&p, input, start_span);
    Ok(Module {
        path: name.to_string(),
        doc: None,
        decls,
        span: Span::merge(start_span, end_span),
    })
}

/// True whether any declaration in `decls` (recursively -- there's no
/// nesting today, but this stays correct if that changes) is an error
/// node. Used by the CLI to decide the process exit code.
pub fn has_errors(decls: &[Decl]) -> bool {
    decls
        .iter()
        .any(|d| matches!(d.kind, DeclKind::Error { .. }))
}

fn parse_decls_with_recovery<'a>(
    p: &LeanParser<'a>,
    mut i: Tokens<'a>,
    start_span: Span,
) -> (Vec<Decl>, Span) {
    let mut decls = Vec::new();
    let mut last_span = start_span;
    loop {
        if at_eof(i) {
            break;
        }
        match p.decl(Ctx::top(), i) {
            Ok((rest, d)) => {
                let consumed = i.offset(&rest);
                last_span = d.span;
                decls.push(d);
                if consumed == 0 {
                    // A declaration parser that reports success without
                    // consuming a token would loop forever; treat it as
                    // an internal-invariant violation and force
                    // recovery instead (this should never actually
                    // trigger -- every `decl_kind` branch consumes at
                    // least its leading keyword).
                    if at_eof(rest) {
                        break;
                    }
                    let (r2, err_decl) = recover(
                        p,
                        rest,
                        LeanError::internal(
                            &"declaration parser made no progress",
                        ),
                    );
                    last_span = err_decl.span;
                    decls.push(err_decl);
                    i = r2;
                } else {
                    i = rest;
                }
            }
            Err(e) => {
                let e = match e {
                    nom::Err::Error(e) | nom::Err::Failure(e) => e,
                    nom::Err::Incomplete(needed) => LeanError::internal(
                        &format!("nom::Err::Incomplete({needed:?})"),
                    ),
                };
                let (rest, err_decl) = recover(p, i, e);
                last_span = err_decl.span;
                decls.push(err_decl);
                i = rest;
            }
        }
    }
    (decls, last_span)
}

/// Recovers from a declaration parse failure: skips at least one token
/// (guaranteeing forward progress) and continues skipping until it
/// reaches end of input or a token that plausibly starts a fresh
/// declaration at column 0 (a declaration keyword, doc comment, or
/// attribute), then resumes the main loop from there.
fn recover<'a>(
    p: &LeanParser<'a>,
    i: Tokens<'a>,
    err: LeanError,
) -> (Tokens<'a>, Decl) {
    let start = peek_tok(i).expect("Tokens should never be empty");
    let start_span = span_of(start);
    let (mut rest, skipped_first) =
        any_tok(i).expect("recover is only called when not at Eof");
    let mut last_span = span_of(skipped_first);
    loop {
        let t = peek_tok(rest).expect("Tokens should never be empty");
        if matches!(t.kind, TokenKind::Eof) {
            break;
        }
        if t.col == 0 && is_decl_resync_point(&t.kind) {
            break;
        }
        last_span = span_of(t);
        let (r2, _) = any_tok(rest).expect("not at Eof, checked above");
        rest = r2;
    }
    let span = Span::merge(start_span, last_span);
    let text = p.text_between(span.start, span.end);
    (
        rest,
        Decl {
            doc: None,
            attrs: vec![],
            kind: DeclKind::Error {
                message: err.to_string(),
                text,
            },
            modifiers: Modifiers::default(),
            span,
        },
    )
}

fn is_decl_resync_point(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Keyword(Keyword::Def)
            | TokenKind::Keyword(Keyword::Abbrev)
            | TokenKind::Keyword(Keyword::Theorem)
            | TokenKind::Keyword(Keyword::Lemma)
            | TokenKind::Keyword(Keyword::Example)
            | TokenKind::Keyword(Keyword::Axiom)
            | TokenKind::Keyword(Keyword::Inductive)
            | TokenKind::Keyword(Keyword::Import)
            | TokenKind::DocComment(_)
            | TokenKind::Attr(_)
    )
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::lexer::lex;

    fn parse(src: &str) -> Module {
        let toks = lex(src).unwrap();
        parse_module("test.lean", src, &toks).unwrap()
    }

    #[test]
    fn multiple_declarations_at_top_level() {
        let m = parse("def a := 1\ndef b := 2\ndef c := 3");
        assert_eq!(m.decls.len(), 3);
        assert!(!has_errors(&m.decls));
    }

    #[test]
    fn a_bad_declaration_becomes_an_error_node_and_parsing_continues() {
        let m = parse("def a := \ndef b := 2");
        // The first `def`'s body parse fails (a dedented `def` at
        // column 0 can't continue its RHS term), producing an `Error`
        // node; the second `def` should still parse cleanly.
        assert!(has_errors(&m.decls));
        assert!(m.decls.iter().any(|d| matches!(
            d.kind,
            DeclKind::Def { ref name, .. } if name == "b"
        )));
    }

    #[test]
    fn empty_module_parses_to_no_declarations() {
        let m = parse("");
        assert!(m.decls.is_empty());
    }

    #[test]
    fn only_comments_parses_to_no_declarations() {
        let m = parse("-- just a comment\n/- and a block comment -/");
        assert!(m.decls.is_empty());
    }
}
