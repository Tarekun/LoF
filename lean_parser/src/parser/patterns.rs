//! Pattern parsing: patterns are *not* a separate grammar. A `match`
//! alternative's pattern is parsed with the ordinary term grammar
//! (`LeanParser::term`) and then reinterpreted structurally into a
//! `Pattern` (`term_to_pattern`). This is far less code than a second
//! grammar and, since it reuses the exact same parser, cannot drift out
//! of sync with what `terms.rs` accepts.

use crate::ast::term::{Pattern, PatternKind, Term, TermKind};
use crate::parser::{Ctx, LeanParser};
use crate::tokens::{PResult, Tokens};

impl<'a> LeanParser<'a> {
    pub fn pattern(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Pattern> {
        let (i, t) = self.term(ctx, 0, i)?;
        Ok((i, term_to_pattern(t)))
    }
}

/// Reinterprets a parsed `Term` as a `Pattern`. Deliberately does *not*
/// try to guess whether a bare, argument-less identifier is a
/// constructor or a bound variable by capitalization or any other
/// heuristic -- that's name resolution, explicitly out of scope. A
/// `Ctor` is only produced when the head carries arguments, or is
/// itself written with a leading dot (`.succ`).
fn term_to_pattern(t: Term) -> Pattern {
    let span = t.span;
    match t.kind {
        TermKind::Hole => Pattern::new(PatternKind::Wildcard, span),
        TermKind::Var { name } => Pattern::new(PatternKind::Var { name }, span),
        TermKind::DotIdent { name } => Pattern::new(
            PatternKind::Ctor {
                name,
                dotted: true,
                args: vec![],
            },
            span,
        ),
        TermKind::App { func, args } => {
            let args: Vec<Pattern> =
                args.into_iter().map(term_to_pattern).collect();
            match func.kind {
                TermKind::Var { name } => Pattern::new(
                    PatternKind::Ctor {
                        name,
                        dotted: false,
                        args,
                    },
                    span,
                ),
                TermKind::DotIdent { name } => Pattern::new(
                    PatternKind::Ctor {
                        name,
                        dotted: true,
                        args,
                    },
                    span,
                ),
                other => Pattern::new(
                    PatternKind::Other {
                        text: format!("{other:?}"),
                    },
                    span,
                ),
            }
        }
        // `n :: ns` -- the one infix operator meaningful in pattern
        // position (list cons); every other `BinOp`/`UnOp` falls
        // through to `Other` below.
        TermKind::BinOp { op, lhs, rhs } if op == "::" => Pattern::new(
            PatternKind::Ctor {
                name: "List.cons".to_string(),
                dotted: false,
                args: vec![term_to_pattern(*lhs), term_to_pattern(*rhs)],
            },
            span,
        ),
        TermKind::Nat { value, .. } => {
            Pattern::new(PatternKind::Nat { value }, span)
        }
        TermKind::Str { value } => {
            Pattern::new(PatternKind::Str { value }, span)
        }
        TermKind::Tuple { elems } => Pattern::new(
            PatternKind::Tuple {
                elems: elems.into_iter().map(term_to_pattern).collect(),
            },
            span,
        ),
        TermKind::Anonymous { elems } => Pattern::new(
            PatternKind::Anonymous {
                elems: elems.into_iter().map(term_to_pattern).collect(),
            },
            span,
        ),
        other => Pattern::new(
            PatternKind::Other {
                text: format!("{other:?}"),
            },
            span,
        ),
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::lexer::lex;
    use crate::tokens::Tokens as Toks;

    fn parse(src: &str) -> Pattern {
        let toks = lex(src).unwrap();
        let p = LeanParser::new(src);
        let (rest, pat) = p.pattern(Ctx::top(), Toks::new(&toks)).unwrap();
        assert!(crate::tokens::at_eof(rest));
        pat
    }

    #[test]
    fn wildcard_pattern() {
        assert!(matches!(parse("_").kind, PatternKind::Wildcard));
    }

    #[test]
    fn variable_pattern() {
        assert!(matches!(
            parse("n").kind,
            PatternKind::Var { ref name } if name == "n"
        ));
    }

    #[test]
    fn bare_dot_ident_is_a_nullary_constructor() {
        match parse(".z").kind {
            PatternKind::Ctor { name, dotted, args } => {
                assert_eq!(name, "z");
                assert!(dotted);
                assert!(args.is_empty());
            }
            other => panic!("expected Ctor, got {other:?}"),
        }
    }

    #[test]
    fn applied_dot_ident_is_a_constructor_with_args() {
        match parse(".s nn").kind {
            PatternKind::Ctor { name, dotted, args } => {
                assert_eq!(name, "s");
                assert!(dotted);
                assert_eq!(args.len(), 1);
                assert!(matches!(args[0].kind, PatternKind::Var { .. }));
            }
            other => panic!("expected Ctor, got {other:?}"),
        }
    }

    #[test]
    fn cons_pattern() {
        match parse("h :: t").kind {
            PatternKind::Ctor { name, args, .. } => {
                assert_eq!(name, "List.cons");
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected Ctor, got {other:?}"),
        }
    }

    #[test]
    fn nested_constructor_pattern() {
        // Nat.succ (Nat.succ n) -- undotted, dotted-name head.
        match parse("Nat.succ n").kind {
            PatternKind::Ctor { name, dotted, args } => {
                assert_eq!(name, "Nat.succ");
                assert!(!dotted);
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Ctor, got {other:?}"),
        }
    }
}
