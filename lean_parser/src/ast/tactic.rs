//! Tactics: a small, closed set (`intro`/`exact`/`apply`, matching the
//! `language` crate's own interactive-tactic vocabulary) plus a raw-text
//! catch-all for everything else, so real-world `by` blocks don't force
//! the whole surrounding declaration into an `Error` node.

use serde::{Deserialize, Serialize};

use crate::ast::term::Term;
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Tactic {
    #[serde(flatten)]
    pub kind: TacticKind,
    pub span: Span,
}

impl Tactic {
    pub fn new(kind: TacticKind, span: Span) -> Tactic {
        Tactic { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum TacticKind {
    /// `intro n m _`
    Intro {
        names: Vec<String>,
    },
    Exact {
        term: Term,
    },
    Apply {
        term: Term,
    },
    /// `t <;> u` -- apply `rhs` to every goal produced by `lhs`.
    SeqFocus {
        lhs: Box<Tactic>,
        rhs: Box<Tactic>,
    },
    /// Any recognised-shape-but-unmodelled tactic (`simp`, `rfl`,
    /// `induction n with ...`, `constructor`, ...), kept as raw source
    /// text rather than failing the parse.
    Unknown {
        name: String,
        text: String,
    },
    /// A tactic that failed to parse even as `Unknown` (e.g. malformed
    /// input inside `intro`/`exact`/`apply`'s own argument).
    Error {
        message: String,
        text: String,
    },
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::ast::term::TermKind;

    fn roundtrip(t: &Tactic) {
        let value = serde_json::to_value(t).unwrap();
        let back: Tactic = serde_json::from_value(value).unwrap();
        assert_eq!(t, &back, "Tactic should survive a JSON round-trip");
    }

    #[test]
    fn every_tactic_kind_variant_roundtrips() {
        let s = Span::DUMMY;
        let term = Term::new(TermKind::Var { name: "h".into() }, s);
        roundtrip(&Tactic::new(
            TacticKind::Intro {
                names: vec!["n".into(), "m".into()],
            },
            s,
        ));
        roundtrip(&Tactic::new(TacticKind::Exact { term: term.clone() }, s));
        roundtrip(&Tactic::new(TacticKind::Apply { term: term.clone() }, s));
        let intro = Box::new(Tactic::new(
            TacticKind::Intro {
                names: vec!["n".into()],
            },
            s,
        ));
        roundtrip(&Tactic::new(
            TacticKind::SeqFocus {
                lhs: intro.clone(),
                rhs: intro.clone(),
            },
            s,
        ));
        roundtrip(&Tactic::new(
            TacticKind::Unknown {
                name: "simp".into(),
                text: "simp".into(),
            },
            s,
        ));
        roundtrip(&Tactic::new(
            TacticKind::Error {
                message: "bad".into(),
                text: "???".into(),
            },
            s,
        ));
    }
}
