//! Terms, binders, and patterns.

use serde::{Deserialize, Serialize};

use crate::ast::tactic::Tactic;
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Term {
    #[serde(flatten)]
    pub kind: TermKind,
    pub span: Span,
}

impl Term {
    pub fn new(kind: TermKind, span: Span) -> Term {
        Term { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum TermKind {
    /// `x`, `Nat.succ` -- purely syntactic; no name resolution is
    /// performed, so a dotted name is just a string.
    Var {
        name: String,
    },
    /// `.succ` -- an anonymous-constructor-style dotted name.
    DotIdent {
        name: String,
    },
    /// `_`
    Hole,
    /// `?m`, `?_`
    SyntheticHole {
        name: Option<String>,
    },
    /// `Type`, `Prop`, `Sort u`
    Sort {
        sort: SortKind,
        level: Option<String>,
    },
    Nat {
        value: u64,
        raw: String,
    },
    Str {
        value: String,
    },
    Char {
        value: char,
    },
    /// `f a b` -- juxtaposition application, n-ary (Lean is curried
    /// underneath, but the surface shape is recorded flattened).
    App {
        func: Box<Term>,
        args: Vec<Term>,
    },
    /// `fun (x : T) y => body`, `λ x => body`
    Fun {
        binders: Vec<Binder>,
        body: Box<Term>,
    },
    /// `∀ (x : T) y, body` and `(x : T) → body` (both spellings of the
    /// dependent product collapse to this one node).
    Forall {
        binders: Vec<Binder>,
        body: Box<Term>,
    },
    /// `∃ x : T, body`
    Exists {
        binders: Vec<Binder>,
        body: Box<Term>,
    },
    /// `A → B` -- the non-dependent arrow, kept distinct from `Forall`
    /// (mirroring the `language` crate's `Arrow`/`TypeProduct` split) so
    /// a downstream LoF <-> Lean bridge is a direct structural map.
    Arrow {
        domain: Box<Term>,
        codomain: Box<Term>,
    },
    /// Any table-driven infix operator except `→` (see
    /// `parser::precedence`).
    BinOp {
        op: String,
        lhs: Box<Term>,
        rhs: Box<Term>,
    },
    /// `¬p`, `-n`
    UnOp {
        op: String,
        operand: Box<Term>,
    },
    /// `let x : T := v; body` / `have h : T := v; body` (`is_have`
    /// distinguishes the two, which otherwise parse identically).
    Let {
        name: String,
        ty: Option<Box<Term>>,
        value: Box<Term>,
        body: Box<Term>,
        is_have: bool,
    },
    /// `match e, e2 with | p, q => b`
    Match {
        scrutinees: Vec<Term>,
        alts: Vec<MatchAlt>,
    },
    /// `by tac; tac`
    By {
        tactics: Vec<Tactic>,
    },
    /// `(a, b, c)`
    Tuple {
        elems: Vec<Term>,
    },
    /// `⟨a, b⟩`
    Anonymous {
        elems: Vec<Term>,
    },
    /// `if c then a else b` -- parsed syntactically only (no elaboration
    /// of the `Decidable`/`ite` machinery); kept cheap because it's
    /// common enough in real files that skipping it would force many
    /// otherwise-in-scope files into `Error` nodes.
    Ite {
        cond: Box<Term>,
        then_branch: Box<Term>,
        else_branch: Box<Term>,
    },
    /// A term that failed to parse, when recovery is enabled at an
    /// enclosing level. Never produced for a clean parse.
    Error {
        message: String,
        text: String,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum SortKind {
    Type,
    Prop,
    Sort,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum BinderInfo {
    Explicit,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// A binder group: `(x y : T)`, `{x : T}`, `⦃x⦄`, `[Inst]`, or a bare
/// `x`. Parsed purely as syntax -- `BinderInfo` records the bracket
/// shape used, with no typeclass-resolution semantics attached to
/// `InstImplicit`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Binder {
    pub names: Vec<String>,
    pub ty: Option<Box<Term>>,
    pub info: BinderInfo,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MatchAlt {
    pub patterns: Vec<Pattern>,
    pub rhs: Term,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Pattern {
    #[serde(flatten)]
    pub kind: PatternKind,
    pub span: Span,
}

impl Pattern {
    pub fn new(kind: PatternKind, span: Span) -> Pattern {
        Pattern { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum PatternKind {
    Var {
        name: String,
    },
    Wildcard,
    /// `Nat.succ n`, `.cons h t` -- `dotted` records whether the head
    /// was written with a leading dot. Deliberately does *not* try to
    /// distinguish a constructor from a bound variable by capitalization
    /// or any other heuristic (that's name resolution, out of scope):
    /// this variant is only produced when the head carries arguments or
    /// is itself a `DotIdent`.
    Ctor {
        name: String,
        dotted: bool,
        args: Vec<Pattern>,
    },
    Nat {
        value: u64,
    },
    Str {
        value: String,
    },
    Tuple {
        elems: Vec<Pattern>,
    },
    Anonymous {
        elems: Vec<Pattern>,
    },
    /// A pattern-position construct not modelled by this grammar,
    /// recorded verbatim rather than failing the whole `match`.
    Other {
        text: String,
    },
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    fn roundtrip(t: &Term) {
        let value = serde_json::to_value(t).unwrap();
        let back: Term = serde_json::from_value(value).unwrap();
        assert_eq!(t, &back, "Term should survive a JSON round-trip");
    }

    fn roundtrip_pattern(p: &Pattern) {
        let value = serde_json::to_value(p).unwrap();
        let back: Pattern = serde_json::from_value(value).unwrap();
        assert_eq!(p, &back, "Pattern should survive a JSON round-trip");
    }

    #[test]
    fn every_term_kind_variant_roundtrips() {
        let s = Span::DUMMY;
        roundtrip(&Term::new(TermKind::Var { name: "x".into() }, s));
        roundtrip(&Term::new(
            TermKind::DotIdent {
                name: "succ".into(),
            },
            s,
        ));
        roundtrip(&Term::new(TermKind::Hole, s));
        roundtrip(&Term::new(
            TermKind::SyntheticHole {
                name: Some("m".into()),
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Sort {
                sort: SortKind::Type,
                level: None,
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Sort {
                sort: SortKind::Sort,
                level: Some("u".into()),
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Nat {
                value: 3,
                raw: "3".into(),
            },
            s,
        ));
        roundtrip(&Term::new(TermKind::Str { value: "hi".into() }, s));
        roundtrip(&Term::new(TermKind::Char { value: 'x' }, s));
        let var = Box::new(Term::new(TermKind::Var { name: "f".into() }, s));
        roundtrip(&Term::new(
            TermKind::App {
                func: var.clone(),
                args: vec![*var.clone()],
            },
            s,
        ));
        let binder = Binder {
            names: vec!["x".into()],
            ty: None,
            info: BinderInfo::Explicit,
            span: s,
        };
        roundtrip(&Term::new(
            TermKind::Fun {
                binders: vec![binder.clone()],
                body: var.clone(),
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Forall {
                binders: vec![binder.clone()],
                body: var.clone(),
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Exists {
                binders: vec![binder.clone()],
                body: var.clone(),
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Arrow {
                domain: var.clone(),
                codomain: var.clone(),
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::BinOp {
                op: "+".into(),
                lhs: var.clone(),
                rhs: var.clone(),
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::UnOp {
                op: "-".into(),
                operand: var.clone(),
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Let {
                name: "x".into(),
                ty: None,
                value: var.clone(),
                body: var.clone(),
                is_have: false,
            },
            s,
        ));
        let pat = Pattern::new(PatternKind::Wildcard, s);
        roundtrip(&Term::new(
            TermKind::Match {
                scrutinees: vec![*var.clone()],
                alts: vec![MatchAlt {
                    patterns: vec![pat.clone()],
                    rhs: *var.clone(),
                    span: s,
                }],
            },
            s,
        ));
        roundtrip(&Term::new(TermKind::By { tactics: vec![] }, s));
        roundtrip(&Term::new(
            TermKind::Tuple {
                elems: vec![*var.clone()],
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Anonymous {
                elems: vec![*var.clone()],
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Ite {
                cond: var.clone(),
                then_branch: var.clone(),
                else_branch: var.clone(),
            },
            s,
        ));
        roundtrip(&Term::new(
            TermKind::Error {
                message: "oops".into(),
                text: "??".into(),
            },
            s,
        ));
    }

    #[test]
    fn every_pattern_kind_variant_roundtrips() {
        let s = Span::DUMMY;
        roundtrip_pattern(&Pattern::new(
            PatternKind::Var { name: "x".into() },
            s,
        ));
        roundtrip_pattern(&Pattern::new(PatternKind::Wildcard, s));
        roundtrip_pattern(&Pattern::new(
            PatternKind::Ctor {
                name: "cons".into(),
                dotted: false,
                args: vec![Pattern::new(PatternKind::Wildcard, s)],
            },
            s,
        ));
        roundtrip_pattern(&Pattern::new(PatternKind::Nat { value: 0 }, s));
        roundtrip_pattern(&Pattern::new(
            PatternKind::Str { value: "hi".into() },
            s,
        ));
        roundtrip_pattern(&Pattern::new(
            PatternKind::Tuple {
                elems: vec![Pattern::new(PatternKind::Wildcard, s)],
            },
            s,
        ));
        roundtrip_pattern(&Pattern::new(
            PatternKind::Anonymous {
                elems: vec![Pattern::new(PatternKind::Wildcard, s)],
            },
            s,
        ));
        roundtrip_pattern(&Pattern::new(
            PatternKind::Other {
                text: "h : T".into(),
            },
            s,
        ));
    }

    #[test]
    fn term_json_shape_is_internally_tagged_and_flattened() {
        let t = Term::new(TermKind::Var { name: "x".into() }, Span::DUMMY);
        let v = serde_json::to_value(&t).unwrap();
        assert_eq!(v["kind"], "var");
        assert_eq!(v["name"], "x");
        assert!(v["span"].is_object());
    }
}
