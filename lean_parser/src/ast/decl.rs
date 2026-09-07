//! Modules and top-level declarations.

use serde::{Deserialize, Serialize};

use crate::ast::term::{Binder, Term};
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Module {
    pub path: String,
    /// A leading `/-! ... -/` module doc comment, if the lexer captured
    /// one at the very start of the file. (Module docs are currently
    /// skipped as trivia by the lexer -- see `lexer::scanner` -- so this
    /// is reserved for a future revision that keeps them; always `None`
    /// today.)
    pub doc: Option<String>,
    pub decls: Vec<Decl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Decl {
    pub doc: Option<String>,
    /// Raw `@[...]` texts, in source order, each without its `@[`/`]`
    /// delimiters.
    pub attrs: Vec<String>,
    #[serde(flatten)]
    pub kind: DeclKind,
    pub modifiers: Modifiers,
    pub span: Span,
}

#[derive(
    Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize,
)]
#[serde(rename_all = "camelCase", default)]
pub struct Modifiers {
    pub is_partial: bool,
    pub is_private: bool,
    pub is_protected: bool,
    pub is_unsafe: bool,
    pub is_noncomputable: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum DeclKind {
    Import {
        module: String,
    },
    /// Covers both `def` and `abbrev` (`is_abbrev` distinguishes them).
    /// There is no separate `is_rec` flag as in the `language` crate's
    /// `Statement::Fun` -- Lean doesn't mark recursion syntactically, a
    /// `def` referencing its own name in its body simply is recursive.
    Def {
        name: String,
        binders: Vec<Binder>,
        ty: Option<Term>,
        body: Term,
        is_abbrev: bool,
    },
    /// Covers both `theorem` and `lemma` (`keyword` records which
    /// spelling was used).
    Theorem {
        name: String,
        binders: Vec<Binder>,
        ty: Term,
        proof: Term,
        keyword: String,
    },
    Example {
        binders: Vec<Binder>,
        ty: Option<Term>,
        body: Term,
    },
    Axiom {
        name: String,
        binders: Vec<Binder>,
        ty: Term,
    },
    Inductive {
        name: String,
        binders: Vec<Binder>,
        ty: Option<Term>,
        ctors: Vec<Ctor>,
        deriving: Vec<String>,
    },
    /// A recovery node produced by the top-level declaration loop when a
    /// chunk of source couldn't be parsed as any known declaration;
    /// never produced for a clean parse.
    Error {
        message: String,
        text: String,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Ctor {
    pub doc: Option<String>,
    pub name: String,
    pub binders: Vec<Binder>,
    pub ty: Option<Term>,
    pub span: Span,
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::ast::term::TermKind;

    fn roundtrip(d: &Decl) {
        let value = serde_json::to_value(d).unwrap();
        let back: Decl = serde_json::from_value(value).unwrap();
        assert_eq!(d, &back, "Decl should survive a JSON round-trip");
    }

    fn wrap(kind: DeclKind) -> Decl {
        Decl {
            doc: None,
            attrs: vec![],
            kind,
            modifiers: Modifiers::default(),
            span: Span::DUMMY,
        }
    }

    #[test]
    fn every_decl_kind_variant_roundtrips() {
        let s = Span::DUMMY;
        let ty = Term::new(
            TermKind::Sort {
                sort: crate::ast::term::SortKind::Type,
                level: None,
            },
            s,
        );
        roundtrip(&wrap(DeclKind::Import {
            module: "Nat".into(),
        }));
        roundtrip(&wrap(DeclKind::Def {
            name: "id".into(),
            binders: vec![],
            ty: Some(ty.clone()),
            body: ty.clone(),
            is_abbrev: false,
        }));
        roundtrip(&wrap(DeclKind::Theorem {
            name: "t".into(),
            binders: vec![],
            ty: ty.clone(),
            proof: ty.clone(),
            keyword: "theorem".into(),
        }));
        roundtrip(&wrap(DeclKind::Example {
            binders: vec![],
            ty: None,
            body: ty.clone(),
        }));
        roundtrip(&wrap(DeclKind::Axiom {
            name: "P".into(),
            binders: vec![],
            ty: ty.clone(),
        }));
        roundtrip(&wrap(DeclKind::Inductive {
            name: "Nat".into(),
            binders: vec![],
            ty: Some(ty.clone()),
            ctors: vec![Ctor {
                doc: None,
                name: "z".into(),
                binders: vec![],
                ty: None,
                span: s,
            }],
            deriving: vec!["Repr".into()],
        }));
        roundtrip(&wrap(DeclKind::Error {
            message: "bad".into(),
            text: "???".into(),
        }));
    }

    #[test]
    fn module_roundtrips() {
        let m = Module {
            path: "Foo.lean".into(),
            doc: None,
            decls: vec![wrap(DeclKind::Import {
                module: "Nat".into(),
            })],
            span: Span::DUMMY,
        };
        let value = serde_json::to_value(&m).unwrap();
        let back: Module = serde_json::from_value(value).unwrap();
        assert_eq!(m, back);
    }

    #[test]
    fn modifiers_default_to_false() {
        let m = Modifiers::default();
        assert_eq!(
            m,
            Modifiers {
                is_partial: false,
                is_private: false,
                is_protected: false,
                is_unsafe: false,
                is_noncomputable: false,
            }
        );
    }
}
