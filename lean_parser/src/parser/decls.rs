//! Declaration parsing: modifiers, attributes, doc-comment attachment,
//! `import`, `def`/`abbrev`, `theorem`/`lemma`, `example`, `axiom`, and
//! `inductive`.

use nom::branch::alt;
use nom::combinator::{map, opt};
use nom::multi::{many0, separated_list1};
use nom::sequence::preceded;

use crate::ast::decl::{Ctor, Decl, DeclKind, Modifiers};
use crate::lexer::token::Keyword;
use crate::lexer::token::Sym;
use crate::parser::commons::spanned;
use crate::parser::{Ctx, LeanParser};
use crate::span::Span;
use crate::tokens::{attr, doc_comment, ident, kw, sym, PResult, Tokens};

impl<'a> LeanParser<'a> {
    /// One top-level declaration, including its leading doc comment,
    /// attributes, and modifiers.
    pub fn decl(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Decl> {
        let (i, (doc, attrs)) = self.decl_prefix(i)?;
        let (i, ((modifiers, (kind, _kind_span)), span)) = spanned(|i| {
            let (i, modifiers) = self.modifiers(i)?;
            let (i, kind_and_span) = self.decl_kind(ctx, i)?;
            Ok((i, (modifiers, kind_and_span)))
        })(i)?;
        Ok((
            i,
            Decl {
                doc,
                attrs,
                kind,
                modifiers,
                span,
            },
        ))
    }

    fn decl_prefix(
        &self,
        i: Tokens<'a>,
    ) -> PResult<'a, (Option<String>, Vec<String>)> {
        let (i, doc) = opt(doc_comment)(i)?;
        let (i, attrs) = many0(attr)(i)?;
        Ok((
            i,
            (
                doc.map(|(text, _)| text),
                attrs.into_iter().map(|(text, _)| text).collect(),
            ),
        ))
    }

    fn modifiers(&self, i: Tokens<'a>) -> PResult<'a, Modifiers> {
        let mut m = Modifiers::default();
        let mut rest = i;
        loop {
            if let Ok((r2, _)) = kw(Keyword::Partial)(rest) {
                m.is_partial = true;
                rest = r2;
                continue;
            }
            if let Ok((r2, _)) = kw(Keyword::Private)(rest) {
                m.is_private = true;
                rest = r2;
                continue;
            }
            if let Ok((r2, _)) = kw(Keyword::Protected)(rest) {
                m.is_protected = true;
                rest = r2;
                continue;
            }
            if let Ok((r2, _)) = kw(Keyword::Unsafe)(rest) {
                m.is_unsafe = true;
                rest = r2;
                continue;
            }
            if let Ok((r2, _)) = kw(Keyword::Noncomputable)(rest) {
                m.is_noncomputable = true;
                rest = r2;
                continue;
            }
            break;
        }
        Ok((rest, m))
    }

    fn decl_kind(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, (DeclKind, Span)> {
        alt((
            |i| self.import_decl(i),
            move |i| self.def_decl(ctx, i),
            move |i| self.theorem_decl(ctx, i),
            move |i| self.example_decl(ctx, i),
            move |i| self.axiom_decl(ctx, i),
            move |i| self.inductive_decl(ctx, i),
        ))(i)
    }

    fn import_decl(&self, i: Tokens<'a>) -> PResult<'a, (DeclKind, Span)> {
        let (i, (module, span)) = spanned(|i| {
            let (i, _) = kw(Keyword::Import)(i)?;
            let (i, (name, _)) = ident(i)?;
            Ok((i, name))
        })(i)?;
        Ok((i, (DeclKind::Import { module }, span)))
    }

    fn def_decl(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, (DeclKind, Span)> {
        let (i, ((is_abbrev, name, binders, ty, body), span)) = spanned(|i| {
            let (i, is_abbrev) = alt((
                map(kw(Keyword::Def), |_| false),
                map(kw(Keyword::Abbrev), |_| true),
            ))(i)?;
            let (i, (name, _)) = ident(i)?;
            let (i, binders) = self.binder_list(ctx, i)?;
            let (i, ty) =
                opt(preceded(sym(Sym::Colon), |i| self.term(ctx, 0, i)))(i)?;
            let (i, _) = sym(Sym::ColonEq)(i)?;
            let (i, body) = self.term(ctx, 0, i)?;
            Ok((i, (is_abbrev, name, binders, ty, body)))
        })(i)?;
        Ok((
            i,
            (
                DeclKind::Def {
                    name,
                    binders,
                    ty,
                    body,
                    is_abbrev,
                },
                span,
            ),
        ))
    }

    fn theorem_decl(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, (DeclKind, Span)> {
        let (i, ((keyword, name, binders, ty, proof), span)) = spanned(|i| {
            let (i, keyword) = alt((
                map(kw(Keyword::Theorem), |_| "theorem".to_string()),
                map(kw(Keyword::Lemma), |_| "lemma".to_string()),
            ))(i)?;
            let (i, (name, _)) = ident(i)?;
            let (i, binders) = self.binder_list(ctx, i)?;
            let (i, _) = sym(Sym::Colon)(i)?;
            let (i, ty) = self.term(ctx, 0, i)?;
            let (i, _) = sym(Sym::ColonEq)(i)?;
            let (i, proof) = self.term(ctx, 0, i)?;
            Ok((i, (keyword, name, binders, ty, proof)))
        })(i)?;
        Ok((
            i,
            (
                DeclKind::Theorem {
                    name,
                    binders,
                    ty,
                    proof,
                    keyword,
                },
                span,
            ),
        ))
    }

    fn example_decl(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, (DeclKind, Span)> {
        let (i, ((binders, ty, body), span)) = spanned(|i| {
            let (i, _) = kw(Keyword::Example)(i)?;
            let (i, binders) = self.binder_list(ctx, i)?;
            let (i, ty) =
                opt(preceded(sym(Sym::Colon), |i| self.term(ctx, 0, i)))(i)?;
            let (i, _) = sym(Sym::ColonEq)(i)?;
            let (i, body) = self.term(ctx, 0, i)?;
            Ok((i, (binders, ty, body)))
        })(i)?;
        Ok((i, (DeclKind::Example { binders, ty, body }, span)))
    }

    fn axiom_decl(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, (DeclKind, Span)> {
        let (i, ((name, binders, ty), span)) = spanned(|i| {
            let (i, _) = kw(Keyword::Axiom)(i)?;
            let (i, (name, _)) = ident(i)?;
            let (i, binders) = self.binder_list(ctx, i)?;
            let (i, _) = sym(Sym::Colon)(i)?;
            let (i, ty) = self.term(ctx, 0, i)?;
            Ok((i, (name, binders, ty)))
        })(i)?;
        Ok((i, (DeclKind::Axiom { name, binders, ty }, span)))
    }

    fn inductive_decl(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, (DeclKind, Span)> {
        let (i, ((name, binders, ty, ctors, deriving), span)) = spanned(|i| {
            let (i, _) = kw(Keyword::Inductive)(i)?;
            let (i, (name, _)) = ident(i)?;
            let (i, binders) = self.binder_list(ctx, i)?;
            let (i, ty) =
                opt(preceded(sym(Sym::Colon), |i| self.term(ctx, 0, i)))(i)?;
            let (i, _) = opt(kw(Keyword::Where))(i)?;
            let (i, ctors) = many0(|i| self.ctor(ctx, i))(i)?;
            let (i, deriving) = opt(preceded(
                kw(Keyword::Deriving),
                separated_list1(sym(Sym::Comma), map(ident, |(n, _)| n)),
            ))(i)?;
            Ok((i, (name, binders, ty, ctors, deriving.unwrap_or_default())))
        })(i)?;
        Ok((
            i,
            (
                DeclKind::Inductive {
                    name,
                    binders,
                    ty,
                    ctors,
                    deriving,
                },
                span,
            ),
        ))
    }

    fn ctor(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Ctor> {
        let (i, ((doc, name, binders, ty), span)) = spanned(|i| {
            let (i, doc) = opt(doc_comment)(i)?;
            let (i, _) = sym(Sym::Bar)(i)?;
            let (i, (name, _)) = ident(i)?;
            let (i, binders) = self.binder_list(ctx, i)?;
            let (i, ty) =
                opt(preceded(sym(Sym::Colon), |i| self.term(ctx, 0, i)))(i)?;
            Ok((i, (doc.map(|(t, _)| t), name, binders, ty)))
        })(i)?;
        Ok((
            i,
            Ctor {
                doc,
                name,
                binders,
                ty,
                span,
            },
        ))
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::lexer::lex;

    fn parse(src: &str) -> Decl {
        let toks = lex(src).unwrap();
        let p = LeanParser::new(src);
        let (rest, d) = p.decl(Ctx::top(), Tokens::new(&toks)).unwrap();
        assert!(
            crate::tokens::at_eof(rest),
            "leftover input: {:?}",
            rest.toks
        );
        d
    }

    #[test]
    fn simple_def() {
        let d = parse("def id (x : Nat) : Nat := x");
        match d.kind {
            DeclKind::Def {
                name,
                binders,
                is_abbrev,
                ..
            } => {
                assert_eq!(name, "id");
                assert_eq!(binders.len(), 1);
                assert!(!is_abbrev);
            }
            other => panic!("expected Def, got {other:?}"),
        }
    }

    #[test]
    fn abbrev_is_marked() {
        let d = parse("abbrev Foo := Nat");
        match d.kind {
            DeclKind::Def { is_abbrev, .. } => assert!(is_abbrev),
            other => panic!("expected Def, got {other:?}"),
        }
    }

    #[test]
    fn theorem_records_its_keyword_spelling() {
        let d = parse("lemma foo : P := proof");
        match d.kind {
            DeclKind::Theorem { keyword, .. } => assert_eq!(keyword, "lemma"),
            other => panic!("expected Theorem, got {other:?}"),
        }
    }

    #[test]
    fn axiom_decl() {
        let d = parse("axiom P : Prop");
        assert!(matches!(d.kind, DeclKind::Axiom { .. }));
    }

    #[test]
    fn import_decl() {
        let d = parse("import Nat");
        match d.kind {
            DeclKind::Import { module } => assert_eq!(module, "Nat"),
            other => panic!("expected Import, got {other:?}"),
        }
    }

    #[test]
    fn inductive_with_constructors() {
        let d = parse(
            "inductive Nat' : Type where\n  | z : Nat'\n  | s : Nat' -> Nat'",
        );
        match d.kind {
            DeclKind::Inductive { name, ctors, .. } => {
                assert_eq!(name, "Nat'");
                assert_eq!(ctors.len(), 2);
                assert_eq!(ctors[0].name, "z");
                assert_eq!(ctors[1].name, "s");
            }
            other => panic!("expected Inductive, got {other:?}"),
        }
    }

    #[test]
    fn inductive_with_parameters() {
        let d = parse(
            "inductive List' (T : Type) : Type where\n  \
             | nil : List' T\n  | cons : T -> List' T -> List' T",
        );
        match d.kind {
            DeclKind::Inductive {
                name,
                binders,
                ctors,
                ..
            } => {
                assert_eq!(name, "List'");
                assert_eq!(binders.len(), 1);
                assert_eq!(ctors.len(), 2);
            }
            other => panic!("expected Inductive, got {other:?}"),
        }
    }

    #[test]
    fn doc_comment_and_attributes_are_attached() {
        let d = parse("/-- doc -/\n@[simp]\ndef foo := 1");
        assert_eq!(d.doc, Some("doc".to_string()));
        assert_eq!(d.attrs, vec!["simp".to_string()]);
    }

    #[test]
    fn modifiers_are_recorded() {
        let d = parse("partial def loop (n : Nat) : Nat := loop n");
        assert!(d.modifiers.is_partial);
    }
}
