//! Term parsing: the Pratt/precedence-climbing infix loop
//! (`LeanParser::term`), its leading-construct dispatch (`term_lead`:
//! `fun`/`∀`/`∃`/`let`/`have`/`match`/`by`/`if`, prefix operators, and
//! the application chain), atoms, and binder-group parsing (shared with
//! `decls.rs`'s declaration parameter lists).

use nom::branch::alt;
use nom::combinator::{map, opt};
use nom::multi::{many0, separated_list0, separated_list1};
use nom::sequence::{delimited, pair};

use crate::ast::term::{Binder, BinderInfo, SortKind, Term, TermKind};
use crate::error::LeanError;
use crate::lexer::token::{Keyword, Sym, TokenKind};
use crate::parser::commons::{col_gt, spanned};
use crate::parser::precedence::{infix_of, prefix_of};
use crate::parser::{Ctx, LeanParser};
use crate::span::Span;
use crate::tokens::{
    any_tok, char_lit, dot_ident, ident, kw, meta_ident, nat_lit, peek_tok,
    str_lit, sym, PResult, Tokens,
};

impl<'a> LeanParser<'a> {
    /// The Pratt loop: parses a leading term (`term_lead`) then repeatedly
    /// extends it with infix operators whose left binding power is at
    /// least `min_bp`, recursing into the right-hand side at that
    /// operator's right binding power. See `parser::precedence` for the
    /// table.
    pub fn term(
        &self,
        ctx: Ctx,
        min_bp: u16,
        input: Tokens<'a>,
    ) -> PResult<'a, Term> {
        let (mut i, mut lhs) = self.term_lead(ctx, input)?;
        loop {
            let t = peek_tok(i).expect("Tokens should never be empty");
            // Layout: an operator token below the enclosing anchor, on a
            // new line, does not continue this term -- it belongs to
            // whatever comes after (a new declaration, a dedented `by`
            // tactic, ...).
            if t.newline_before && t.col <= ctx.min_col {
                break;
            }
            let Some(op) = infix_of(&t.kind) else { break };
            let (lbp, rbp) = op.binding_power();
            if lbp < min_bp {
                break;
            }
            let (i2, _) = any_tok(i)?; // consume the operator token
            let (i3, rhs) = self.term(ctx, rbp, i2)?;
            let span = Span::merge(lhs.span, rhs.span);
            lhs = if op.is_arrow {
                Term::new(
                    TermKind::Arrow {
                        domain: Box::new(lhs),
                        codomain: Box::new(rhs),
                    },
                    span,
                )
            } else {
                Term::new(
                    TermKind::BinOp {
                        op: op.name.to_string(),
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                    span,
                )
            };
            i = i3;
        }
        Ok((i, lhs))
    }

    fn term_lead(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        let ctx = ctx
            .deeper(peek_tok(i).expect("Tokens should never be empty"))
            .map_err(nom::Err::Failure)?;
        alt((
            move |i| self.fun_term(ctx, i),
            move |i| self.forall_term(ctx, i),
            move |i| self.exists_term(ctx, i),
            move |i| self.let_term(ctx, i),
            move |i| self.match_term(ctx, i),
            move |i| self.by_term(ctx, i),
            move |i| self.ite_term(ctx, i),
            move |i| self.prefix_term(ctx, i),
            move |i| self.app_chain(ctx, i),
        ))(i)
    }

    // -- binders --------------------------------------------------------

    pub(crate) fn binder_name(&self, i: Tokens<'a>) -> PResult<'a, String> {
        alt((
            map(ident, |(n, _)| n),
            map(sym(Sym::Underscore), |_| "_".to_string()),
        ))(i)
    }

    /// One bracketed binder group: `(x y : T)`, `{x : T}`, `⦃x⦄`,
    /// `[Inst]`. Tries the named form (`names : type`) first, falling
    /// back to a type-only anonymous form -- which is what lets `[Foo
    /// Bar]`-style instance brackets (no name, just a type) parse
    /// without any typeclass-specific grammar.
    fn binder_group(
        &self,
        info: BinderInfo,
        open: Sym,
        close: Sym,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, Binder> {
        let (i, ((names, ty), span)) = spanned(|i| {
            let (i, _) = sym(open)(i)?;
            let (i, (names, ty)) = alt((
                |i| {
                    let (i, names) =
                        nom::multi::many1(move |i| self.binder_name(i))(i)?;
                    let (i, _) = sym(Sym::Colon)(i)?;
                    let (i, ty) = self.term(ctx, 0, i)?;
                    Ok((i, (names, Some(ty))))
                },
                |i| {
                    let (i, ty) = self.term(ctx, 0, i)?;
                    Ok((i, (vec![], Some(ty))))
                },
            ))(i)?;
            let (i, _) = sym(close)(i)?;
            Ok((i, (names, ty)))
        })(i)?;
        Ok((
            i,
            Binder {
                names,
                ty: ty.map(Box::new),
                info,
                span,
            },
        ))
    }

    fn bare_binder(&self, i: Tokens<'a>) -> PResult<'a, Binder> {
        map(spanned(move |i| self.binder_name(i)), |(name, span)| {
            Binder {
                names: vec![name],
                ty: None,
                info: BinderInfo::Explicit,
                span,
            }
        })(i)
    }

    fn binder_atom(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Binder> {
        alt((
            |i| {
                self.binder_group(
                    BinderInfo::Explicit,
                    Sym::LParen,
                    Sym::RParen,
                    ctx,
                    i,
                )
            },
            |i| {
                self.binder_group(
                    BinderInfo::Implicit,
                    Sym::LBrace,
                    Sym::RBrace,
                    ctx,
                    i,
                )
            },
            |i| {
                self.binder_group(
                    BinderInfo::StrictImplicit,
                    Sym::LStrictImp,
                    Sym::RStrictImp,
                    ctx,
                    i,
                )
            },
            |i| {
                self.binder_group(
                    BinderInfo::InstImplicit,
                    Sym::LBracket,
                    Sym::RBracket,
                    ctx,
                    i,
                )
            },
            move |i| self.bare_binder(i),
        ))(i)
    }

    /// Zero or more binder groups, in source order, each respecting the
    /// enclosing indentation (`col_gt(ctx.min_col)`). Used for
    /// `def`/`theorem`/`axiom`/`inductive` parameter lists in
    /// `decls.rs`, where an empty list is legal.
    pub fn binder_list(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, Vec<Binder>> {
        many0(nom::sequence::preceded(col_gt(ctx.min_col), |i| {
            self.binder_atom(ctx, i)
        }))(i)
    }

    /// Like `binder_list`, but requires at least one binder -- used by
    /// `fun`/`∀`/`∃`, which are meaningless without a bound variable.
    fn binder_list1(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, Vec<Binder>> {
        let (i, first) = nom::sequence::preceded(col_gt(ctx.min_col), |i| {
            self.binder_atom(ctx, i)
        })(i)?;
        let (i, mut rest) = self.binder_list(ctx, i)?;
        rest.insert(0, first);
        Ok((i, rest))
    }

    /// The binder list accepted by `fun`/`∀`/`∃`: one or more binder
    /// items (bracketed groups or bare names, as `binder_list1`), with
    /// one extra rule bracketed groups don't need: a *trailing run* of
    /// otherwise-untyped bare names may share one type written after
    /// them (`∀ x y : T, P` -- both `x` and `y` get type `T`), which is
    /// idiomatic Lean and, unlike a bracketed group, can't be parsed as
    /// its own self-contained binder. Only the trailing run of bare,
    /// still-untyped, explicit binders is eligible; anything already
    /// typed (a bracketed group) stops the run.
    fn quantifier_binders(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, Vec<Binder>> {
        let (i, mut items) = self.binder_list1(ctx, i)?;
        let (i, shared_ty) =
            opt(nom::sequence::preceded(sym(Sym::Colon), |i| {
                self.term(ctx, 0, i)
            }))(i)?;
        if let Some(ty) = shared_ty {
            let mut split = items.len();
            for b in items.iter().rev() {
                if b.ty.is_none()
                    && b.info == BinderInfo::Explicit
                    && b.names.len() == 1
                {
                    split -= 1;
                } else {
                    break;
                }
            }
            let ty_span = ty.span;
            let start_span =
                items.get(split).map(|b| b.span).unwrap_or(ty_span);
            let names: Vec<String> = items[split..]
                .iter()
                .flat_map(|b| b.names.clone())
                .collect();
            let merged = Binder {
                names,
                ty: Some(Box::new(ty)),
                info: BinderInfo::Explicit,
                span: Span::merge(start_span, ty_span),
            };
            items.truncate(split);
            items.push(merged);
        }
        Ok((i, items))
    }

    // -- leading constructs -----------------------------------------

    fn fun_term(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        let (i, ((binders, body), span)) = spanned(|i| {
            let (i, _) = kw(Keyword::Fun)(i)?;
            let (i, binders) = self.quantifier_binders(ctx, i)?;
            let (i, _) = sym(Sym::MapsTo)(i)?;
            let (i, body) = self.term(ctx, 0, i)?;
            Ok((i, (binders, body)))
        })(i)?;
        Ok((
            i,
            Term::new(
                TermKind::Fun {
                    binders,
                    body: Box::new(body),
                },
                span,
            ),
        ))
    }

    fn forall_term(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        let (i, ((binders, body), span)) = spanned(|i| {
            let (i, _) = kw(Keyword::Forall)(i)?;
            let (i, binders) = self.quantifier_binders(ctx, i)?;
            let (i, _) = sym(Sym::Comma)(i)?;
            let (i, body) = self.term(ctx, 0, i)?;
            Ok((i, (binders, body)))
        })(i)?;
        Ok((
            i,
            Term::new(
                TermKind::Forall {
                    binders,
                    body: Box::new(body),
                },
                span,
            ),
        ))
    }

    fn exists_term(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        let (i, ((binders, body), span)) = spanned(|i| {
            let (i, _) = kw(Keyword::Exists)(i)?;
            let (i, binders) = self.quantifier_binders(ctx, i)?;
            let (i, _) = sym(Sym::Comma)(i)?;
            let (i, body) = self.term(ctx, 0, i)?;
            Ok((i, (binders, body)))
        })(i)?;
        Ok((
            i,
            Term::new(
                TermKind::Exists {
                    binders,
                    body: Box::new(body),
                },
                span,
            ),
        ))
    }

    /// `let x [: T] := v; body` / `have h [: T] := v; body`, or the
    /// same with the `;` replaced by a newline before `body`.
    fn let_term(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        // Re-anchor at the `let`/`have` keyword's own column, rather
        // than inheriting `ctx` unchanged: `ctx.min_col` here is
        // whatever the *enclosing* construct required (e.g. `0` for a
        // top-level `def`'s body), which can be far looser than this
        // `let`'s own indentation. Without this, a value/body that
        // merely happens to be indented past the enclosing anchor --
        // but not past the `let` itself -- would look like a valid
        // continuation to `app_chain`'s `col_gt(ctx.min_col)` check and
        // swallow the following declaration whole.
        let let_col = peek_tok(i).expect("Tokens should never be empty").col;
        let inner_ctx = ctx.anchored_at(let_col.max(ctx.min_col));
        let (i, ((is_have, name, ty, value, body), span)) = spanned(|i| {
            let (i, is_have) = alt((
                map(kw(Keyword::Let), |_| false),
                map(kw(Keyword::Have), |_| true),
            ))(i)?;
            let (i, (name, _)) = ident(i)?;
            let (i, ty) =
                opt(nom::sequence::preceded(sym(Sym::Colon), move |i| {
                    self.term(inner_ctx, 0, i)
                }))(i)?;
            let (i, _) = sym(Sym::ColonEq)(i)?;
            let (i, value) = self.term(inner_ctx, 0, i)?;
            let (i, semi) = opt(sym(Sym::Semi))(i)?;
            if semi.is_none() {
                let next = peek_tok(i).expect("Tokens should never be empty");
                if !next.newline_before {
                    return Err(nom::Err::Error(LeanError::expected(
                        "';' or a new line before the let-body",
                        format!("{:?}", next.kind),
                        next.start,
                        next.line,
                        next.col,
                    )));
                }
            }
            let (i, body) = self.term(inner_ctx, 0, i)?;
            Ok((i, (is_have, name, ty, value, body)))
        })(i)?;
        Ok((
            i,
            Term::new(
                TermKind::Let {
                    name,
                    ty: ty.map(Box::new),
                    value: Box::new(value),
                    body: Box::new(body),
                    is_have,
                },
                span,
            ),
        ))
    }

    fn match_term(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        let (i, ((scrutinees, alts), span)) = spanned(|i| {
            let (i, _) = kw(Keyword::Match)(i)?;
            let (i, scrutinees) = separated_list1(sym(Sym::Comma), move |i| {
                self.term(ctx, 0, i)
            })(i)?;
            let (i, _) = kw(Keyword::With)(i)?;
            let (i, alts) = self.match_alts(ctx, i)?;
            Ok((i, (scrutinees, alts)))
        })(i)?;
        Ok((i, Term::new(TermKind::Match { scrutinees, alts }, span)))
    }

    /// Parses the `| pat => rhs` alternatives of a `match`. The column
    /// of the *first* `|` becomes this match's `alt_col` anchor: later
    /// alternatives must sit at `col >= alt_col`, and (per
    /// `Ctx::alt_col`) a nested `match` inside an alternative's RHS is
    /// only accepted if its own first `|` is at a column strictly
    /// greater than this one -- otherwise the nested match would (like
    /// Lean itself) fail to find any alternatives of its own. This is
    /// the mechanism that lets
    /// ```text
    /// match n with
    /// | .z => z
    /// | .s nn =>
    ///   match m with        -- inner `|` at a deeper column: fine
    ///   | .z => n
    ///   | .s mm => f nn mm
    /// ```
    /// parse correctly while two `match`es whose alternatives share a
    /// column do not.
    fn match_alts(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, Vec<crate::ast::term::MatchAlt>> {
        let t = peek_tok(i).expect("Tokens should never be empty");
        if !matches!(t.kind, TokenKind::Sym(Sym::Bar)) {
            return Err(nom::Err::Error(LeanError::expected(
                "a match alternative (`|`)",
                format!("{:?}", t.kind),
                t.start,
                t.line,
                t.col,
            )));
        }
        let bar_col = t.col;
        if let Some(outer) = ctx.alt_col {
            if bar_col <= outer {
                return Err(nom::Err::Error(LeanError::expected(
                    "a nested match's alternatives to be indented past \
                     the enclosing match",
                    format!("column {bar_col}"),
                    t.start,
                    t.line,
                    t.col,
                )));
            }
        }
        let inner_ctx = ctx.with_alts(bar_col).anchored_at(bar_col);
        nom::multi::many1(nom::sequence::preceded(
            crate::parser::commons::col_ge(bar_col),
            move |i| self.match_alt_committed(inner_ctx, i),
        ))(i)
    }

    /// Like `match_alt`, but promotes any failure to `nom::Err::Failure`
    /// once a `|` is actually seen. This matters because `many1` (used
    /// by `match_alts` above) silently *stops* -- rather than
    /// propagating the error -- the moment its inner parser fails, which
    /// is the right behaviour when there simply is no further `|` (that
    /// correctly ends the alternative list), but the wrong behaviour
    /// when a `|` *is* present and something after it is malformed (a
    /// bad pattern, a missing `=>`, an invalid nested `match`): silently
    /// truncating there would leave the malformed alternative -- and
    /// everything after it -- as unparsed leftover input, with the
    /// enclosing `match` reporting success on a truncated alternative
    /// list instead of surfacing the real error.
    fn match_alt_committed(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, crate::ast::term::MatchAlt> {
        let t = peek_tok(i).expect("Tokens should never be empty");
        if !matches!(t.kind, TokenKind::Sym(Sym::Bar)) {
            // No `|` here at all: a normal, silent end of the
            // alternative list -- let `many1` stop as usual.
            return Err(nom::Err::Error(LeanError::expected(
                "a match alternative (`|`)",
                format!("{:?}", t.kind),
                t.start,
                t.line,
                t.col,
            )));
        }
        match self.match_alt(ctx, i) {
            Err(nom::Err::Error(e)) => Err(nom::Err::Failure(e)),
            other => other,
        }
    }

    fn match_alt(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, crate::ast::term::MatchAlt> {
        let (i, ((patterns, rhs), span)) = spanned(|i| {
            let (i, _) = sym(Sym::Bar)(i)?;
            let (i, patterns) =
                separated_list1(sym(Sym::Comma), |i| self.pattern(ctx, i))(i)?;
            let (i, _) = sym(Sym::MapsTo)(i)?;
            let (i, rhs) = self.term(ctx, 0, i)?;
            Ok((i, (patterns, rhs)))
        })(i)?;
        Ok((
            i,
            crate::ast::term::MatchAlt {
                patterns,
                rhs,
                span,
            },
        ))
    }

    fn by_term(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        let (i, (_by_tok, by_span)) = spanned(kw(Keyword::By))(i)?;
        let (i, tactics) = self.by_block(ctx, by_span, i)?;
        let span = if let Some(last) = tactics.last() {
            Span::merge(by_span, last.span)
        } else {
            by_span
        };
        Ok((i, Term::new(TermKind::By { tactics }, span)))
    }

    fn ite_term(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        let (i, ((cond, then_b, else_b), span)) = spanned(|i| {
            let (i, _) = kw(Keyword::If)(i)?;
            let (i, cond) = self.term(ctx, 0, i)?;
            let (i, _) = kw(Keyword::Then)(i)?;
            let (i, then_b) = self.term(ctx, 0, i)?;
            let (i, _) = kw(Keyword::Else)(i)?;
            let (i, else_b) = self.term(ctx, 0, i)?;
            Ok((i, (cond, then_b, else_b)))
        })(i)?;
        Ok((
            i,
            Term::new(
                TermKind::Ite {
                    cond: Box::new(cond),
                    then_branch: Box::new(then_b),
                    else_branch: Box::new(else_b),
                },
                span,
            ),
        ))
    }

    fn prefix_term(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        let t = peek_tok(i).expect("Tokens should never be empty");
        let Some(pfx) = prefix_of(&t.kind) else {
            return Err(nom::Err::Error(LeanError::expected(
                "a prefix operator",
                format!("{:?}", t.kind),
                t.start,
                t.line,
                t.col,
            )));
        };
        let (i, (operand, span)) = spanned(|i| {
            let (i, _) = any_tok(i)?;
            self.term(ctx, pfx.rbp, i)
        })(i)?;
        Ok((
            i,
            Term::new(
                TermKind::UnOp {
                    op: pfx.name.to_string(),
                    operand: Box::new(operand),
                },
                span,
            ),
        ))
    }

    /// One atom, then a run of further atoms at `col > ctx.min_col`
    /// consumed as application arguments (`f a b`). A single atom with
    /// no arguments is returned bare, not wrapped in `App`.
    fn app_chain(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        let (mut rest, func) = self.atom(ctx, i)?;
        let mut args = Vec::new();
        loop {
            match nom::sequence::preceded(col_gt(ctx.min_col), |i| {
                self.atom(ctx, i)
            })(rest)
            {
                Ok((r2, arg)) => {
                    args.push(arg);
                    rest = r2;
                }
                Err(_) => break,
            }
        }
        if args.is_empty() {
            return Ok((rest, func));
        }
        let span = Span::merge(func.span, args.last().unwrap().span);
        Ok((
            rest,
            Term::new(
                TermKind::App {
                    func: Box::new(func),
                    args,
                },
                span,
            ),
        ))
    }

    // -- atoms ----------------------------------------------------------

    fn atom(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        alt((
            move |i| self.sort_atom(i),
            move |i| self.lit_atom(i),
            move |i| self.hole_atom(i),
            move |i| self.var_atom(i),
            move |i| self.anonymous_atom(ctx, i),
            move |i| self.paren_atom(ctx, i),
        ))(i)
    }

    fn sort_atom(&self, i: Tokens<'a>) -> PResult<'a, Term> {
        alt((
            map(spanned(kw(Keyword::Type)), |(_, span)| {
                Term::new(
                    TermKind::Sort {
                        sort: SortKind::Type,
                        level: None,
                    },
                    span,
                )
            }),
            map(spanned(kw(Keyword::Prop)), |(_, span)| {
                Term::new(
                    TermKind::Sort {
                        sort: SortKind::Prop,
                        level: None,
                    },
                    span,
                )
            }),
            map(
                spanned(pair(
                    kw(Keyword::Sort),
                    opt(alt((
                        map(ident, |(n, _)| n),
                        map(nat_lit, |(_, raw, _)| raw),
                    ))),
                )),
                |((_, level), span)| {
                    Term::new(
                        TermKind::Sort {
                            sort: SortKind::Sort,
                            level,
                        },
                        span,
                    )
                },
            ),
        ))(i)
    }

    fn lit_atom(&self, i: Tokens<'a>) -> PResult<'a, Term> {
        alt((
            map(nat_lit, |(value, raw, span)| {
                Term::new(TermKind::Nat { value, raw }, span)
            }),
            map(str_lit, |(value, span)| {
                Term::new(TermKind::Str { value }, span)
            }),
            map(char_lit, |(value, span)| {
                Term::new(TermKind::Char { value }, span)
            }),
        ))(i)
    }

    fn hole_atom(&self, i: Tokens<'a>) -> PResult<'a, Term> {
        alt((
            map(spanned(sym(Sym::Underscore)), |(_, span)| {
                Term::new(TermKind::Hole, span)
            }),
            map(meta_ident, |(name, span)| {
                let name = if name == "_" { None } else { Some(name) };
                Term::new(TermKind::SyntheticHole { name }, span)
            }),
        ))(i)
    }

    fn var_atom(&self, i: Tokens<'a>) -> PResult<'a, Term> {
        alt((
            map(ident, |(name, span)| {
                Term::new(TermKind::Var { name }, span)
            }),
            map(dot_ident, |(name, span)| {
                Term::new(TermKind::DotIdent { name }, span)
            }),
        ))(i)
    }

    fn anonymous_atom(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        map(
            spanned(delimited(
                sym(Sym::LAngle),
                separated_list0(sym(Sym::Comma), move |i| self.term(ctx, 0, i)),
                sym(Sym::RAngle),
            )),
            |(elems, span)| Term::new(TermKind::Anonymous { elems }, span),
        )(i)
    }

    /// `(x : T) → B` (a dependent-binder group followed by `→`) is
    /// disambiguated from a plain parenthesized term/tuple by trying
    /// the binder-group reading first; nom's `alt` backtracks to the
    /// original input on failure, so a plain `(a + b)` or `(a, b)` falls
    /// through to `paren_or_tuple_atom` untouched.
    fn paren_atom(&self, ctx: Ctx, i: Tokens<'a>) -> PResult<'a, Term> {
        alt((
            move |i| self.dependent_arrow_atom(ctx, i),
            move |i| self.paren_or_tuple_atom(ctx, i),
        ))(i)
    }

    fn dependent_arrow_atom(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, Term> {
        let (i, ((binder, body), span)) = spanned(|i| {
            let (i, binder) = self.binder_group(
                BinderInfo::Explicit,
                Sym::LParen,
                Sym::RParen,
                ctx,
                i,
            )?;
            let (i, _) = sym(Sym::Arrow)(i)?;
            let (i, body) = self.term(ctx, 0, i)?;
            Ok((i, (binder, body)))
        })(i)?;
        Ok((
            i,
            Term::new(
                TermKind::Forall {
                    binders: vec![binder],
                    body: Box::new(body),
                },
                span,
            ),
        ))
    }

    fn paren_or_tuple_atom(
        &self,
        ctx: Ctx,
        i: Tokens<'a>,
    ) -> PResult<'a, Term> {
        map(
            spanned(delimited(
                sym(Sym::LParen),
                separated_list1(sym(Sym::Comma), move |i| self.term(ctx, 0, i)),
                sym(Sym::RParen),
            )),
            |(mut elems, span)| {
                if elems.len() == 1 {
                    let mut t = elems.remove(0);
                    t.span = span; // widen to include the parens themselves
                    t
                } else {
                    Term::new(TermKind::Tuple { elems }, span)
                }
            },
        )(i)
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::lexer::lex;

    fn parse(src: &str) -> Term {
        let toks = lex(src).unwrap();
        let p = LeanParser::new(src);
        let (rest, t) = p.term(Ctx::top(), 0, Tokens::new(&toks)).unwrap();
        assert!(
            crate::tokens::at_eof(rest),
            "leftover input after parsing {src:?}: {:?}",
            rest.toks
        );
        t
    }

    #[test]
    fn addition_and_multiplication_respect_precedence() {
        // a + b * c  ==  a + (b * c)
        let t = parse("a + b * c");
        match t.kind {
            TermKind::BinOp { op, rhs, .. } => {
                assert_eq!(op, "+");
                assert!(matches!(rhs.kind, TermKind::BinOp { .. }));
            }
            other => panic!("expected BinOp, got {other:?}"),
        }
    }

    #[test]
    fn arrow_is_right_associative() {
        // a -> b -> c  ==  a -> (b -> c)
        let t = parse("a -> b -> c");
        match t.kind {
            TermKind::Arrow { codomain, .. } => {
                assert!(matches!(codomain.kind, TermKind::Arrow { .. }));
            }
            other => panic!("expected Arrow, got {other:?}"),
        }
    }

    #[test]
    fn subtraction_is_left_associative() {
        // a - b - c  ==  (a - b) - c
        let t = parse("a - b - c");
        match t.kind {
            TermKind::BinOp { op, lhs, .. } => {
                assert_eq!(op, "-");
                assert!(matches!(lhs.kind, TermKind::BinOp { .. }));
            }
            other => panic!("expected BinOp, got {other:?}"),
        }
    }

    #[test]
    fn application_flattens_multiple_arguments() {
        let t = parse("f a b");
        match t.kind {
            TermKind::App { args, .. } => assert_eq!(args.len(), 2),
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn application_binds_tighter_than_operators() {
        // f a + b  ==  (f a) + b
        let t = parse("f a + b");
        match t.kind {
            TermKind::BinOp { lhs, .. } => {
                assert!(matches!(lhs.kind, TermKind::App { .. }));
            }
            other => panic!("expected BinOp, got {other:?}"),
        }
    }

    #[test]
    fn parenthesized_application_argument() {
        let t = parse("f (g a) b");
        match t.kind {
            TermKind::App { args, .. } => {
                assert_eq!(args.len(), 2);
                assert!(matches!(args[0].kind, TermKind::App { .. }));
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn fun_with_two_bare_binders() {
        let t = parse("fun x y => x");
        match t.kind {
            TermKind::Fun { binders, .. } => assert_eq!(binders.len(), 2),
            other => panic!("expected Fun, got {other:?}"),
        }
    }

    #[test]
    fn forall_body_extends_as_far_as_possible() {
        // ∀ x : T, P ∧ Q  ==  ∀ x, (P ∧ Q)
        let t = parse("forall x : T, P /\\ Q");
        match t.kind {
            TermKind::Forall { body, .. } => {
                assert!(matches!(body.kind, TermKind::BinOp { .. }));
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn dependent_arrow_binder_group() {
        let t = parse("(x : T) -> B");
        match t.kind {
            TermKind::Forall { binders, .. } => {
                assert_eq!(binders[0].names, vec!["x".to_string()]);
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn plain_parenthesized_term_is_not_a_binder_group() {
        let t = parse("(a + b)");
        assert!(matches!(t.kind, TermKind::BinOp { .. }));
    }

    #[test]
    fn parenthesized_comma_list_is_a_tuple() {
        let t = parse("(a, b, c)");
        match t.kind {
            TermKind::Tuple { elems } => assert_eq!(elems.len(), 3),
            other => panic!("expected Tuple, got {other:?}"),
        }
    }

    #[test]
    fn holes_and_dot_idents() {
        assert!(matches!(parse("_").kind, TermKind::Hole));
        assert!(matches!(
            parse("?m").kind,
            TermKind::SyntheticHole { name: Some(ref n) } if n == "m"
        ));
        assert!(matches!(
            parse(".succ").kind,
            TermKind::DotIdent { ref name } if name == "succ"
        ));
    }

    #[test]
    fn literals() {
        assert!(matches!(parse("42").kind, TermKind::Nat { value: 42, .. }));
        assert!(
            matches!(parse("\"hi\"").kind, TermKind::Str { ref value } if value == "hi")
        );
    }
}
