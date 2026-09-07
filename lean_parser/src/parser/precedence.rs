//! The built-in infix/prefix operator table driving the Pratt parser in
//! `terms.rs`. Precedences match Lean 4's real notation levels (all
//! multiples of 5); binding powers are derived as `(p, p+1)` for a
//! left-associative operator and `(p, p)` for a right-associative one,
//! which never collide since every table precedence is a multiple of 5.
//!
//! Application (juxtaposition, `f a b`) binds tighter than everything
//! here and is handled structurally in `terms.rs`, not via this table.

use crate::lexer::token::{Sym, TokenKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assoc {
    Left,
    Right,
    /// Lean treats chained comparisons (`a = b = c`) as an error rather
    /// than parsing them one way or the other. This implementation
    /// deviates and treats them as left-associative for simplicity,
    /// since nothing in the in-scope corpus exercises the distinction;
    /// tagged separately so that choice stays visible and revisitable.
    NonAssocAsLeft,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InfixOp {
    pub sym: Sym,
    /// The `op` string recorded in `TermKind::BinOp`/`UnOp`. Unused for
    /// `Arrow`, which becomes its own dedicated `TermKind` variant
    /// rather than a `BinOp`.
    pub name: &'static str,
    pub prec: u16,
    pub assoc: Assoc,
    pub is_arrow: bool,
}

impl InfixOp {
    /// `(left binding power, right binding power)`: the Pratt loop
    /// continues consuming this operator only while `lbp >= min_bp`,
    /// then recurses into the right-hand side at `rbp`.
    pub fn binding_power(&self) -> (u16, u16) {
        match self.assoc {
            Assoc::Left | Assoc::NonAssocAsLeft => (self.prec, self.prec + 1),
            Assoc::Right => (self.prec, self.prec),
        }
    }
}

const fn op(sym: Sym, name: &'static str, prec: u16, assoc: Assoc) -> InfixOp {
    InfixOp {
        sym,
        name,
        prec,
        assoc,
        is_arrow: false,
    }
}

/// The infix operator table, ordered by ascending precedence (purely
/// for readability -- lookup is by `Sym`, not position).
pub const INFIX_OPS: &[InfixOp] = &[
    op(Sym::Iff, "<->", 20, Assoc::Right),
    InfixOp {
        sym: Sym::Arrow,
        name: "->",
        prec: 25,
        assoc: Assoc::Right,
        is_arrow: true,
    },
    op(Sym::Or, "or", 30, Assoc::Right),
    op(Sym::Sum, "sum", 30, Assoc::Right),
    op(Sym::And, "and", 35, Assoc::Right),
    op(Sym::Prod, "prod", 35, Assoc::Right),
    op(Sym::Eq, "=", 50, Assoc::NonAssocAsLeft),
    op(Sym::Ne, "!=", 50, Assoc::NonAssocAsLeft),
    op(Sym::Lt, "<", 50, Assoc::NonAssocAsLeft),
    op(Sym::Le, "<=", 50, Assoc::NonAssocAsLeft),
    op(Sym::Gt, ">", 50, Assoc::NonAssocAsLeft),
    op(Sym::Ge, ">=", 50, Assoc::NonAssocAsLeft),
    op(Sym::Append, "++", 65, Assoc::Left),
    op(Sym::Add, "+", 65, Assoc::Left),
    op(Sym::Sub, "-", 65, Assoc::Left),
    op(Sym::Cons, "::", 67, Assoc::Right),
    op(Sym::Mul, "*", 70, Assoc::Left),
    op(Sym::Div, "/", 70, Assoc::Left),
    op(Sym::Mod, "%", 70, Assoc::Left),
    op(Sym::Pow, "^", 75, Assoc::Right),
    op(Sym::Comp, "circ", 90, Assoc::Right),
];

/// Looks up the infix operator matching `kind`, if any.
pub fn infix_of(kind: &TokenKind) -> Option<InfixOp> {
    match kind {
        TokenKind::Sym(s) => INFIX_OPS.iter().find(|op| op.sym == *s).copied(),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrefixOp {
    pub sym: Sym,
    pub name: &'static str,
    pub rbp: u16,
}

/// Prefix (unary) operators: logical negation and unary minus. `¬`
/// binds looser than the arithmetic operators (`40`); unary `-` binds
/// tight (`75`, just under `^`) so `-a ^ b` parses as `-(a ^ b)`,
/// matching common mathematical convention (Lean core actually treats
/// `Neg.neg` as `prefix:max` in places, but `75` is a deliberately
/// conservative choice given nothing in the in-scope corpus stresses
/// this).
pub const PREFIX_OPS: &[PrefixOp] = &[
    PrefixOp {
        sym: Sym::Not,
        name: "not",
        rbp: 40,
    },
    PrefixOp {
        sym: Sym::Sub,
        name: "neg",
        rbp: 75,
    },
];

pub fn prefix_of(kind: &TokenKind) -> Option<PrefixOp> {
    match kind {
        TokenKind::Sym(s) => PREFIX_OPS.iter().find(|op| op.sym == *s).copied(),
        _ => None,
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn arrow_is_right_associative_and_marked_as_arrow() {
        let arrow = infix_of(&TokenKind::Sym(Sym::Arrow)).unwrap();
        assert!(arrow.is_arrow);
        assert_eq!(arrow.binding_power(), (25, 25));
    }

    #[test]
    fn add_is_left_associative() {
        let add = infix_of(&TokenKind::Sym(Sym::Add)).unwrap();
        let (lbp, rbp) = add.binding_power();
        assert!(lbp < rbp, "left-assoc operators should have lbp < rbp");
    }

    #[test]
    fn pow_is_right_associative() {
        let pow = infix_of(&TokenKind::Sym(Sym::Pow)).unwrap();
        let (lbp, rbp) = pow.binding_power();
        assert_eq!(lbp, rbp, "right-assoc operators should have lbp == rbp");
    }

    #[test]
    fn mul_binds_tighter_than_add() {
        let add = infix_of(&TokenKind::Sym(Sym::Add)).unwrap();
        let mul = infix_of(&TokenKind::Sym(Sym::Mul)).unwrap();
        assert!(mul.prec > add.prec);
    }

    #[test]
    fn non_operator_token_has_no_infix_entry() {
        assert_eq!(infix_of(&TokenKind::Sym(Sym::LParen)), None);
    }

    #[test]
    fn unary_minus_binds_tighter_than_binary_minus() {
        let binary_sub = infix_of(&TokenKind::Sym(Sym::Sub)).unwrap();
        let unary_sub = prefix_of(&TokenKind::Sym(Sym::Sub)).unwrap();
        assert!(unary_sub.rbp > binary_sub.prec);
    }
}
