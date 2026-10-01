use super::syntax::{atomic_word, sym, upper_word};
use crate::{
    parser::api::PResult,
    type_theory::grammars::cnf::{
        CnfFormula::{self, Atom, Clause, Equality, Not},
        CnfTerm::{self, Application, Variable},
    },
};
use nom::{
    branch::alt,
    combinator::{map, opt},
    multi::separated_list1,
    sequence::{delimited, pair, preceded, separated_pair},
};

fn arguments(input: &str) -> PResult<'_, Vec<CnfTerm>> {
    delimited(sym("("), separated_list1(sym(","), term), sym(")"))(input)
}

/// A variable, implicitly universally quantified, or a function application.
/// Constants are nullary applications
fn term(input: &str) -> PResult<'_, CnfTerm> {
    alt((
        map(upper_word, |var| Variable(var.to_string())),
        map(pair(atomic_word, opt(arguments)), |(fun, args)| {
            Application(fun, args.unwrap_or_default())
        }),
    ))(input)
}

/// `s = t`, `s != t` or a predicate application `p(args)` / `p`
fn atom(input: &str) -> PResult<'_, CnfFormula> {
    alt((
        map(separated_pair(term, sym("="), term), |(l, r)| {
            Equality(l, r)
        }),
        map(separated_pair(term, sym("!="), term), |(l, r)| {
            Not(Box::new(Equality(l, r)))
        }),
        map(pair(atomic_word, opt(arguments)), |(pred, args)| {
            Atom(pred, args.unwrap_or_default())
        }),
    ))(input)
}

fn literal(input: &str) -> PResult<'_, CnfFormula> {
    alt((map(preceded(sym("~"), atom), |φ| Not(Box::new(φ))), atom))(input)
}

/// A disjunction of literals. Unit clauses are bare literals, as SUP expects
fn disjunction(input: &str) -> PResult<'_, CnfFormula> {
    map(separated_list1(sym("|"), literal), |mut literals| {
        if literals.len() == 1 {
            literals.pop().unwrap()
        } else {
            Clause(literals)
        }
    })(input)
}

/// Parses the formula of a `cnf(...)` annotated formula: a disjunction of
/// literals, optionally wrapped in parentheses
pub fn cnf_formula(input: &str) -> PResult<'_, CnfFormula> {
    alt((delimited(sym("("), disjunction, sym(")")), disjunction))(input)
}
