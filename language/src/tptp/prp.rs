use super::syntax::{atomic_word, sym};
use crate::{
    parser::api::PResult,
    type_theory::grammars::prop::PropFormula::{
        self, Arrow, Atom, Conjunction, Disjunction, Not,
    },
};
use nom::{
    branch::alt,
    combinator::map,
    multi::many1,
    sequence::{delimited, pair, preceded},
};

fn iff(left: PropFormula, right: PropFormula) -> PropFormula {
    Conjunction(vec![
        Arrow(Box::new(left.clone()), Box::new(right.clone())),
        Arrow(Box::new(right), Box::new(left)),
    ])
}

/// `<fof_logic_formula>`: a unitary formula, optionally followed by either a
/// non associative binary connective and another unitary formula, or a chain
/// of `|` or `&`. TPTP connectives have no relative precedence, so anything
/// else needs parentheses
pub fn prp_formula(input: &str) -> PResult<'_, PropFormula> {
    let (input, first) = unitary(input)?;

    let connective = alt((
        sym("<=>"),
        sym("<~>"),
        sym("=>"),
        sym("<="),
        sym("~|"),
        sym("~&"),
    ));
    if let Ok((input, (op, second))) = pair(connective, unitary)(input) {
        let formula = match op {
            "<=>" => iff(first, second),
            "<~>" => Not(Box::new(iff(first, second))),
            "=>" => Arrow(Box::new(first), Box::new(second)),
            "<=" => Arrow(Box::new(second), Box::new(first)),
            "~|" => Not(Box::new(Disjunction(vec![first, second]))),
            "~&" => Not(Box::new(Conjunction(vec![first, second]))),
            _ => unreachable!(),
        };
        return Ok((input, formula));
    }
    if let Ok((input, rest)) = many1(preceded(sym("|"), unitary))(input) {
        return Ok((input, Disjunction([vec![first], rest].concat())));
    }
    if let Ok((input, rest)) = many1(preceded(sym("&"), unitary))(input) {
        return Ok((input, Conjunction([vec![first], rest].concat())));
    }
    Ok((input, first))
}

/// `<fof_unitary_formula>`: negated, parenthesized or atomic. `$true` and
/// `$false` are ⊤ and ⊥, the empty conjunction and disjunction
fn unitary(input: &str) -> PResult<'_, PropFormula> {
    alt((
        map(preceded(sym("~"), unitary), |φ| Not(Box::new(φ))),
        delimited(sym("("), prp_formula, sym(")")),
        map(sym("$true"), |_| Conjunction(vec![])),
        map(sym("$false"), |_| Disjunction(vec![])),
        map(atomic_word, Atom),
    ))(input)
}
