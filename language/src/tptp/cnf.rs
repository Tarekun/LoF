use super::syntax::{atomic_formula, sym, TptpAtom, TptpTerm};
use crate::{
    parser::api::PResult,
    type_theory::grammars::cnf::{
        CnfFormula::{self, Atom, Clause, Equality, Not},
        CnfTerm::{self, Application, Variable},
    },
};
use nom::{
    branch::alt,
    combinator::map,
    multi::separated_list1,
    sequence::{delimited, preceded},
};

/// Lowers a TPTP term to CNF: in clauses every variable is implicitly
/// universally quantified, while constants become nullary applications
pub fn term_to_cnf(term: &TptpTerm) -> CnfTerm {
    match term {
        TptpTerm::Var(name) => Variable(name.to_string()),
        TptpTerm::Fun(name, args) => Application(
            name.to_string(),
            args.iter().map(term_to_cnf).collect(),
        ),
    }
}

fn atom_to_cnf(atom: &TptpAtom) -> CnfFormula {
    match atom {
        TptpAtom::Pred(name, args) => {
            Atom(name.to_string(), args.iter().map(term_to_cnf).collect())
        }
        TptpAtom::Eq(left, right, is_positive) => {
            let equality = Equality(term_to_cnf(left), term_to_cnf(right));
            if *is_positive {
                equality
            } else {
                Not(Box::new(equality))
            }
        }
    }
}

/// Packs `literals` following the SUP convention: the empty clause is
/// `Clause([])`, unit clauses are bare literals, anything else is a `Clause`
pub fn make_clause(mut literals: Vec<CnfFormula>) -> CnfFormula {
    if literals.len() == 1 {
        literals.pop().unwrap()
    } else {
        Clause(literals)
    }
}

fn literal(input: &str) -> PResult<'_, CnfFormula> {
    alt((
        map(preceded(sym("~"), atomic_formula), |atom| {
            Not(Box::new(atom_to_cnf(&atom)))
        }),
        map(atomic_formula, |atom| atom_to_cnf(&atom)),
    ))(input)
}

fn disjunction(input: &str) -> PResult<'_, CnfFormula> {
    map(separated_list1(sym("|"), literal), make_clause)(input)
}

/// Parses the formula of a `cnf(...)` annotated formula: a disjunction of
/// literals, optionally wrapped in parentheses
pub fn cnf_formula(input: &str) -> PResult<'_, CnfFormula> {
    alt((delimited(sym("("), disjunction, sym(")")), disjunction))(input)
}
