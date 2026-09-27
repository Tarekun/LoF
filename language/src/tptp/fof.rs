use super::syntax::{atomic_formula, sym, upper_word, TptpAtom, TptpTerm};
use crate::{
    error::LofError,
    parser::api::PResult,
    type_theory::grammars::fol::{
        FolFormula::{
            self, Arrow, Conjunction, Disjunction, Exist, ForAll, Not,
            Predicate,
        },
        FolTerm::{self, Variable},
    },
};
use nom::{
    branch::alt,
    character::complete::char,
    combinator::{map, not},
    multi::{many0, separated_list1},
    sequence::{delimited, preceded, terminated},
};
use std::{cell::RefCell, collections::HashSet};

/// Name of the sort given to every quantified variable, as FOF is untyped
pub const INDIVIDUAL_SORT: &str = "$i";
/// Name of the predicate FOF equalities are lowered to
pub const EQUALITY_PREDICATE: &str = "=";

#[derive(Clone, Copy)]
enum BinaryConnective {
    Iff,
    NotIff,
    Implies,
    ImpliedBy,
    Nor,
    Nand,
}

fn binary_connective(input: &str) -> PResult<'_, BinaryConnective> {
    alt((
        map(sym("<=>"), |_| BinaryConnective::Iff),
        map(sym("<~>"), |_| BinaryConnective::NotIff),
        map(sym("=>"), |_| BinaryConnective::Implies),
        map(sym("<="), |_| BinaryConnective::ImpliedBy),
        map(sym("~|"), |_| BinaryConnective::Nor),
        map(sym("~&"), |_| BinaryConnective::Nand),
    ))(input)
}

fn combine(
    op: BinaryConnective,
    left: FolFormula,
    right: FolFormula,
) -> FolFormula {
    let iff = |l: FolFormula, r: FolFormula| {
        Conjunction(vec![
            Arrow(Box::new(l.clone()), Box::new(r.clone())),
            Arrow(Box::new(r), Box::new(l)),
        ])
    };
    match op {
        BinaryConnective::Iff => iff(left, right),
        BinaryConnective::NotIff => Not(Box::new(iff(left, right))),
        BinaryConnective::Implies => Arrow(Box::new(left), Box::new(right)),
        BinaryConnective::ImpliedBy => Arrow(Box::new(right), Box::new(left)),
        BinaryConnective::Nor => Not(Box::new(Disjunction(vec![left, right]))),
        BinaryConnective::Nand => Not(Box::new(Conjunction(vec![left, right]))),
    }
}

/// Stateful parser for a single FOF formula. Keeps track of:
/// * the bound variables in scope, as (source_name, rectified_name) pairs
/// * every binder name used so far, to rectify shadowing binders
/// * the constant/function symbols met, needed by `clausify` to tell them
///   apart from variables, as both are `FolTerm::Variable`s
struct FofParser {
    scope: RefCell<Vec<(String, String)>>,
    binders: RefCell<HashSet<String>>,
    constants: RefCell<HashSet<String>>,
}

impl FofParser {
    fn new() -> Self {
        FofParser {
            scope: RefCell::new(vec![]),
            binders: RefCell::new(HashSet::new()),
            constants: RefCell::new(HashSet::new()),
        }
    }

    /// Returns a binder name for `var_name` distinct from every binder already
    /// in the formula. `prenex_normal_form` doesn't rectify variables yet, so
    /// shadowing binders must be renamed apart here
    fn fresh_binder(&self, var_name: &str) -> String {
        let mut binders = self.binders.borrow_mut();
        let mut fresh = var_name.to_string();
        let mut idx = 0;
        while binders.contains(&fresh) {
            idx += 1;
            fresh = format!("{}_{}", var_name, idx);
        }
        binders.insert(fresh.clone());
        fresh
    }

    fn lower_term(&self, term: &TptpTerm) -> Result<FolTerm, LofError> {
        match term {
            TptpTerm::Var(name) => self
                .scope
                .borrow()
                .iter()
                .rev()
                .find(|(source, _)| source == name)
                .map(|(_, rectified)| Variable(rectified.to_string()))
                .ok_or_else(|| LofError::unbound_variable(name)),
            TptpTerm::Fun(name, args) => {
                self.constants.borrow_mut().insert(name.to_string());
                let args = args
                    .iter()
                    .map(|arg| self.lower_term(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(FolTerm::make_multiarg_app(name, &args))
            }
        }
    }

    fn lower_atom(&self, atom: &TptpAtom) -> Result<FolFormula, LofError> {
        match atom {
            TptpAtom::Pred(name, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.lower_term(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Predicate(name.to_string(), args))
            }
            TptpAtom::Eq(left, right, is_positive) => {
                // TODO FolFormula has no dedicated equality variant, so equality is
                // encoded as the `=` predicate (and mapped back to `CnfFormula::Equality`
                // by `clausify`). Reevaluate whether a `FolFormula::Equality` is worth it
                let equality = Predicate(
                    EQUALITY_PREDICATE.to_string(),
                    vec![self.lower_term(left)?, self.lower_term(right)?],
                );
                if *is_positive {
                    Ok(equality)
                } else {
                    Ok(Not(Box::new(equality)))
                }
            }
        }
    }

    /// `<fof_logic_formula>`: a unitary formula, optionally followed by either a
    /// non associative binary connective or a chain of `|` or `&`
    fn logic_formula<'a>(&self, input: &'a str) -> PResult<'a, FolFormula> {
        let (input, first) = self.unitary(input)?;

        if let Ok((input, op)) = binary_connective(input) {
            let (input, second) = self.unitary(input)?;
            return Ok((input, combine(op, first, second)));
        }

        let (input, disjuncts) =
            many0(preceded(sym("|"), |input| self.unitary(input)))(input)?;
        let (input, conjuncts) = if disjuncts.is_empty() {
            many0(preceded(sym("&"), |input| self.unitary(input)))(input)?
        } else {
            (input, vec![])
        };

        // TPTP connectives don't have relative precedence, mixing requires parentheses
        if alt((sym("|"), sym("&"), map(binary_connective, |_| "")))(input)
            .is_ok()
        {
            return Err(nom::Err::Failure(LofError::custom(
                "TPTP requires parentheses when mixing binary connectives",
            )));
        }

        let formula = if !disjuncts.is_empty() {
            Disjunction([vec![first], disjuncts].concat())
        } else if !conjuncts.is_empty() {
            Conjunction([vec![first], conjuncts].concat())
        } else {
            first
        };
        Ok((input, formula))
    }

    /// `<fof_unitary_formula>`: quantified, negated, parenthesized or atomic
    fn unitary<'a>(&self, input: &'a str) -> PResult<'a, FolFormula> {
        alt((
            |input| self.quantified(input),
            map(preceded(sym("~"), |input| self.unitary(input)), |φ| {
                Not(Box::new(φ))
            }),
            delimited(sym("("), |input| self.logic_formula(input), sym(")")),
            |input| self.atomic(input),
        ))(input)
    }

    fn atomic<'a>(&self, input: &'a str) -> PResult<'a, FolFormula> {
        let (input, atom) = atomic_formula(input)?;
        let formula = self.lower_atom(&atom).map_err(nom::Err::Failure)?;
        Ok((input, formula))
    }

    /// `! [X, Y] : φ` and `? [X, Y] : φ`, where `φ` is a unitary formula
    fn quantified<'a>(&self, input: &'a str) -> PResult<'a, FolFormula> {
        let (input, is_universal) = alt((
            // don't confuse `!` with `!=`
            map(terminated(sym("!"), not(char('='))), |_| true),
            map(sym("?"), |_| false),
        ))(input)?;
        let (input, vars) = delimited(
            sym("["),
            separated_list1(sym(","), upper_word),
            preceded(sym("]"), sym(":")),
        )(input)?;

        let bound: Vec<(String, String)> = vars
            .iter()
            .map(|var| (var.to_string(), self.fresh_binder(var)))
            .collect();
        let scope_len = self.scope.borrow().len();
        self.scope.borrow_mut().extend(bound.clone());
        let body = self.unitary(input);
        self.scope.borrow_mut().truncate(scope_len);
        let (input, body) = body?;

        let sort = Predicate(INDIVIDUAL_SORT.to_string(), vec![]);
        let formula = bound.into_iter().rev().fold(body, |body, (_, var)| {
            if is_universal {
                ForAll(var, Box::new(sort.clone()), Box::new(body))
            } else {
                Exist(var, Box::new(sort.clone()), Box::new(body))
            }
        });
        Ok((input, formula))
    }
}

/// Parses the formula of a `fof(...)` annotated formula. Returns the formula
/// together with the set of constant and function symbols occurring in it
pub fn fof_formula(input: &str) -> PResult<'_, (FolFormula, HashSet<String>)> {
    let parser = FofParser::new();
    let (input, formula) = parser.logic_formula(input)?;
    Ok((input, (formula, parser.constants.into_inner())))
}
