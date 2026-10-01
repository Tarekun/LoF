use super::{
    cnf::cnf_formula,
    header::{parse_header, Form, Order, TptpHeader},
    prp::prp_formula,
    syntax::{name, role, skip_annotations, sym, ws0, Role},
};
use crate::{
    error::LofError,
    file_manager::read_file,
    parser::api::PResult,
    type_theory::grammars::{cnf::CnfFormula, prop::PropFormula},
};
use nom::{
    combinator::{all_consuming, map, opt},
    multi::many0,
    sequence::{preceded, terminated, tuple},
};

#[derive(Debug, Clone, PartialEq)]
/// An annotated formula `<keyword>(name, role, formula[, annotations]).`,
/// with the formula in the grammar `F` of the problem's logic
pub struct TptpInput<F> {
    pub name: String,
    pub role: Role,
    pub formula: F,
}

#[derive(Debug, Clone, PartialEq)]
/// The annotated formulas of a problem, in the grammar of the logic declared
/// by the problem's header
pub enum TptpBody {
    /// Propositional problems (SPC `FOF_*_PRP`), written with `fof`
    Propositional(Vec<TptpInput<PropFormula>>),
    /// First order clauses (SPC `CNF_*_EPR`, `CNF_*_RFO`), written with `cnf`
    Clausal(Vec<TptpInput<CnfFormula>>),
}

#[derive(Debug, Clone, PartialEq)]
/// A TPTP problem: its header and its annotated formulas
pub struct TptpProblem {
    pub header: TptpHeader,
    pub body: TptpBody,
}

/// Parses every annotated formula `<keyword>(name, role, formula[,
/// annotations]).` of `source`, parsing their formulas with `formula`
fn inputs<'a, F>(
    source: &'a str,
    keyword: &'static str,
    formula: fn(&'a str) -> PResult<'a, F>,
) -> Result<Vec<TptpInput<F>>, LofError> {
    let input = map(
        tuple((
            sym(keyword),
            sym("("),
            name,
            sym(","),
            role,
            sym(","),
            formula,
            opt(preceded(sym(","), skip_annotations)),
            sym(")"),
            sym("."),
        )),
        |(_, _, name, _, role, _, formula, _, _, _)| TptpInput {
            name,
            role,
            formula,
        },
    );
    let (_, inputs) = all_consuming(terminated(many0(input), ws0))(source)?;
    Ok(inputs)
}

/// Parses the TPTP problem `source`: its header decides the logic, and with
/// it the grammar its formulas are parsed into
pub fn parse_tptp(source: &str) -> Result<TptpProblem, LofError> {
    let header = parse_header(source)?;
    let body = match (header.form, header.order) {
        (Form::Fof, Some(Order::Propositional)) => {
            TptpBody::Propositional(inputs(source, "fof", prp_formula)?)
        }
        (
            Form::Cnf,
            Some(Order::EffectivelyPropositional | Order::ReallyFirstOrder),
        ) => TptpBody::Clausal(inputs(source, "cnf", cnf_formula)?),
        _ => {
            return Err(LofError::unsupported(
                "Only propositional FOF (FOF_*_PRP) and first order CNF \
                 (CNF_*_EPR, CNF_*_RFO) TPTP problems are supported",
            ))
        }
    };
    Ok(TptpProblem { header, body })
}

/// Loads the TPTP problem file at `path`
pub fn load_tptp_file(path: &str) -> Result<TptpProblem, LofError> {
    parse_tptp(&read_file(path)?)
}
