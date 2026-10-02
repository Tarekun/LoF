use super::{
    header::{parse_header, Form, Order, TptpHeader},
    prp::prp_formula,
    syntax::{name, role, skip_annotations, sym, ws0, Role},
};
use crate::{
    error::LofError, file_manager::read_file, parser::api::PResult,
    type_theory::grammars::prop::PropFormula,
};
use nom::{
    combinator::{all_consuming, opt},
    multi::many0,
    sequence::{preceded, terminated},
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
}

#[derive(Debug, Clone, PartialEq)]
/// A TPTP problem: its header and its annotated formulas
pub struct TptpProblem {
    pub header: TptpHeader,
    pub body: TptpBody,
}

/// `fof(name, role, formula[, annotations]).` in a propositional problem
fn prp_input(input: &str) -> PResult<'_, TptpInput<PropFormula>> {
    let (input, _) = sym("fof")(input)?;
    let (input, _) = sym("(")(input)?;
    let (input, name) = name(input)?;
    let (input, _) = sym(",")(input)?;
    let (input, role) = role(input)?;
    let (input, _) = sym(",")(input)?;
    let (input, formula) = prp_formula(input)?;
    let (input, _) = opt(preceded(sym(","), skip_annotations))(input)?;
    let (input, _) = sym(")")(input)?;
    let (input, _) = sym(".")(input)?;

    Ok((
        input,
        TptpInput {
            name,
            role,
            formula,
        },
    ))
}

/// Parses the TPTP problem `source`: its header decides the logic, and with
/// it the grammar its formulas are parsed into
pub fn parse_tptp(source: &str) -> Result<TptpProblem, LofError> {
    let header = parse_header(source)?;
    let body =
        match (header.form, header.order) {
            (Form::Fof, Some(Order::Propositional)) => {
                let (_, inputs) =
                    all_consuming(terminated(many0(prp_input), ws0))(source)?;

                TptpBody::Propositional(inputs)
            }

            _ => return Err(LofError::unsupported(
                "Only propositional TPTP problems (FOF_*_PRP) are supported",
            )),
        };

    Ok(TptpProblem { header, body })
}

/// Loads the TPTP problem file at `path`
pub fn load_tptp_file(path: &str) -> Result<TptpProblem, LofError> {
    parse_tptp(&read_file(path)?)
}
