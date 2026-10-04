use super::{
    cnf::cnf_formula,
    header::{parse_header, Form, Order, TptpHeader},
    prp::prp_formula,
    syntax::{name, role, single_quoted, skip_annotations, sym, ws0, Role},
    thf::{thf_input, ThfInput},
};
use crate::{
    error::LofError,
    file_manager::read_file,
    parser::api::PResult,
    type_theory::grammars::{cnf::CnfFormula, prop::PropFormula},
};
use nom::{
    branch::alt,
    combinator::{all_consuming, map, opt},
    multi::{many0, separated_list0},
    sequence::{delimited, preceded, terminated, tuple},
};
use std::{env, path::Path};

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
    /// Clausal problems (SPC `CNF_*`), written with `cnf`
    Clausal(Vec<TptpInput<CnfFormula>>),
    /// Higher order problems (SPC `TH0_*`, `TH1_*`), written with `thf`
    HigherOrder(Vec<TptpInput<ThfInput>>),
}

#[derive(Debug, Clone, PartialEq)]
/// A TPTP problem: its header and its annotated formulas
pub struct TptpProblem {
    pub header: TptpHeader,
    pub body: TptpBody,
}

/// Parses every annotated formula `<keyword>(name, role, formula[,
/// annotations]).` of `source`, parsing their formulas with `formula`.
/// Included files are found in `dir`, falling back to the `$TPTP` library
/// root, and their formulas are parsed with the same grammar
fn inputs<F>(
    source: &str,
    dir: &Path,
    keyword: &'static str,
    formula: fn(&str) -> PResult<'_, F>,
) -> Result<Vec<TptpInput<F>>, LofError> {
    enum Item<F> {
        Input(TptpInput<F>),
        /// `include('file'[, [names]]).`: the file and the names to select
        Include(String, Option<Vec<String>>),
    }

    // simple input
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
        |(_, _, name, _, role, _, formula, _, _, _)| {
            Item::Input(TptpInput {
                name,
                role,
                formula,
            })
        },
    );
    // include statements
    let include = map(
        tuple((
            sym("include"),
            sym("("),
            single_quoted,
            opt(preceded(
                sym(","),
                delimited(sym("["), separated_list0(sym(","), name), sym("]")),
            )),
            sym(")"),
            sym("."),
        )),
        |(_, _, file, selection, _, _)| Item::Include(file, selection),
    );
    let (_, items) =
        all_consuming(terminated(many0(alt((input, include))), ws0))(source)?;

    let mut parsed = vec![];
    for item in items {
        match item {
            Item::Input(input) => parsed.push(input),
            Item::Include(file, selection) => {
                let mut path = dir.join(&file);
                if let (false, Ok(root)) = (path.exists(), env::var("TPTP")) {
                    path = Path::new(&root).join(&file);
                }
                let source =
                    read_file(&path.display().to_string()).map_err(|err| {
                        LofError::custom(format!(
                            "Cannot read the included TPTP file '{}': {}",
                            file, err
                        ))
                    })?;
                let dir = path.parent().unwrap_or(dir);
                parsed.extend(
                    inputs(&source, dir, keyword, formula)?.into_iter().filter(
                        |input| {
                            selection.as_ref().map_or(true, |names| {
                                names.contains(&input.name)
                            })
                        },
                    ),
                );
            }
        }
    }
    Ok(parsed)
}

/// Parses the TPTP problem `source`, whose includes are found in `dir`: its
/// header decides the logic, and with it the grammar its formulas are parsed
/// into
fn parse(source: &str, dir: &Path) -> Result<TptpProblem, LofError> {
    let header = parse_header(source)?;
    let body = match (header.form, header.order) {
        (Form::Fof, Some(Order::Propositional)) => {
            TptpBody::Propositional(inputs(source, dir, "fof", prp_formula)?)
        }
        // TODO propositional CNF problems are parsed to first order clauses
        // over nullary atoms, rather than to `PropFormula`
        (Form::Cnf, Some(_)) => {
            TptpBody::Clausal(inputs(source, dir, "cnf", cnf_formula)?)
        }
        (Form::Th0 | Form::Th1, _) => {
            TptpBody::HigherOrder(inputs(source, dir, "thf", thf_input)?)
        }
        _ => return Err(LofError::unsupported(
            "Only propositional FOF (FOF_*_PRP), CNF and THF TPTP problems \
                 are supported",
        )),
    };
    Ok(TptpProblem { header, body })
}

/// Parses the TPTP problem `source`, resolving its includes from the working
/// directory
pub fn parse_tptp(source: &str) -> Result<TptpProblem, LofError> {
    parse(source, Path::new(""))
}

/// Loads the TPTP problem file at `path`, resolving its includes from the
/// file's directory
pub fn load_tptp_file(path: &str) -> Result<TptpProblem, LofError> {
    let dir = Path::new(path).parent().unwrap_or(Path::new(""));
    parse(&read_file(path)?, dir)
}
