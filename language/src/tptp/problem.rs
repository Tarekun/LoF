pub use super::syntax::Role;
use super::{
    cnf::{cnf_formula, make_clause},
    fof::{fof_formula, tff_formula, Symbols},
    syntax::{
        lower_word, name, role, single_quoted, skip_annotations, sym, ws0,
    },
    tff::{build_environment, type_declaration, TypeDeclaration},
    thf::{
        elaborate, hol_environment, is_formula_type, thf_formula,
        thf_type_declaration,
    },
};
use crate::{
    error::LofError,
    file_manager::read_file,
    parser::api::PResult,
    type_theory::{
        environment::Environment,
        f::f::{FStm, SystemF},
        fol::{fol::Fol, fol_utils::clausify},
        grammars::{
            cnf::{
                CnfFormula::{self, Atom, Clause, Equality, ForAll, Not},
                CnfTerm::{self, Application, Variable},
            },
            f::{FTerm, FType},
            fol::FolFormula::{self, Conjunction},
        },
        interface::Kernel,
    },
};
use nom::{
    combinator::opt,
    multi::separated_list0,
    sequence::{delimited, preceded},
};
use std::{
    collections::HashSet,
    env,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone, PartialEq)]
pub enum TptpFormula {
    /// `fof` or `tff` formula, non logical symbols occurring in it
    Fol(FolFormula, Symbols),
    Cnf(CnfFormula),
    /// `tff` type declaration
    Declaration(TypeDeclaration),
    /// `thf` formula, a System F term expected of type `$o`
    Thf(FTerm),
    /// `thf` type declaration: symbol_name, symbol_type
    ThfDeclaration(String, FType),
}

#[derive(Debug, Clone, PartialEq)]
/// An annotated formula `<dialect>(name, role, formula[, annotations]).`
pub struct TptpInput {
    pub name: String,
    pub role: Role,
    pub formula: TptpFormula,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TptpProblem {
    pub inputs: Vec<TptpInput>,
}

#[derive(Debug, Clone, PartialEq)]
enum TopLevel {
    Input(TptpInput),
    /// file_path, optional selection of formula names
    Include(String, Option<Vec<String>>),
}

//############################# PARSING

fn annotated_formula(input: &str) -> PResult<'_, TopLevel> {
    let (input, dialect) = lower_word(input)?;
    let (input, _) = sym("(")(input)?;

    let (input, top_level) = match dialect {
        "include" => {
            let (input, path) = single_quoted(input)?;
            let (input, selection) = opt(preceded(
                sym(","),
                delimited(sym("["), separated_list0(sym(","), name), sym("]")),
            ))(input)?;
            (input, TopLevel::Include(path, selection))
        }
        "fof" | "tff" | "thf" | "cnf" => {
            let (input, name) = name(input)?;
            let (input, _) = sym(",")(input)?;
            let (input, role) = role(input)?;
            let (input, _) = sym(",")(input)?;
            let (input, formula) = match (dialect, &role) {
                ("tff", Role::Type) => {
                    let (input, declaration) = type_declaration(input)?;
                    (input, TptpFormula::Declaration(declaration))
                }
                ("tff", _) => {
                    let (input, (formula, symbols)) = tff_formula(input)?;
                    (input, TptpFormula::Fol(formula, symbols))
                }
                ("thf", Role::Type) => {
                    let (input, (name, typee)) = thf_type_declaration(input)?;
                    (input, TptpFormula::ThfDeclaration(name, typee))
                }
                ("thf", _) => {
                    let (input, formula) = thf_formula(input)?;
                    (input, TptpFormula::Thf(formula))
                }
                ("fof", _) => {
                    let (input, (formula, symbols)) = fof_formula(input)?;
                    (input, TptpFormula::Fol(formula, symbols))
                }
                _ => {
                    let (input, formula) = cnf_formula(input)?;
                    (input, TptpFormula::Cnf(formula))
                }
            };
            let (input, _) = opt(preceded(sym(","), skip_annotations))(input)?;
            (
                input,
                TopLevel::Input(TptpInput {
                    name,
                    role,
                    formula,
                }),
            )
        }
        other => {
            return Err(nom::Err::Failure(LofError::unsupported(format!(
                "TPTP dialect '{}' is not supported, only 'cnf', 'fof', 'tff' (TF0) and 'thf' (TH0/TH1) are",
                other
            ))))
        }
    };

    let (input, _) = sym(")")(input)?;
    let (input, _) = sym(".")(input)?;
    Ok((input, top_level))
}

/// Parses every top level item of `source`, `origin` only labels errors
fn parse_top_level(
    source: &str,
    origin: &str,
) -> Result<Vec<TopLevel>, LofError> {
    let mut items = vec![];
    let mut input = source;
    loop {
        let (rest, _) = ws0(input)?;
        if rest.is_empty() {
            return Ok(items);
        }
        let (rest, item) = annotated_formula(rest).map_err(|err| {
            LofError::custom(format!(
                "Error parsing TPTP input '{}': {}",
                origin,
                LofError::from(err)
            ))
        })?;
        items.push(item);
        input = rest;
    }
}

/// Parses a self contained TPTP problem. `include` directives are rejected,
/// use `load_tptp_file` to resolve them
pub fn parse_tptp(source: &str) -> Result<TptpProblem, LofError> {
    let mut inputs = vec![];
    for item in parse_top_level(source, "<string>")? {
        match item {
            TopLevel::Input(input) => inputs.push(input),
            TopLevel::Include(path, _) => {
                return Err(LofError::unsupported(format!(
                    "Cannot resolve include('{}') when parsing a string, use `load_tptp_file`",
                    path
                )))
            }
        }
    }
    Ok(TptpProblem { inputs })
}

/// Finds the file `include`d by `including_file`: relative to the including
/// file's directory first, then to the TPTP library root `$TPTP`, then to the
/// working directory
fn resolve_include(
    include: &str,
    including_file: &Path,
) -> Result<PathBuf, LofError> {
    let mut candidates = vec![];
    if let Some(dir) = including_file.parent() {
        candidates.push(dir.join(include));
    }
    if let Ok(tptp_root) = env::var("TPTP") {
        candidates.push(Path::new(&tptp_root).join(include));
    }
    candidates.push(PathBuf::from(include));

    candidates
        .iter()
        .find(|candidate| candidate.is_file())
        .cloned()
        .ok_or_else(|| {
            LofError::custom(format!(
                "Cannot find included file '{}', tried: {:?}",
                include, candidates
            ))
        })
}

fn load_inputs(
    path: &Path,
    loading: &mut Vec<PathBuf>,
) -> Result<Vec<TptpInput>, LofError> {
    let canonical = path.canonicalize().map_err(|err| {
        LofError::custom(format!(
            "Cannot open TPTP file '{}': {}",
            path.display(),
            err
        ))
    })?;
    if loading.contains(&canonical) {
        return Err(LofError::custom(format!(
            "Cyclic include of TPTP file '{}'",
            path.display()
        )));
    }
    loading.push(canonical);

    let origin = path.display().to_string();
    let source = read_file(&origin).map_err(|err| {
        LofError::custom(format!("Cannot read TPTP file '{}': {}", origin, err))
    })?;

    let mut inputs = vec![];
    for item in parse_top_level(&source, &origin)? {
        match item {
            TopLevel::Input(input) => inputs.push(input),
            TopLevel::Include(include, selection) => {
                let included = resolve_include(&include, path)?;
                let included_inputs = load_inputs(&included, loading)?;
                inputs.extend(included_inputs.into_iter().filter(|input| {
                    selection
                        .as_ref()
                        .map_or(true, |names| names.contains(&input.name))
                }));
            }
        }
    }

    loading.pop();
    Ok(inputs)
}

/// Loads the TPTP problem at `path`, recursively resolving `include` directives
pub fn load_tptp_file(path: &str) -> Result<TptpProblem, LofError> {
    let inputs = load_inputs(Path::new(path), &mut vec![])?;
    Ok(TptpProblem { inputs })
}

//############################# PARSING
//
//
//############################# CLAUSIFICATION

/// Prefix of the witnesses introduced by `FolFormula::skolemize`
const SKOLEM_PREFIX: &str = "sw_";

fn is_skolem_witness(name: &str) -> bool {
    name.strip_prefix(SKOLEM_PREFIX).is_some_and(|idx| {
        !idx.is_empty() && idx.chars().all(|c| c.is_ascii_digit())
    })
}

// TODO this works around `skolemize` restarting its witness counter on every call
// (so witnesses of different formulas clash) and nullary witnesses coming out of
// `clausify` as variables. Drop it once `skolemize` generates globally fresh constants
/// Renames the skolem witnesses of the `formula_idx`-th clausified formula
/// apart from the ones of every other formula, turning them into applications
fn rename_skolems(
    clause: &CnfFormula,
    formula_idx: usize,
    constants: &HashSet<String>,
) -> CnfFormula {
    fn rename_term(
        term: &CnfTerm,
        formula_idx: usize,
        constants: &HashSet<String>,
    ) -> CnfTerm {
        let rename = |name: &str| {
            format!("sk{}_{}", formula_idx, &name[SKOLEM_PREFIX.len()..])
        };
        match term {
            Variable(name) if is_skolem_witness(name) => {
                Application(rename(name), vec![])
            }
            Variable(_) => term.clone(),
            Application(name, args) => {
                let args = args
                    .iter()
                    .map(|arg| rename_term(arg, formula_idx, constants))
                    .collect();
                if is_skolem_witness(name) && !constants.contains(name) {
                    Application(rename(name), args)
                } else {
                    Application(name.to_string(), args)
                }
            }
        }
    }

    let rename = |term: &CnfTerm| rename_term(term, formula_idx, constants);
    match clause {
        Atom(pred, args) => {
            Atom(pred.to_string(), args.iter().map(rename).collect())
        }
        Equality(left, right) => Equality(rename(left), rename(right)),
        Not(literal) => {
            Not(Box::new(rename_skolems(literal, formula_idx, constants)))
        }
        Clause(literals) => Clause(
            literals
                .iter()
                .map(|literal| rename_skolems(literal, formula_idx, constants))
                .collect(),
        ),
        ForAll(var, var_type, body) => ForAll(
            var.to_string(),
            Box::new(rename_skolems(var_type, formula_idx, constants)),
            Box::new(rename_skolems(body, formula_idx, constants)),
        ),
    }
}

/// Returns `Some(b)` if `literal` is the truth constant `b` (possibly negated)
fn truth_value(literal: &CnfFormula) -> Option<bool> {
    match literal {
        Atom(pred, args) if args.is_empty() && pred == "$true" => Some(true),
        Atom(pred, args) if args.is_empty() && pred == "$false" => Some(false),
        Not(inner) => truth_value(inner).map(|value| !value),
        _ => None,
    }
}

/// Simplifies away `$true`/`$false` literals: returns `None` if `clause` is
/// trivially true, otherwise the clause without its false literals
fn simplify_truth_constants(clause: &CnfFormula) -> Option<CnfFormula> {
    let mut literals = vec![];
    for literal in clause.unpack_literals() {
        match truth_value(&literal) {
            Some(true) => return None,
            Some(false) => {}
            None => literals.push(literal),
        }
    }
    Some(make_clause(literals))
}

/// Clausifies the FOF formula `φ`, the `formula_idx`-th of its problem
fn clausify_fof(
    φ: &FolFormula,
    constants: &HashSet<String>,
    formula_idx: usize,
) -> Result<Vec<CnfFormula>, LofError> {
    Ok(clausify(φ, constants)?
        .iter()
        .map(|clause| rename_skolems(clause, formula_idx, constants))
        .collect())
}

impl TptpProblem {
    /// Returns the clauses whose unsatisfiability proves the problem, ready for
    /// SUP saturation: CNF inputs are taken as they are, FOF/TFF inputs are
    /// clausified, and FOF/TFF conjectures are jointly negated before
    /// clausification. TFF sorts are erased and type declarations skipped
    // TODO erasing sorts is only sound for monotonic problems (eg no axiom
    // bounding the cardinality of a sort), check it or encode sorts as guards
    pub fn to_clauses(&self) -> Result<Vec<CnfFormula>, LofError> {
        let mut clauses = vec![];
        let mut errors = vec![];
        let mut conjectures = vec![];
        let mut conjecture_constants = HashSet::new();

        for (idx, input) in self.inputs.iter().enumerate() {
            match &input.formula {
                TptpFormula::Cnf(clause) => clauses.push(clause.clone()),
                TptpFormula::Declaration(_) => {}
                TptpFormula::Thf(_) | TptpFormula::ThfDeclaration(_, _) => {
                    errors.push(LofError::unsupported(format!(
                        "THF input '{}' is higher order and cannot be clausified",
                        input.name
                    )))
                }
                TptpFormula::Fol(φ, symbols)
                    if input.role == Role::Conjecture =>
                {
                    conjectures.push(φ.clone());
                    conjecture_constants.extend(symbols.constants());
                }
                TptpFormula::Fol(φ, symbols) => {
                    match clausify_fof(φ, &symbols.constants(), idx) {
                        Ok(new_clauses) => clauses.extend(new_clauses),
                        Err(err) => errors.push(err),
                    }
                }
            }
        }

        // conjectures are proved jointly: refute the negation of their conjunction
        if !conjectures.is_empty() {
            let goal = if conjectures.len() == 1 {
                conjectures.pop().unwrap()
            } else {
                Conjunction(conjectures)
            };
            let negated_goal = FolFormula::Not(Box::new(goal));
            match clausify_fof(
                &negated_goal,
                &conjecture_constants,
                self.inputs.len(),
            ) {
                Ok(new_clauses) => clauses.extend(new_clauses),
                Err(err) => errors.push(err),
            }
        }

        if !errors.is_empty() {
            return Err(LofError::aggregate(errors));
        }
        Ok(clauses
            .iter()
            .filter_map(simplify_truth_constants)
            .collect())
    }
}

//############################# CLAUSIFICATION
//
//
//############################# TYPE CHECKING

impl TptpProblem {
    /// Returns the FOL typing environment declared by the problem's `tff`
    /// type declarations. Symbols used by FOF/TFF formulas but not declared
    /// get the TPTP default types over `$i`. CNF inputs are untyped and ignored
    pub fn environment(&self) -> Result<Environment<Fol>, LofError> {
        let mut declarations = vec![];
        let mut used = Symbols::default();
        for input in &self.inputs {
            match &input.formula {
                TptpFormula::Declaration(declaration) => {
                    declarations.push(declaration.clone())
                }
                TptpFormula::Fol(_, symbols) => used.extend(symbols),
                _ => {}
            }
        }
        build_environment(&declarations, &used)
    }

    /// Type checks every FOF/TFF formula of the problem with the FOL kernel,
    /// returning the typing environment they're well typed in
    pub fn type_check(&self) -> Result<Environment<Fol>, LofError> {
        let mut environment = self.environment()?;
        let mut errors = vec![];
        for input in &self.inputs {
            if let TptpFormula::Fol(φ, _) = &input.formula {
                if let Err(err) = Fol::type_check_type(φ, &mut environment) {
                    errors.push(LofError::custom(format!(
                        "TPTP formula '{}' is ill typed: {}",
                        input.name, err
                    )));
                }
            }
        }

        if errors.is_empty() {
            Ok(environment)
        } else {
            Err(LofError::aggregate(errors))
        }
    }
}

//############################# TYPE CHECKING
//
//
//############################# THF TYPE CHECKING

impl TptpProblem {
    /// Type checks the THF inputs of the problem with the System F kernel.
    /// Declarations extend the HOL environment of `thf::hol_environment`, and
    /// every formula is elaborated and checked to be of type `$o`. Returns the
    /// environment together with the elaborated formulas, by input name
    pub fn type_check_thf(
        &self,
    ) -> Result<(Environment<SystemF>, Vec<(String, FTerm)>), LofError> {
        let mut environment = hol_environment();
        let mut errors = vec![];

        for input in &self.inputs {
            if let TptpFormula::ThfDeclaration(name, typee) = &input.formula {
                let declaration = FStm::Axiom(name.to_string(), typee.clone());
                if let Err(err) =
                    SystemF::type_check_stm(&declaration, &mut environment)
                {
                    errors.push(LofError::custom(format!(
                        "THF declaration '{}' is ill typed: {}",
                        input.name, err
                    )));
                }
            }
        }

        let mut formulas = vec![];
        for input in &self.inputs {
            let TptpFormula::Thf(term) = &input.formula else {
                continue;
            };
            let checked = elaborate(term, &mut environment).and_then(|term| {
                let term_type =
                    SystemF::type_check_term(&term, &mut environment)?;
                if is_formula_type(&term_type) {
                    Ok(term)
                } else {
                    Err(LofError::custom(format!(
                        "expected a formula of type $o, found type {:?}",
                        term_type
                    )))
                }
            });
            match checked {
                Ok(term) => formulas.push((input.name.to_string(), term)),
                Err(err) => errors.push(LofError::custom(format!(
                    "THF formula '{}' is ill typed: {}",
                    input.name, err
                ))),
            }
        }

        if errors.is_empty() {
            Ok((environment, formulas))
        } else {
            Err(LofError::aggregate(errors))
        }
    }
}

//############################# THF TYPE CHECKING
