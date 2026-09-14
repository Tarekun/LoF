use crate::{
    config::Config,
    error::LofError,
    file_manager::{list_sources, read_source_file},
    misc::Union,
};
use nom::{branch::alt, combinator::map, multi::many0};
use std::{cell::RefCell, collections::BTreeMap};

/// The parser's own `IResult`, wired to `LofError` so parse failures join
/// the same error framework used by the rest of the pipeline.
pub type PResult<'a, T> = nom::IResult<&'a str, T, LofError>;

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    VarUse(String),
    /// (var_name, var_type, function_body)
    Abstraction(String, Box<Expression>, Box<Expression>),
    /// (var_name, var_type, dependent_type)
    TypeProduct(String, Box<Expression>, Box<Expression>),
    /// (domain, codomain)
    Arrow(Box<Expression>, Box<Expression>),
    /// function, args
    Application(Box<Expression>, Vec<Expression>),
    /// (matched_term, [ branch: (pattern, body) ])
    Match(Box<Expression>, Vec<(Expression, Expression)>),
    // Infer operator to be elaborated to metavariables
    Inferator(),
    /// [conjunted terms]
    Tuple(Vec<Expression>),
    /// [disjunted types]
    Pipe(Vec<Expression>),
    /// (var_name, var_type, definition_body, scope)
    Let(
        String,
        Box<Option<Expression>>,
        Box<Expression>,
        Box<Expression>,
    ),
}
#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Comment(),
    FileRoot(String, Vec<LofAst>),
    DirRoot(String, Vec<LofAst>),
    EmptyRoot(Vec<LofAst>),
    Axiom(String, Box<Expression>),
    /// (theorem_name, formula, proof)
    Theorem(
        String,
        Expression,
        Union<Expression, Vec<Tactic<Expression>>>,
    ),
    /// (var_name, var_type, definition_body)
    Global(String, Option<Expression>, Expression),
    /// (fun_name, args, out_type, body, is_rec)
    Fun(
        String,
        Vec<(String, Expression)>,
        Box<Expression>,
        Box<Expression>,
        bool,
    ),
    /// type_name, [(param_name : param_type)], ariety, [( constr_name, constr_type )]
    Inductive(
        String,
        Vec<(String, Expression)>,
        Box<Expression>,
        Vec<(String, Expression)>,
    ),
    Auto(Expression),
    /// formulas
    Solve(Vec<Expression>),
    /// head, [subgoals]
    HClause(Expression, Vec<Expression>),
    /// (equivalence_name, type_a, type_b, forward, backward, section,
    /// retraction, dep_elim, opt_eta, dep_constr entries, iota entries)
    Equivalence(
        String,
        Box<Expression>,
        Box<Expression>,
        Box<Expression>,
        Box<Expression>,
        Box<Expression>,
        Box<Expression>,
        Box<Expression>,
        Option<Box<Expression>>,
        Vec<(String, Expression)>,
        Vec<(String, Expression)>,
    ),
    /// (new_name, new_formula_or_type, old_name, equivalence_name)
    Transport(String, Box<Expression>, String, String),
}
#[derive(Debug, PartialEq, Clone)]
pub enum Tactic<E> {
    Begin(),
    Qed(),
    Intro(String, E),
    Exact(E),
    Apply(E),
}
#[derive(Debug, PartialEq, Clone)]
pub enum LofAst {
    Stm(Statement),
    Exp(Expression),
}

#[derive(Debug)]
pub struct Notation {
    pub pattern_tokens: Vec<String>,
    pub body: Expression,
    // pub precedence: i32,
}

#[derive(Debug)]
pub struct LofParser {
    pub config: Config,
    pub custom_notations: RefCell<BTreeMap<i32, Notation>>,
}
impl LofParser {
    pub fn new(config: Config) -> LofParser {
        LofParser {
            config,
            custom_notations: RefCell::new(BTreeMap::new()),
        }
    }

    /// Top level parser for single nodes that wraps expressions and statements
    pub fn parse_node<'a>(&self, input: &'a str) -> PResult<'a, LofAst> {
        alt((
            map(|input| self.parse_expression(input), LofAst::Exp),
            map(|input| self.parse_statement(input), LofAst::Stm),
            // TODO why tf was this here? find why + test if it needs to stay here
            map(|input| self.parse_theory_block(input), LofAst::Stm),
        ))(input)
    }

    /// Fully parses the source file at `filepath` and returns its corresponding AST
    pub fn parse_source_file(
        &self,
        filepath: &str,
    ) -> Result<(String, LofAst), LofError> {
        let source = read_source_file(filepath)?;
        let (remaining_input, terms) = many0(|input| self.parse_node(input))(&source)?;

        Ok((
            remaining_input.to_string(),
            LofAst::Stm(Statement::FileRoot(filepath.to_string(), terms)),
        ))
    }

    /// Fully parses the code contained in `workspace` amd returns its corresponding AST
    pub fn parse_workspace(
        &self,
        _config: &Config,
        workspace: &str,
    ) -> Result<LofAst, LofError> {
        let workspace_is_dir = std::path::Path::new(workspace).is_dir();
        let workspace_path = std::path::Path::new(workspace);
        let lof_files: Vec<String> = list_sources(workspace)
            .into_iter()
            .map(|f| {
                if workspace_is_dir {
                    std::path::Path::new(&f)
                        .strip_prefix(workspace_path)
                        .map(|p| p.to_string_lossy().into_owned())
                        .unwrap_or(f)
                } else {
                    f
                }
            })
            .collect();
        if workspace_is_dir {
            std::env::set_current_dir(workspace)?;
        }
        let mut asts = vec![];
        let mut errors = vec![];

        if lof_files.is_empty() {
            panic!("Directory {} is not a LoF workspace", workspace);
        }
        for filepath in lof_files {
            let (remainder, ast) = self.parse_source_file(&filepath)?;
            if !remainder.chars().all(|c| c.is_whitespace()) {
                errors.push(LofError::leftover_input(filepath, remainder));
            } else {
                asts.push(ast);
            }
        }

        if !errors.is_empty() {
            return Err(LofError::aggregate(errors));
        }
        Ok(LofAst::Stm(Statement::DirRoot(workspace.to_string(), asts)))
    }
}
