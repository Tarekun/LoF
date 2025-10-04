use crate::{
    config::Config,
    file_manager::{list_sources, read_source_file},
    misc::Union,
};
use nom::{branch::alt, combinator::map, multi::many0, IResult};
use std::{cell::RefCell, collections::BTreeMap};

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
    Global(String, Option<Expression>, Box<Expression>),
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
}
#[derive(Debug, PartialEq, Clone)]
pub enum Tactic<E> {
    Begin(),
    Qed(),
    Suppose(String, E),
    By(E),
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
    pub fn parse_node<'a>(&self, input: &'a str) -> IResult<&'a str, LofAst> {
        alt((
            map(|input| self.parse_expression(input), LofAst::Exp),
            map(|input| self.parse_statement(input), LofAst::Stm),
            map(|input| self.parse_theory_block(input), LofAst::Stm),
        ))(input)
    }

    /// Fully parses the source file at `filepath` and returns its corresponding AST
    pub fn parse_source_file(&self, filepath: &str) -> (String, LofAst) {
        let source = match read_source_file(filepath) {
            Ok(content) => content,
            Err(e) => {
                panic!("Error reading file: {:?}", e);
            }
        };
        let result = many0(|input| self.parse_node(input))(&source);
        let (remaining_input, terms) = match result {
            Ok((remaining, terms)) => (remaining, terms),
            Err(e) => {
                panic!("Parsing error: {:?}", e);
            }
        };

        (
            remaining_input.to_string(),
            LofAst::Stm(Statement::FileRoot(filepath.to_string(), terms)),
        )
    }

    /// Fully parses the code contained in `workspace` amd returns its corresponding AST
    pub fn parse_workspace(
        &self,
        _config: &Config,
        workspace: &str,
    ) -> Result<LofAst, String> {
        let lof_files: Vec<String> = list_sources(workspace);
        let mut asts = vec![];
        let mut errors = vec![];

        if lof_files.is_empty() {
            panic!("Directory {} is not a LoF workspace", workspace);
        }
        for filepath in lof_files {
            let (remainder, ast) = self.parse_source_file(&filepath);
            if !remainder.chars().all(|c| c.is_whitespace()) {
                errors.push(format!(
                    "Error parsing file '{}'. Remaining code:\n'{}'",
                    filepath, remainder
                ));
            } else {
                asts.push(ast);
            }
        }

        if !errors.is_empty() {
            return Err(errors.join("\n"));
        }
        Ok(LofAst::Stm(Statement::DirRoot(workspace.to_string(), asts)))
    }
}
