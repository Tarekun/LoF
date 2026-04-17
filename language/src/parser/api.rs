use crate::{
    config::Config,
    file_manager::{list_sources, read_source_file},
    misc::Union,
};
use nom::{branch::alt, combinator::map, multi::many0, IResult};
use std::{cell::RefCell, collections::BTreeMap};

#[derive(Debug, PartialEq, Clone, Default)]
pub struct Span {
    pub line: u32,
    pub col: u32,
}

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
    Stm(Statement, Span),
    Exp(Expression, Span),
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
    current_source: RefCell<Option<String>>,
}
impl LofParser {
    pub fn new(config: Config) -> LofParser {
        LofParser {
            config,
            custom_notations: RefCell::new(BTreeMap::new()),
            current_source: RefCell::new(None),
        }
    }

    /// Converts a byte offset within `source` to a (line, col) Span (0-indexed).
    fn offset_to_span(source: &str, byte_offset: usize) -> Span {
        let bytes = source.as_bytes();
        let before = &bytes[..byte_offset.min(bytes.len())];
        let line = before.iter().filter(|&&b| b == b'\n').count() as u32;
        let col = match before.iter().rposition(|&b| b == b'\n') {
            Some(last_nl) => byte_offset - last_nl - 1,
            None => byte_offset,
        } as u32;
        Span { line, col }
    }

    /// Returns the Span of `input` relative to the currently stored source string.
    /// Falls back to Span::default() if no source is stored or the pointer is out of range.
    fn input_to_span(&self, input: &str) -> Span {
        let source = self.current_source.borrow();
        if let Some(src) = source.as_deref() {
            let base = src.as_ptr() as usize;
            let ptr = input.as_ptr() as usize;
            if ptr >= base && ptr <= base + src.len() {
                return Self::offset_to_span(src, ptr - base);
            }
        }
        Span::default()
    }

    /// Top level parser for single nodes that wraps expressions and statements
    pub fn parse_node<'a>(&self, input: &'a str) -> IResult<&'a str, LofAst> {
        let span = self.input_to_span(input);
        let result = alt((
            map(
                |input| self.parse_expression(input),
                |exp| LofAst::Exp(exp, span.clone()),
            ),
            map(
                |input| self.parse_statement(input),
                |stm| LofAst::Stm(stm, span.clone()),
            ),
            // TODO why tf was this here? find why + test if it needs to stay here
            map(
                |input| self.parse_theory_block(input),
                |stm| LofAst::Stm(stm, span.clone()),
            ),
        ))(input);
        result
    }

    /// Fully parses the source file at `filepath` and returns its corresponding AST
    pub fn parse_source_file(&self, filepath: &str) -> (String, LofAst) {
        let source = match read_source_file(filepath) {
            Ok(content) => content,
            Err(e) => {
                panic!("Error reading file: {:?}", e);
            }
        };
        // save and restore to handle nested calls like parse_import
        let prev_source = self.current_source.borrow().clone();
        *self.current_source.borrow_mut() = Some(source.clone());
        let result = many0(|input| self.parse_node(input))(&source);
        *self.current_source.borrow_mut() = prev_source;
        let (remaining_input, terms) = match result {
            Ok((remaining, terms)) => (remaining, terms),
            Err(e) => {
                panic!("Parsing error: {:?}", e);
            }
        };

        (
            remaining_input.to_string(),
            LofAst::Stm(
                Statement::FileRoot(filepath.to_string(), terms),
                Span::default(),
            ),
        )
    }

    /// Fully parses the code contained in `workspace` amd returns its corresponding AST
    pub fn parse_workspace(
        &self,
        _config: &Config,
        workspace: &str,
    ) -> Result<LofAst, String> {
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
            std::env::set_current_dir(workspace).map_err(|e| e.to_string())?;
        }
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
        Ok(LofAst::Stm(
            Statement::DirRoot(workspace.to_string(), asts),
            Span::default(),
        ))
    }
}
