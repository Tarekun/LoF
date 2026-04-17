use crate::{
    config::Config,
    file_manager::{list_sources, read_source_file},
    misc::Union,
};
use nom::{branch::alt, combinator::map, multi::many0, IResult};
use std::{cell::Cell, cell::RefCell, collections::BTreeMap};

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
    // Raw pointer + length of the source string currently being parsed.
    // Valid only while parse_source_file is on the call stack.
    // Using Cell (not RefCell) so nested parse_source_file calls (e.g. from
    // parse_import) can safely save/restore the value without a borrow conflict.
    current_source: Cell<Option<(*const u8, usize)>>,
}
impl LofParser {
    pub fn new(config: Config) -> LofParser {
        LofParser {
            config,
            custom_notations: RefCell::new(BTreeMap::new()),
            current_source: Cell::new(None),
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

    /// Returns the Span of `input` relative to the currently tracked source.
    /// Falls back to Span::default() if no source is tracked or the pointer is out of range.
    fn input_to_span(&self, input: &str) -> Span {
        if let Some((base_ptr, len)) = self.current_source.get() {
            let base = base_ptr as usize;
            let ptr = input.as_ptr() as usize;
            if ptr >= base && ptr <= base + len {
                // Safety: base_ptr was recorded from a live &str in parse_source_file,
                // which is still on the call stack (we are executing inside many0's
                // closure), so the pointed-to allocation is still valid.
                let src = unsafe {
                    std::str::from_utf8_unchecked(std::slice::from_raw_parts(base_ptr, len))
                };
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
        // Save and restore so that nested calls (e.g. parse_import → parse_source_file)
        // track the inner file while parsing it and restore the outer file afterward.
        // We store a raw pointer to `source`'s allocation; it is valid for the entire
        // duration of the many0 call below since `source` lives until the end of this fn.
        let prev = self.current_source.get();
        self.current_source.set(Some((source.as_ptr(), source.len())));
        let result = many0(|input| self.parse_node(input))(&source);
        self.current_source.set(prev);
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

#[cfg(test)]
mod span_tests {
    use super::*;
    use crate::config::Config;

    fn make_parser() -> LofParser {
        LofParser::new(Config::default())
    }

    fn span_of(node: &LofAst) -> Span {
        match node {
            LofAst::Exp(_, s) | LofAst::Stm(_, s) => s.clone(),
        }
    }

    // ── offset_to_span ────────────────────────────────────────────────────────

    #[test]
    fn offset_to_span_start() {
        assert_eq!(LofParser::offset_to_span("hello", 0), Span { line: 0, col: 0 });
    }

    #[test]
    fn offset_to_span_mid_first_line() {
        // offset 6 → column 6, still line 0
        assert_eq!(LofParser::offset_to_span("hello world", 6), Span { line: 0, col: 6 });
    }

    #[test]
    fn offset_to_span_start_of_second_line() {
        // "abc\ndef" — 'd' is at offset 4
        assert_eq!(LofParser::offset_to_span("abc\ndef", 4), Span { line: 1, col: 0 });
    }

    #[test]
    fn offset_to_span_mid_second_line() {
        // "abc\ndef" — 'f' is at offset 6
        assert_eq!(LofParser::offset_to_span("abc\ndef", 6), Span { line: 1, col: 2 });
    }

    #[test]
    fn offset_to_span_third_line() {
        // "a\nb\nc" — 'c' is at offset 4
        assert_eq!(LofParser::offset_to_span("a\nb\nc", 4), Span { line: 2, col: 0 });
    }

    // ── parse_node span tracking ──────────────────────────────────────────────

    #[test]
    fn parse_node_span_at_start() {
        // A node parsed from the very beginning of the source sits at (0, 0).
        let p = make_parser();
        let source = "x".to_string();
        p.current_source.set(Some((source.as_ptr(), source.len())));
        let (_, node) = p.parse_node(&source).unwrap();
        assert_eq!(span_of(&node), Span { line: 0, col: 0 });
    }

    #[test]
    fn parse_node_span_mid_line() {
        // Parsing from byte 3 inside "   x" reports column 3.
        let p = make_parser();
        let source = "   x".to_string();
        p.current_source.set(Some((source.as_ptr(), source.len())));
        let (_, node) = p.parse_node(&source[3..]).unwrap();
        assert_eq!(span_of(&node), Span { line: 0, col: 3 });
    }

    #[test]
    fn parse_node_span_second_line() {
        // "x\ny" — 'y' starts at byte 2, which is line 1, col 0.
        let p = make_parser();
        let source = "x\ny".to_string();
        p.current_source.set(Some((source.as_ptr(), source.len())));
        let (_, node) = p.parse_node(&source[2..]).unwrap();
        assert_eq!(span_of(&node), Span { line: 1, col: 0 });
    }

    #[test]
    fn parse_node_span_mid_second_line() {
        // "ab\ncd" — 'd' starts at byte 4, which is line 1, col 1.
        let p = make_parser();
        let source = "ab\ncd".to_string();
        p.current_source.set(Some((source.as_ptr(), source.len())));
        let (_, node) = p.parse_node(&source[4..]).unwrap();
        assert_eq!(span_of(&node), Span { line: 1, col: 1 });
    }

    #[test]
    fn parse_node_span_no_source_defaults_to_zero() {
        // When no source is registered the span defaults to (0, 0).
        let p = make_parser();
        let (_, node) = p.parse_node("x").unwrap();
        assert_eq!(span_of(&node), Span { line: 0, col: 0 });
    }

    #[test]
    fn parse_node_sequential_nodes_get_correct_spans() {
        // Parse two clearly delimited statements from a multi-line source and
        // verify each node carries the span of where its input slice began.
        let p = make_parser();
        // "axiom x : TYPE;\naxiom y : TYPE;"
        //  0123456789...14 15
        //  first statement is 15 bytes, then '\n' at byte 15, second starts at byte 16
        let source = "axiom x : TYPE;\naxiom y : TYPE;".to_string();
        p.current_source.set(Some((source.as_ptr(), source.len())));

        let (remaining, first) = p.parse_node(&source).unwrap();
        let (_, second) = p.parse_node(remaining).unwrap();

        assert_eq!(span_of(&first), Span { line: 0, col: 0 });
        // `remaining` begins at the '\n' (byte 15): still line 0, col 15.
        // parse_node records the span *before* consuming leading whitespace.
        assert_eq!(span_of(&second), Span { line: 0, col: 15 });
    }
}
