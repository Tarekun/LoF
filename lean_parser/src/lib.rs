//! `lean_parser` — a syntactic parser for a subset of Lean 4, producing a
//! serde-serializable AST (emitted as JSON by the accompanying CLI).
//!
//! Scope is deliberately narrow: it targets roughly the surface features
//! the `proofr`/`language` crate's own `.lof` language supports (defs and
//! recursion, inductives, theorems with term or tactic proofs, `match`,
//! `let`, arrows/Pi-types, holes, imports, comments) rather than all of
//! Lean 4. See `README.md` for the full in-scope/non-goal table.
//!
//! Pipeline: `lexer` (`&str` -> `Vec<Token>`) -> `tokens` (nom-7 input
//! traits over a token slice) -> `parser` (nom combinators -> `ast`).
//! Nothing here integrates with the `language` crate; the only interface
//! this crate exposes is the JSON produced by `emit`.

pub mod ast;
pub mod cli;
pub mod emit;
pub mod error;
pub mod file_manager;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod tokens;

pub use error::LeanError;

use ast::decl::Module;

/// Parse a single `.lean` source string (given a display name used in
/// spans/errors, e.g. the file path) into a `Module`.
pub fn parse_str(name: &str, src: &str) -> Result<Module, LeanError> {
    let toks =
        lexer::lex(src).map_err(|e| LeanError::in_file(name.to_string(), e))?;
    parser::api::parse_module(name, src, &toks)
        .map_err(|e| LeanError::in_file(name.to_string(), e))
}

/// Parse a single `.lean` file from disk into a `Module`.
pub fn parse_file(path: &std::path::Path) -> Result<Module, LeanError> {
    let src = file_manager::read_source_file(path)?;
    parse_str(&path.display().to_string(), &src)
}

/// Parse every `.lean` file found under `root` (see
/// `file_manager::list_sources`) into a list of `Module`s. Parse failures
/// on individual files are collected rather than aborting the whole run.
pub fn parse_workspace(
    root: &std::path::Path,
    recursive: bool,
) -> Result<(Vec<Module>, Vec<LeanError>), LeanError> {
    let paths = file_manager::list_sources(root, recursive)?;
    let mut modules = Vec::new();
    let mut errors = Vec::new();
    for path in paths {
        match parse_file(&path) {
            Ok(m) => modules.push(m),
            Err(e) => errors.push(e),
        }
    }
    Ok((modules, errors))
}
