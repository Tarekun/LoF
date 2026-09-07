//! Thin CLI entry point: parses args, runs the requested parse
//! (`--tokens` for the raw lexer output, otherwise the full AST) over a
//! file or a directory, and writes JSON to stdout or `--output FILE`.

use std::path::Path;
use std::process::ExitCode;

use lean_parser::ast::decl::Module;
use lean_parser::cli::{parse_args, Options, USAGE};
use lean_parser::{emit, error::LeanError, file_manager, lexer, parser};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(opts) = parse_args(&args) else {
        eprint!("{USAGE}");
        return ExitCode::FAILURE;
    };
    if opts.help {
        print!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    match run(&opts) {
        Ok(had_errors) => {
            if had_errors && !opts.lenient {
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(e) => {
            eprintln!("lean_parser: {e}");
            ExitCode::FAILURE
        }
    }
}

/// Runs the requested parse and writes its JSON output. Returns whether
/// the result contains any error node (used to pick the exit code,
/// unless `--lenient` was given).
fn run(opts: &Options) -> Result<bool, LeanError> {
    let path = Path::new(&opts.path);
    if opts.tokens {
        return run_tokens(opts, path);
    }
    if path.is_dir() {
        run_workspace(opts, path)
    } else {
        run_single_file(opts, path)
    }
}

fn write_output(opts: &Options, json: &str) -> Result<(), LeanError> {
    match &opts.output {
        Some(file) => std::fs::write(file, json).map_err(LeanError::Io),
        None => {
            println!("{json}");
            Ok(())
        }
    }
}

fn run_tokens(opts: &Options, path: &Path) -> Result<bool, LeanError> {
    let src = file_manager::read_source_file(path)?;
    let toks = lexer::lex(&src)
        .map_err(|e| LeanError::in_file(opts.path.clone(), e))?;
    let json = emit::to_json_string(&toks, opts.pretty, opts.no_spans)?;
    write_output(opts, &json)?;
    Ok(false)
}

fn run_single_file(opts: &Options, path: &Path) -> Result<bool, LeanError> {
    let module = lean_parser::parse_file(path)?;
    let had_errors = parser::api::has_errors(&module.decls);
    let json = emit::to_json_string(&module, opts.pretty, opts.no_spans)?;
    write_output(opts, &json)?;
    Ok(had_errors)
}

fn run_workspace(opts: &Options, path: &Path) -> Result<bool, LeanError> {
    let (modules, errors) = lean_parser::parse_workspace(path, opts.recursive)?;
    let had_decl_errors = modules
        .iter()
        .any(|m: &Module| parser::api::has_errors(&m.decls));
    let had_errors = had_decl_errors || !errors.is_empty();
    let value = serde_json::json!({
        "kind": "workspace",
        "root": opts.path,
        "modules": modules,
        "errors": errors.iter().map(|e| e.to_string()).collect::<Vec<_>>(),
    });
    let json = emit::to_json_string(&value, opts.pretty, opts.no_spans)?;
    write_output(opts, &json)?;
    Ok(had_errors)
}
