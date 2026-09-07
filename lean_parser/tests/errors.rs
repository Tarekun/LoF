//! Error-path tests: every `.lean` file under `tests/corpus/bad/`
//! carries a `-- EXPECT: <line>:<col>` comment on its first line, and
//! must produce a diagnostic (either a lex-level `Err`, or the first
//! `DeclKind::Error` node's message) whose leading `"{line}:{col}: "`
//! prefix -- every `LeanError` variant's `Display` starts with exactly
//! that -- matches it.

use std::path::{Path, PathBuf};

use lean_parser::ast::decl::DeclKind;

fn bad_corpus_files() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/bad");
    let mut out: Vec<PathBuf> = std::fs::read_dir(&root)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("lean"))
        .collect();
    out.sort();
    out
}

/// Parses the `-- EXPECT: <line>:<col>` annotation off a file's first
/// line.
fn expected_position(src: &str) -> (u32, u32) {
    let first_line = src.lines().next().unwrap();
    let rest = first_line
        .strip_prefix("-- EXPECT:")
        .unwrap_or_else(|| {
            panic!("first line must be `-- EXPECT: L:C`, got {first_line:?}")
        })
        .trim();
    let mut parts = rest.splitn(2, ':');
    let line: u32 = parts.next().unwrap().trim().parse().unwrap();
    let col: u32 = parts.next().unwrap().trim().parse().unwrap();
    (line, col)
}

/// Every `LeanError` variant's `Display` starts with `"{line}:{col}: "`,
/// optionally preceded by an `InFile` wrapper's `"error in '<path>': "`.
/// Strips the wrapper if present, then reads the leading `L:C`.
fn extract_line_col(message: &str) -> (u32, u32) {
    let message = match message.find("': ") {
        Some(idx) if message.starts_with("error in '") => &message[idx + 3..],
        _ => message,
    };
    let mut parts = message.splitn(3, ':');
    let line: u32 = parts
        .next()
        .unwrap_or_else(|| panic!("malformed message: {message:?}"))
        .trim()
        .parse()
        .unwrap_or_else(|_| panic!("malformed message: {message:?}"));
    let col: u32 = parts
        .next()
        .unwrap_or_else(|| panic!("malformed message: {message:?}"))
        .trim()
        .parse()
        .unwrap_or_else(|_| panic!("malformed message: {message:?}"));
    (line, col)
}

#[test]
fn every_bad_corpus_file_reports_its_expected_position() {
    let mut failures = Vec::new();
    for path in bad_corpus_files() {
        let src = std::fs::read_to_string(&path).unwrap();
        let expected = expected_position(&src);

        let message =
            match lean_parser::parse_str(&path.display().to_string(), &src) {
                Err(e) => e.to_string(),
                Ok(module) => {
                    match module.decls.iter().find_map(|d| match &d.kind {
                        DeclKind::Error { message, .. } => {
                            Some(message.clone())
                        }
                        _ => None,
                    }) {
                        Some(m) => m,
                        None => {
                            failures.push(format!(
                                "{}: expected a parse failure, but the file \
                             parsed with no error nodes",
                                path.display()
                            ));
                            continue;
                        }
                    }
                }
            };

        let actual = extract_line_col(&message);
        if actual != expected {
            failures.push(format!(
                "{}: expected error at {}:{}, got {}:{} (message: {message:?})",
                path.display(),
                expected.0,
                expected.1,
                actual.0,
                actual.1
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "error-position mismatches:\n{}",
        failures.join("\n")
    );
}
