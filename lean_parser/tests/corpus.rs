//! Corpus tests: every `.lean` file under `tests/corpus/` (excluding
//! `bad/`, covered by `tests/errors.rs`) must parse with zero error
//! nodes, round-trip losslessly through JSON, and match a golden JSON
//! file (regenerated with `UPDATE_EXPECT=1 cargo test`). Every span in
//! the tree is also checked for basic sanity (`start <= end <= len`,
//! valid char boundaries), which catches most span-computation bugs in
//! one sweep across the whole corpus.

use std::path::{Path, PathBuf};

use lean_parser::ast::decl::{DeclKind, Module};

fn corpus_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

fn walk_lean_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_dir() {
            walk_lean_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
            out.push(path);
        }
    }
}

fn good_corpus_files() -> Vec<PathBuf> {
    let root = corpus_root();
    let bad_dir = root.join("bad");
    let mut all = Vec::new();
    walk_lean_files(&root, &mut all);
    all.retain(|p| !p.starts_with(&bad_dir));
    all.sort();
    all
}

fn collect_error_messages(module: &Module) -> Vec<String> {
    module
        .decls
        .iter()
        .filter_map(|d| match &d.kind {
            DeclKind::Error { message, .. } => Some(message.clone()),
            _ => None,
        })
        .collect()
}

/// Recursively asserts every `{"span": {...}}` object in `value` has
/// sane byte offsets relative to `src`.
fn check_spans(value: &serde_json::Value, src: &str, path: &Path) {
    match value {
        serde_json::Value::Object(map) => {
            if let Some(span) = map.get("span") {
                let start = span["start"].as_u64().unwrap() as usize;
                let end = span["end"].as_u64().unwrap() as usize;
                assert!(
                    start <= end,
                    "{}: span start {start} > end {end}",
                    path.display()
                );
                assert!(
                    end <= src.len(),
                    "{}: span end {end} exceeds source length {}",
                    path.display(),
                    src.len()
                );
                assert!(
                    src.is_char_boundary(start) && src.is_char_boundary(end),
                    "{}: span [{start}, {end}) is not on a char boundary",
                    path.display()
                );
                let line = span["line"].as_u64().unwrap();
                assert!(
                    line >= 1,
                    "{}: span line must be >= 1",
                    path.display()
                );
            }
            for v in map.values() {
                check_spans(v, src, path);
            }
        }
        serde_json::Value::Array(items) => {
            for v in items {
                check_spans(v, src, path);
            }
        }
        _ => {}
    }
}

fn golden_path(lean_path: &Path) -> PathBuf {
    let root = corpus_root();
    let rel = lean_path.strip_prefix(&root).unwrap();
    root.join("expected").join(rel).with_extension("json")
}

#[test]
fn every_good_corpus_file_parses_cleanly_and_matches_its_golden() {
    let update = std::env::var("UPDATE_EXPECT").is_ok();
    let mut failures = Vec::new();
    for path in good_corpus_files() {
        let src = std::fs::read_to_string(&path).unwrap();
        // Use a path relative to the corpus root as the module's
        // recorded name: the golden files are checked in, so they must
        // not embed this machine's absolute checkout path.
        let rel_name = path
            .strip_prefix(corpus_root())
            .unwrap()
            .display()
            .to_string();
        let module = match lean_parser::parse_str(&rel_name, &src) {
            Ok(m) => m,
            Err(e) => {
                failures.push(format!("{}: lex error: {e}", path.display()));
                continue;
            }
        };

        let errs = collect_error_messages(&module);
        if !errs.is_empty() {
            failures.push(format!(
                "{}: produced {} error node(s): {:?}",
                path.display(),
                errs.len(),
                errs
            ));
            continue;
        }

        // 1. JSON round-trip: the AST must be losslessly readable back.
        let value = serde_json::to_value(&module).unwrap();
        let back: Module = serde_json::from_value(value.clone()).unwrap();
        assert_eq!(
            module,
            back,
            "{}: Module did not round-trip through JSON",
            path.display()
        );

        // 2. Span sanity, across the whole tree.
        check_spans(&value, &src, &path);

        // 3. Golden comparison (structural, via serde_json::Value so
        // key order/formatting don't matter).
        let gpath = golden_path(&path);
        if update {
            std::fs::create_dir_all(gpath.parent().unwrap()).unwrap();
            let pretty = serde_json::to_string_pretty(&value).unwrap();
            std::fs::write(&gpath, pretty + "\n").unwrap();
        } else {
            let expected_str =
                std::fs::read_to_string(&gpath).unwrap_or_else(|_| {
                    panic!(
                        "missing golden {} -- run with UPDATE_EXPECT=1 to \
                         generate it",
                        gpath.display()
                    )
                });
            let expected: serde_json::Value =
                serde_json::from_str(&expected_str).unwrap();
            if expected != value {
                failures.push(format!(
                    "{}: does not match golden {} (run with \
                     UPDATE_EXPECT=1 to update)",
                    path.display(),
                    gpath.display()
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "corpus failures:\n{}",
        failures.join("\n")
    );
}
