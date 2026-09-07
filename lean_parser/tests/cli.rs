//! Smoke tests for the `lean_parser` binary, run as a subprocess via
//! `CARGO_BIN_EXE_lean_parser`.

use std::path::Path;
use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_lean_parser"))
}

fn corpus_file(rel: &str) -> String {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/corpus")
        .join(rel)
        .display()
        .to_string()
}

#[test]
fn parses_a_clean_file_and_exits_zero() {
    let out = bin().arg(corpus_file("lof/unit.lean")).output().unwrap();
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json["decls"][0]["kind"], "inductive");
}

#[test]
fn pretty_flag_produces_multiline_output() {
    let out = bin()
        .args(["--pretty", &corpus_file("lof/unit.lean")])
        .output()
        .unwrap();
    assert!(out.status.success());
    assert!(String::from_utf8_lossy(&out.stdout).contains('\n'));
}

#[test]
fn no_spans_flag_strips_span_keys() {
    let out = bin()
        .args(["--no-spans", &corpus_file("lof/unit.lean")])
        .output()
        .unwrap();
    assert!(out.status.success());
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(!text.contains("\"span\""));
}

#[test]
fn tokens_flag_emits_a_token_stream() {
    let out = bin()
        .args(["--tokens", &corpus_file("lof/unit.lean")])
        .output()
        .unwrap();
    assert!(out.status.success());
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert!(json.as_array().unwrap().len() > 1);
}

#[test]
fn a_bad_file_exits_nonzero_unless_lenient() {
    let strict = bin()
        .arg(corpus_file("bad/missing_arrow_rhs.lean"))
        .output()
        .unwrap();
    assert!(!strict.status.success());

    let lenient = bin()
        .args(["--lenient", &corpus_file("bad/missing_arrow_rhs.lean")])
        .output()
        .unwrap();
    assert!(lenient.status.success());
}

#[test]
fn help_flag_prints_usage_and_exits_zero() {
    let out = bin().arg("--help").output().unwrap();
    assert!(out.status.success());
    assert!(String::from_utf8_lossy(&out.stdout).contains("lean_parser"));
}

#[test]
fn missing_path_exits_nonzero() {
    let out = bin().output().unwrap();
    assert!(!out.status.success());
}

#[test]
fn workspace_mode_parses_a_directory() {
    let out = bin().arg(corpus_file("lof")).output().unwrap();
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json["kind"], "workspace");
    assert!(json["modules"].as_array().unwrap().len() >= 5);
}
