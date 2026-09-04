//! Ad hoc benchmark comparing the saturation-based ATP pipeline against the
//! SLD-resolution pipeline (see `sld.rs`) on the same set of Horn-clause
//! problems, reporting wall-clock time and peak resident memory for each.
//!
//! This is a development tool, not a correctness suite, so it's gated
//! behind `#[ignore]`. Run it explicitly, and in release mode (a debug
//! build's timings/allocation patterns aren't representative of anything):
//!
//!   cargo test --release sld_vs_saturation_benchmark -- --ignored --nocapture
//!
//! Problems are read from the file named by the `SLD_BENCH_PROBLEMS_FILE`
//! env var, or by default `benches/sld_vs_saturation_problems.txt` in the
//! crate root — see that file's header comment for the problem syntax. Point
//! `SLD_BENCH_PROBLEMS_FILE` at your own file to try other problems without
//! touching this code.
//!
//! Tuning knobs (env vars, all optional):
//!   SLD_BENCH_REPEATS       how many times each engine re-runs a problem,
//!                           reporting the fastest run (default 5)
//!   SLD_BENCH_TIMEOUT_SECS  per-run wall-clock budget before giving up and
//!                           reporting "timeout" (default 2)
//!
//! Peak memory is read from `/proc/self/status`'s `VmHWM`, reset before each
//! run via `/proc/self/clear_refs` (Linux-only; falls back to reporting
//! peak memory as unavailable everywhere else).
//!
//! A note on what this benchmark found: saturation is a general-purpose
//! calculus with no notion of "goal-directedness", so even once it's sound
//! and complete its given-clause heuristics can still be a poor match for
//! definite-clause logic programs - exactly the fragment SLD is specialized
//! for - and its running time doesn't grow monotonically/predictably with
//! problem size (see `peano_mult`'s comparatively large speedup below for a
//! small problem). One specific, more fundamental limit worth calling out:
//! saturation can only ever *confirm* unsatisfiability in finite time (by
//! deriving the empty clause) - confirming *satisfiability* by exhausting
//! its search queue is undecidable in general, and for a program with an
//! infinite family of consequences (eg this file's recursive `add` rule,
//! which keeps generating add(1,M,s(M)), add(2,M,s(s(M))), ... forever)
//! that queue never actually empties. `peano_add_unsatisfiable` below is
//! kept specifically to demonstrate this: SLD reports "failed" instantly
//! (it only ever searches downward from the goal, so it hits a dead end
//! quickly), while saturation can time out trying to prove the negative.
//! That's why a disagreement between the two engines is *reported*, not
//! treated as a test failure: for this class of problem it can reflect a
//! real, expected capability/performance difference rather than a bug in
//! either pipeline (see the `expect:` directive below, which records what
//! SLD - trusted as ground truth here, see its own unit tests - says a
//! problem's answer should be).

use crate::config::SelectionFunction;
use crate::error::LofError;
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::fol::fol::FolFormula::{self, Arrow, Conjunction, Not, Predicate};
use crate::type_theory::fol::fol::FolTerm;
use crate::type_theory::fol::fol_utils::{clausify, make_multiarg_app};
use crate::type_theory::sup::freedom::{get_selection_fn, pick_clause_weighted};
use crate::type_theory::sup::saturation::saturate;
use crate::type_theory::sup::sld::sld_solve;
use crate::type_theory::sup::sup::SupTerm;
use crate::type_theory::sup::sup_utils::standardize_apart;
use std::collections::HashSet;
use std::fs;
use std::sync::mpsc;
use std::time::{Duration, Instant};

//########################### AD HOC PROBLEM FILE PARSING

struct Problem {
    name: String,
    constants: HashSet<String>,
    assumptions: Vec<FolFormula>,
    goals: Vec<FolFormula>,
    /// Ground truth for whether the goal follows from the assumptions,
    /// taken from the `expect:` directive (default: `proved`). SLD is
    /// simple/complete enough for this Horn fragment that we trust it to
    /// match this; saturation is only checked against it informationally.
    expect_proved: bool,
}

/// Minimal recursive-descent cursor over the problem file's term/atom syntax:
/// `name` or `name(arg, arg, ...)`, arguments nesting arbitrarily.
struct CharCursor {
    chars: Vec<char>,
    pos: usize,
}

impl CharCursor {
    fn new(s: &str) -> Self {
        CharCursor { chars: s.chars().collect(), pos: 0 }
    }
    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }
    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }
    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(c) if c.is_whitespace()) {
            self.pos += 1;
        }
    }
    fn rest(&self) -> String {
        self.chars[self.pos..].iter().collect()
    }
    fn parse_ident(&mut self) -> String {
        self.skip_ws();
        let start = self.pos;
        while matches!(self.peek(), Some(c) if c.is_alphanumeric() || c == '_') {
            self.pos += 1;
        }
        assert!(self.pos > start, "expected an identifier, found {:?}", self.rest());
        self.chars[start..self.pos].iter().collect()
    }
    fn parse_arg_list(&mut self) -> Vec<FolTerm> {
        let mut args = vec![self.parse_term()];
        loop {
            self.skip_ws();
            if self.peek() == Some(',') {
                self.bump();
                args.push(self.parse_term());
            } else {
                break;
            }
        }
        args
    }
    /// A bare `name` is always parsed as a logic variable here: whether it
    /// ends up meaning a variable or a 0-ary constant is decided later, by
    /// the same `constants` set the FOL->SUP clausifier itself consults.
    fn parse_term(&mut self) -> FolTerm {
        let name = self.parse_ident();
        self.skip_ws();
        if self.peek() == Some('(') {
            self.bump();
            let args = self.parse_arg_list();
            self.skip_ws();
            assert_eq!(self.bump(), Some(')'), "expected closing ')' after {name}(...");
            make_multiarg_app(&name, &args)
        } else {
            FolTerm::Variable(name)
        }
    }
    fn parse_atom(&mut self) -> FolFormula {
        let name = self.parse_ident();
        self.skip_ws();
        let args = if self.peek() == Some('(') {
            self.bump();
            let args = self.parse_arg_list();
            self.skip_ws();
            assert_eq!(self.bump(), Some(')'), "expected closing ')' after {name}(...");
            args
        } else {
            vec![]
        };
        Predicate(name, args)
    }
    fn parse_atom_list(&mut self) -> Vec<FolFormula> {
        let mut atoms = vec![self.parse_atom()];
        loop {
            self.skip_ws();
            if self.peek() == Some(',') {
                self.bump();
                atoms.push(self.parse_atom());
            } else {
                break;
            }
        }
        atoms
    }
    fn expect_end(&mut self, context: &str) {
        self.skip_ws();
        assert!(self.peek().is_none(), "trailing input after {context}: {:?}", self.rest());
    }
}

/// Parses an `assume:` line's value: either a bare fact atom, or
/// `head :- body1, ..., bodyN` (split on the first `:-`).
fn parse_assumption(text: &str) -> FolFormula {
    match text.split_once(":-") {
        Some((head_str, body_str)) => {
            let mut head_cursor = CharCursor::new(head_str.trim());
            let head = head_cursor.parse_atom();
            head_cursor.expect_end("rule head");

            let mut body_cursor = CharCursor::new(body_str.trim());
            let body = body_cursor.parse_atom_list();
            body_cursor.expect_end("rule body");

            Arrow(Box::new(Conjunction(body)), Box::new(head))
        }
        None => {
            let mut cursor = CharCursor::new(text.trim());
            let fact = cursor.parse_atom();
            cursor.expect_end("fact");
            fact
        }
    }
}

/// Parses a `goal:` line's value: a comma-separated list of subgoals to
/// prove together (their conjunction).
fn parse_goal(text: &str) -> FolFormula {
    let mut cursor = CharCursor::new(text.trim());
    let atoms = cursor.parse_atom_list();
    cursor.expect_end("goal");
    match atoms.len() {
        1 => atoms.into_iter().next().unwrap(),
        _ => Conjunction(atoms),
    }
}

fn parse_expect(value: &str) -> bool {
    match value {
        "proved" => true,
        "failed" => false,
        other => panic!("`expect:` must be `proved` or `failed`, got {other:?}"),
    }
}

fn parse_problems(content: &str) -> Vec<Problem> {
    let mut problems = vec![];
    let mut current: Option<Problem> = None;

    for (line_no, raw_line) in content.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "---" {
            if let Some(problem) = current.take() {
                problems.push(problem);
            }
            continue;
        }

        let Some((key, value)) = line.split_once(':') else {
            panic!("malformed line {}: expected `key: value`, got {raw_line:?}", line_no + 1);
        };
        let (key, value) = (key.trim(), value.trim());

        match key {
            "name" => {
                if let Some(problem) = current.take() {
                    problems.push(problem);
                }
                current = Some(Problem {
                    name: value.to_string(),
                    constants: HashSet::new(),
                    assumptions: vec![],
                    goals: vec![],
                    expect_proved: true,
                });
            }
            "const" => {
                let problem = current
                    .as_mut()
                    .unwrap_or_else(|| panic!("`const:` before `name:` at line {}", line_no + 1));
                problem.constants.extend(value.split_whitespace().map(str::to_string));
            }
            "assume" => {
                let assumption = parse_assumption(value);
                let problem = current
                    .as_mut()
                    .unwrap_or_else(|| panic!("`assume:` before `name:` at line {}", line_no + 1));
                problem.assumptions.push(assumption);
            }
            "goal" => {
                let goal = parse_goal(value);
                let problem = current
                    .as_mut()
                    .unwrap_or_else(|| panic!("`goal:` before `name:` at line {}", line_no + 1));
                problem.goals.push(goal);
            }
            "expect" => {
                let expect_proved = parse_expect(value);
                let problem = current
                    .as_mut()
                    .unwrap_or_else(|| panic!("`expect:` before `name:` at line {}", line_no + 1));
                problem.expect_proved = expect_proved;
            }
            other => panic!("unknown directive `{other}:` at line {}", line_no + 1),
        }
    }
    if let Some(problem) = current.take() {
        problems.push(problem);
    }

    problems
}
//########################### AD HOC PROBLEM FILE PARSING

//########################### TIME & PEAK MEMORY MEASUREMENT

fn read_vmhwm_kb() -> Option<u64> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    status.lines().find_map(|line| {
        line.strip_prefix("VmHWM:")
            .and_then(|rest| rest.trim().trim_end_matches("kB").trim().parse().ok())
    })
}

/// Resets the process's peak RSS high-water mark (`VmHWM`) to its current
/// RSS, a documented Linux feature (writing "5" to `clear_refs`). Lets us
/// isolate the peak memory of a single call within one long-lived process,
/// rather than spawning a subprocess per measurement.
fn reset_peak_rss() -> bool {
    fs::write("/proc/self/clear_refs", "5").is_ok()
}

/// Runs `run` on a background thread and waits up to `timeout`. On timeout
/// the thread is abandoned (Rust has no safe thread cancellation) rather
/// than joined - fine for a one-shot benchmark process, but if a problem
/// times out its thread keeps consuming CPU/memory in the background for
/// the rest of the run, which can distort later measurements. Keep ad hoc
/// problems modest, or run one at a time, if you hit this.
fn run_with_timeout<T: Send + 'static>(
    timeout: Duration,
    run: impl FnOnce() -> T + Send + 'static,
) -> Option<T> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(run());
    });
    rx.recv_timeout(timeout).ok()
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Outcome {
    Proved,
    Failed,
    TimedOut,
}
impl Outcome {
    fn label(self) -> &'static str {
        match self {
            Outcome::Proved => "proved",
            Outcome::Failed => "failed",
            Outcome::TimedOut => "timeout",
        }
    }
    fn matches_expectation(self, expect_proved: bool) -> bool {
        match self {
            Outcome::Proved => expect_proved,
            Outcome::Failed => !expect_proved,
            Outcome::TimedOut => false,
        }
    }
}
fn outcome_of<T>(result: &Result<T, LofError>) -> Outcome {
    match result {
        Ok(_) => Outcome::Proved,
        Err(_) => Outcome::Failed,
    }
}

/// Runs `run` `repeats` times (each individually bounded by `timeout`),
/// resetting peak RSS before each run, and returns the (time, peak RSS,
/// outcome) triple from whichever run had the lowest wall-clock time. A
/// timeout counts as "infinitely slow" for picking the best run, so a
/// single successful run among several timeouts still wins.
fn measure(
    repeats: usize,
    timeout: Duration,
    mut run: impl FnMut(Duration) -> (Duration, Outcome),
) -> (Duration, Option<u64>, Outcome) {
    let supports_reset = reset_peak_rss();
    let mut best: Option<(Duration, Option<u64>, Outcome)> = None;

    for _ in 0..repeats.max(1) {
        if supports_reset {
            reset_peak_rss();
        }
        let (elapsed, outcome) = run(timeout);
        let peak_kb = if supports_reset { read_vmhwm_kb() } else { None };

        let is_better = match &best {
            None => true,
            Some((best_elapsed, _, best_outcome)) => {
                match (*best_outcome == Outcome::TimedOut, outcome == Outcome::TimedOut) {
                    (true, false) => true,
                    (false, true) => false,
                    (true, true) => false,
                    (false, false) => elapsed < *best_elapsed,
                }
            }
        };
        if is_better {
            best = Some((elapsed, peak_kb, outcome));
        }
    }

    best.expect("repeats.max(1) guarantees at least one iteration")
}
//########################### TIME & PEAK MEMORY MEASUREMENT

//########################### RUNNING BOTH PIPELINES

/// Saturation refutes `assumptions ∧ ¬(goal1 ∧ ... ∧ goalN)` as a single
/// negated-conjunction clause, so it proves exactly the same statement SLD
/// does (prove every goal together), not something subtly different.
fn run_saturation(
    assumptions: &[FolFormula],
    goals: &[FolFormula],
    constants: &HashSet<String>,
) -> Result<Substitution<SupTerm>, LofError> {
    let mut saturation_set = vec![];
    for assumption in assumptions {
        for clause in clausify(assumption, constants)? {
            saturation_set.push(standardize_apart(&clause));
        }
    }

    let combined_goal = match goals.len() {
        1 => goals[0].clone(),
        _ => Conjunction(goals.to_vec()),
    };
    for clause in clausify(&Not(Box::new(combined_goal)), constants)? {
        saturation_set.push(standardize_apart(&clause));
    }

    // mirrors this project's default ATP configuration (see config.rs)
    let selection_fn = get_selection_fn(SelectionFunction::Maximal);
    saturate(&saturation_set, &selection_fn, pick_clause_weighted)
}

fn measure_saturation(
    problem: &Problem,
    repeats: usize,
    timeout: Duration,
) -> (Duration, Option<u64>, Outcome) {
    let assumptions = problem.assumptions.clone();
    let goals = problem.goals.clone();
    let constants = problem.constants.clone();

    measure(repeats, timeout, move |timeout| {
        let assumptions = assumptions.clone();
        let goals = goals.clone();
        let constants = constants.clone();
        let start = Instant::now();
        let outcome = match run_with_timeout(timeout, move || run_saturation(&assumptions, &goals, &constants)) {
            Some(result) => outcome_of(&result),
            None => Outcome::TimedOut,
        };
        (start.elapsed(), outcome)
    })
}

fn measure_sld(problem: &Problem, repeats: usize, timeout: Duration) -> (Duration, Option<u64>, Outcome) {
    let assumptions = problem.assumptions.clone();
    let goals = problem.goals.clone();
    let constants = problem.constants.clone();

    measure(repeats, timeout, move |timeout| {
        let assumptions = assumptions.clone();
        let goals = goals.clone();
        let constants = constants.clone();
        let start = Instant::now();
        let outcome = match run_with_timeout(timeout, move || sld_solve(&assumptions, &goals, &constants)) {
            Some(result) => outcome_of(&result),
            None => Outcome::TimedOut,
        };
        (start.elapsed(), outcome)
    })
}
//########################### RUNNING BOTH PIPELINES

//########################### REPORTING

fn format_elapsed(elapsed: Duration) -> String {
    format!("{:.3} ms", elapsed.as_secs_f64() * 1000.0)
}

fn format_peak(peak_kb: Option<u64>) -> String {
    match peak_kb {
        Some(kb) => format!("{kb} KB"),
        None => "n/a".to_string(),
    }
}

struct Row {
    problem: String,
    expect_proved: bool,
    sat_outcome: Outcome,
    sat_elapsed: Duration,
    sat_peak: Option<u64>,
    sld_outcome: Outcome,
    sld_elapsed: Duration,
    sld_peak: Option<u64>,
}

fn print_report(rows: &[Row]) {
    println!(
        "\n{:<28} | {:^26} | {:^26} | {:>10}",
        "problem", "saturation", "SLD", "speedup"
    );
    println!("{:-<28}-+-{:-<26}-+-{:-<26}-+-{:->10}", "", "", "", "");
    for row in rows {
        let saturation = format!(
            "{:<7} {:>10} {:>10}",
            row.sat_outcome.label(),
            format_elapsed(row.sat_elapsed),
            format_peak(row.sat_peak)
        );
        let sld = format!(
            "{:<7} {:>10} {:>10}",
            row.sld_outcome.label(),
            format_elapsed(row.sld_elapsed),
            format_peak(row.sld_peak)
        );
        let speedup = if row.sat_outcome != Outcome::TimedOut
            && row.sld_outcome != Outcome::TimedOut
            && row.sld_elapsed.as_secs_f64() > 0.0
        {
            format!("{:.2}x", row.sat_elapsed.as_secs_f64() / row.sld_elapsed.as_secs_f64())
        } else {
            "n/a".to_string()
        };
        println!("{:<28} | {:<26} | {:<26} | {:>10}", row.problem, saturation, sld, speedup);
    }
    println!("(speedup = saturation time / SLD time; >1x means SLD was faster on this problem)");

    let sld_off: Vec<_> = rows.iter().filter(|r| !r.sld_outcome.matches_expectation(r.expect_proved)).collect();
    let sat_off: Vec<_> = rows.iter().filter(|r| !r.sat_outcome.matches_expectation(r.expect_proved)).collect();
    if !sld_off.is_empty() {
        println!(
            "\nSLD disagreed with the expected answer on: {}. SLD is meant to be complete for \
            this Horn fragment, so this likely points to an actual bug - worth investigating.",
            sld_off.iter().map(|r| r.problem.as_str()).collect::<Vec<_>>().join(", ")
        );
    }
    if !sat_off.is_empty() {
        println!(
            "\nSaturation disagreed with the expected answer on: {}. See this file's header \
            comment: this can be an inherent difference (eg confirming satisfiability by \
            exhausting the search queue is undecidable in general, so saturation can time out \
            where SLD's goal-directed search doesn't) rather than necessarily a bug in either \
            pipeline - but if a *provable* goal was missed (not just a timeout on an unprovable \
            one), that's worth a closer look.",
            sat_off.iter().map(|r| r.problem.as_str()).collect::<Vec<_>>().join(", ")
        );
    }
}
//########################### REPORTING

#[test]
#[ignore = "development benchmark, not a correctness check: cargo test --release sld_vs_saturation_benchmark -- --ignored --nocapture"]
fn sld_vs_saturation_benchmark() {
    let path = std::env::var("SLD_BENCH_PROBLEMS_FILE").unwrap_or_else(|_| {
        format!("{}/benches/sld_vs_saturation_problems.txt", env!("CARGO_MANIFEST_DIR"))
    });
    let content = fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("couldn't read problems file {path:?}: {err}"));
    let problems = parse_problems(&content);
    assert!(!problems.is_empty(), "problems file {path:?} defines no problems");

    let repeats: usize = std::env::var("SLD_BENCH_REPEATS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5);
    let timeout = Duration::from_secs(
        std::env::var("SLD_BENCH_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(2),
    );

    if !reset_peak_rss() {
        println!(
            "note: this OS/sandbox doesn't support resetting peak RSS via /proc/self/clear_refs; peak memory will show as n/a"
        );
    }

    let rows: Vec<Row> = problems
        .iter()
        .map(|problem| {
            let (sat_elapsed, sat_peak, sat_outcome) = measure_saturation(problem, repeats, timeout);
            let (sld_elapsed, sld_peak, sld_outcome) = measure_sld(problem, repeats, timeout);
            Row {
                problem: problem.name.clone(),
                expect_proved: problem.expect_proved,
                sat_outcome,
                sat_elapsed,
                sat_peak,
                sld_outcome,
                sld_elapsed,
                sld_peak,
            }
        })
        .collect();

    print_report(&rows);

    assert!(
        rows.iter().all(|r| r.sld_outcome.matches_expectation(r.expect_proved)),
        "SLD disagreed with a problem's `expect:` directive - since SLD is meant to be complete \
        for this Horn fragment, that's a real bug, not an expected gap (see the printed report above)"
    );
}

mod parser_unit_tests {
    use super::*;

    #[test]
    fn test_parse_fact_and_rule() {
        let fact = parse_assumption("parent(tom, bob)");
        assert_eq!(fact, Predicate("parent".to_string(), vec![
            FolTerm::Variable("tom".to_string()),
            FolTerm::Variable("bob".to_string()),
        ]));

        let rule = parse_assumption("grandparent(x, z) :- parent(x, y), parent(y, z)");
        assert_eq!(
            rule,
            Arrow(
                Box::new(Conjunction(vec![
                    Predicate("parent".to_string(), vec![FolTerm::Variable("x".to_string()), FolTerm::Variable("y".to_string())]),
                    Predicate("parent".to_string(), vec![FolTerm::Variable("y".to_string()), FolTerm::Variable("z".to_string())]),
                ])),
                Box::new(Predicate("grandparent".to_string(), vec![FolTerm::Variable("x".to_string()), FolTerm::Variable("z".to_string())])),
            )
        );
    }

    #[test]
    fn test_parse_nested_terms_and_goal_conjunction() {
        let goal = parse_goal("add(s(zero), x, r), add(r, x, w)");
        assert_eq!(
            goal,
            Conjunction(vec![
                Predicate("add".to_string(), vec![
                    make_multiarg_app("s", &[FolTerm::Variable("zero".to_string())]),
                    FolTerm::Variable("x".to_string()),
                    FolTerm::Variable("r".to_string()),
                ]),
                Predicate("add".to_string(), vec![
                    FolTerm::Variable("r".to_string()),
                    FolTerm::Variable("x".to_string()),
                    FolTerm::Variable("w".to_string()),
                ]),
            ])
        );
    }

    #[test]
    fn test_parse_problems_splits_blocks_and_collects_directives() {
        let content = "\
# a comment
name: p1
const: a b
assume: p(a)
goal: p(a)
---
name: p2
assume: q(x)
goal: q(y)
expect: failed
";
        let problems = parse_problems(content);
        assert_eq!(problems.len(), 2, "expected 2 problem blocks");
        assert_eq!(problems[0].name, "p1");
        assert_eq!(problems[0].constants, HashSet::from(["a".to_string(), "b".to_string()]));
        assert_eq!(problems[0].assumptions.len(), 1);
        assert_eq!(problems[0].goals.len(), 1);
        assert!(problems[0].expect_proved, "expect defaults to `proved` when omitted");
        assert_eq!(problems[1].name, "p2");
        assert!(problems[1].constants.is_empty());
        assert!(!problems[1].expect_proved);
    }

    /// Not `#[ignore]`d: this is a cheap, fast correctness check (SLD only,
    /// no saturation - see this file's header comment for why) that the
    /// shipped default problems file stays parseable and that SLD's answer
    /// matches each problem's `expect:` directive.
    #[test]
    fn test_default_problems_file_matches_sld() {
        let path = format!(
            "{}/benches/sld_vs_saturation_problems.txt",
            env!("CARGO_MANIFEST_DIR")
        );
        let content = fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("couldn't read problems file {path:?}: {err}"));
        let problems = parse_problems(&content);
        assert!(!problems.is_empty(), "the shipped problems file should define at least one problem");

        for problem in &problems {
            let sld = sld_solve(&problem.assumptions, &problem.goals, &problem.constants);
            assert_eq!(
                sld.is_ok(),
                problem.expect_proved,
                "problem {:?}: SLD returned {:?}, but `expect:` says it should be {}",
                problem.name,
                sld,
                if problem.expect_proved { "proved" } else { "failed" }
            );
        }
    }
}
