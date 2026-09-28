use super::{sld_prove_all, sld_prove_first, to_horn_clause};
use crate::type_theory::grammars::cnf::{
    CnfFormula::{self, Atom, Clause, Equality, Not},
    CnfTerm::{self, Application, Variable},
};

//########################### TEST HELPERS
fn v(name: &str) -> CnfTerm {
    Variable(name.to_string())
}
fn c(name: &str, args: &[CnfTerm]) -> CnfTerm {
    Application(name.to_string(), args.to_vec())
}
fn p(name: &str, args: &[CnfTerm]) -> CnfFormula {
    Atom(name.to_string(), args.to_vec())
}
/// A fact is just its head, a rule is `head ∨ ¬body1 ∨ ... ∨ ¬bodyN`
fn rule(head: CnfFormula, body: Vec<CnfFormula>) -> CnfFormula {
    if body.is_empty() {
        head
    } else {
        let mut literals = vec![head];
        literals.extend(body.into_iter().map(|atom| Not(Box::new(atom))));
        Clause(literals)
    }
}
//########################### TEST HELPERS

#[test]
fn test_to_horn_clause_accepts_facts_and_rules() {
    let p = Atom("p".to_string(), vec![]);
    let q = Atom("q".to_string(), vec![]);

    let fact =
        to_horn_clause(&p).expect("a bare atom is a valid (fact) Horn clause");
    assert_eq!(fact.head, p);
    assert!(fact.body.is_empty());

    let rule_clause = Clause(vec![p.clone(), Not(Box::new(q.clone()))]);
    let rule = to_horn_clause(&rule_clause)
        .expect("one positive + one negative literal is a valid Horn clause");
    assert_eq!(rule.head, p);
    assert_eq!(rule.body, vec![q]);
}

#[test]
fn test_to_horn_clause_rejects_non_horn_and_headless_clauses() {
    let p = Atom("p".to_string(), vec![]);
    let q = Atom("q".to_string(), vec![]);

    let two_positive = Clause(vec![p.clone(), q.clone()]);
    assert!(
        to_horn_clause(&two_positive).is_err(),
        "a clause with 2 positive literals isn't a Horn clause"
    );

    let headless =
        Clause(vec![Not(Box::new(p.clone())), Not(Box::new(q.clone()))]);
    assert!(
        to_horn_clause(&headless).is_err(),
        "SLD program clauses need exactly one positive literal (a head)"
    );

    let with_equality = Equality(v("x"), v("y"));
    assert!(
        to_horn_clause(&with_equality).is_err(),
        "equality literals aren't supported by this SLD implementation"
    );
}

#[test]
fn test_sld_rejects_non_horn_program() {
    let x = v("x");
    let not_horn = Clause(vec![p("P", &[x.clone()]), p("Q", &[x])]);

    assert!(
        sld_prove_first(&[not_horn], &[p("P", &[v("y")])]).is_err(),
        "a disjunction of two positive predicates isn't a Horn clause and should be rejected"
    );
}

#[test]
fn test_sld_rejects_non_atomic_goal() {
    let goal = Not(Box::new(p("P", &[v("x")])));

    assert!(
        sld_prove_first(&[], &[goal]).is_err(),
        "SLD goals must be plain atoms; a negated goal should be rejected"
    );
}

#[test]
fn test_sld_backtracks_across_failing_facts() {
    // likes(mary, wine).
    // likes(mary, cheese).
    // ?- likes(mary, cheese).
    let program = vec![
        rule(p("likes", &[c("mary", &[]), c("wine", &[])]), vec![]),
        rule(p("likes", &[c("mary", &[]), c("cheese", &[])]), vec![]),
    ];
    let goals = vec![p("likes", &[c("mary", &[]), c("cheese", &[])])];

    assert!(
        sld_prove_first(&program, &goals).is_ok(),
        "SLD should backtrack past the first non-unifying fact and succeed on the second"
    );
}

#[test]
fn test_sld_solves_for_free_variable() {
    // parent(tom, bob).
    // ?- parent(tom, X).
    let program =
        vec![rule(p("parent", &[c("tom", &[]), c("bob", &[])]), vec![])];
    let goals = vec![p("parent", &[c("tom", &[]), v("X")])];

    let solution = sld_prove_first(&program, &goals).expect(
        "parent(tom,bob) should let SLD solve parent(tom,X) with X=bob",
    );
    assert_eq!(solution.resolvent("X"), Some(&c("bob", &[])));
}

#[test]
fn test_sld_fails_when_goal_isnt_entailed() {
    // likes(john, wine).
    // ?- likes(mary, X).
    let program =
        vec![rule(p("likes", &[c("john", &[]), c("wine", &[])]), vec![])];
    let goals = vec![p("likes", &[c("mary", &[]), v("X")])];

    assert!(
        sld_prove_first(&program, &goals).is_err(),
        "SLD shouldn't find a proof for a goal that isn't entailed by the program"
    );
}

#[test]
fn test_sld_recursive_rule_arithmetic() {
    // add(zero, x, x).
    // add(s(n), m, s(p)) :- add(n, m, p).
    // ?- add(s(s(zero)), s(zero), R).
    let zero = || c("zero", &[]);
    let s = |t: CnfTerm| c("s", &[t]);

    let program = vec![
        rule(p("add", &[zero(), v("x"), v("x")]), vec![]),
        rule(
            p("add", &[s(v("n")), v("m"), s(v("p"))]),
            vec![p("add", &[v("n"), v("m"), v("p")])],
        ),
    ];
    let goals = vec![p("add", &[s(s(zero())), s(zero()), v("R")])];

    let solution = sld_prove_first(&program, &goals)
        .expect("SLD should derive 2+1=3 from the Peano add rules");
    assert_eq!(solution.resolvent("R"), Some(&s(s(s(zero())))));
}

#[test]
fn test_sld_finds_all_solutions_via_backtracking() {
    // member(x, cons(x, rest)).
    // member(x, cons(first, rest)) :- member(x, rest).
    // ?- member(X, cons(a, cons(b, cons(c, nil)))).
    let nil = || c("nil", &[]);
    let cons = |h: CnfTerm, t: CnfTerm| c("cons", &[h, t]);

    let list = cons(c("a", &[]), cons(c("b", &[]), cons(c("c", &[]), nil())));

    let program = vec![
        rule(p("member", &[v("x"), cons(v("x"), v("rest"))]), vec![]),
        rule(
            p("member", &[v("x"), cons(v("first"), v("rest"))]),
            vec![p("member", &[v("x"), v("rest")])],
        ),
    ];
    let goals = vec![p("member", &[v("X"), list])];

    let solutions = sld_prove_all(&program, &goals)
        .expect("SLD should find every member of the list");

    let found: Vec<_> = solutions
        .iter()
        .map(|subst| subst.resolvent("X").cloned())
        .collect();
    assert_eq!(
        found,
        vec![Some(c("a", &[])), Some(c("b", &[])), Some(c("c", &[]))],
        "SLD should backtrack through both member clauses to enumerate every list element"
    );
}
