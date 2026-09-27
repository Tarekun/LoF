#[cfg(test)]
mod unit_tests {
    use crate::{
        config::SelectionFunction,
        tptp::{
            problem::{parse_tptp, TptpFormula},
            tff::{type_declaration, TypeDeclaration},
        },
        type_theory::{
            grammars::fol::FolFormula::{self, Arrow, Predicate},
            sup::{
                freedom::{get_selection_fn, pick_clause},
                saturation::saturate,
            },
        },
    };

    fn sort(name: &str) -> FolFormula {
        Predicate(name.to_string(), vec![])
    }
    fn arrow(domain: FolFormula, codomain: FolFormula) -> FolFormula {
        Arrow(Box::new(domain), Box::new(codomain))
    }
    fn symbol(name: &str, args: &[&str], result: &str) -> TypeDeclaration {
        TypeDeclaration::Symbol(
            name.to_string(),
            args.iter().map(|arg| arg.to_string()).collect(),
            result.to_string(),
        )
    }

    const PEANO: &str = "
        tff(nat_type, type, nat: $tType).
        tff(zero_decl, type, zero: nat).
        tff(succ_decl, type, succ: nat > nat).
        tff(plus_decl, type, plus: (nat * nat) > nat).
        tff(even_decl, type, even: nat > $o).
        tff(zero_even, axiom, even(zero)).
        tff(succ_succ, axiom, ![X: nat]: (even(X) => even(succ(succ(X))))).
        tff(plus_zero, axiom, ![X: nat]: plus(zero, X) = X).
        tff(goal, conjecture, ?[Y: nat]: even(succ(succ(Y)))).";

    #[test]
    fn test_type_declarations() {
        assert_eq!(
            type_declaration("nat: $tType"),
            Ok(("", TypeDeclaration::Sort("nat".to_string())))
        );
        assert_eq!(
            type_declaration("zero: nat"),
            Ok(("", symbol("zero", &[], "nat")))
        );
        assert_eq!(
            type_declaration("( succ: ( nat > nat ) )"),
            Ok(("", symbol("succ", &["nat"], "nat"))),
            "TFF parser doesnt handle parenthesized declarations and types"
        );
        assert_eq!(
            type_declaration("plus: (nat * nat) > nat"),
            Ok(("", symbol("plus", &["nat", "nat"], "nat"))),
            "TFF parser doesnt handle product argument types"
        );
        assert_eq!(
            type_declaration("even: nat > $o"),
            Ok(("", symbol("even", &["nat"], "$o")))
        );
        assert_eq!(type_declaration("p: $o"), Ok(("", symbol("p", &[], "$o"))));
        assert!(
            type_declaration("list: $tType > $tType").is_err(),
            "TFF parser accepts type constructors (TF1)"
        );
        assert!(
            type_declaration("id: !>[A: $tType]: (A > A)").is_err(),
            "TFF parser accepts polymorphic types (TF1)"
        );
    }

    #[test]
    fn test_annotated_tff() {
        let problem = parse_tptp(PEANO).unwrap();
        assert_eq!(
            problem.inputs[2].formula,
            TptpFormula::Declaration(symbol("succ", &["nat"], "nat"))
        );
        assert!(matches!(problem.inputs[6].formula, TptpFormula::Fol(_, _)));
    }

    #[test]
    fn test_environment() {
        let nat = sort("nat");
        let environment = parse_tptp(PEANO).unwrap().environment().unwrap();

        assert_eq!(
            environment.get_predicate("nat"),
            Some(vec![]),
            "Declared sorts arent registered as nullary predicates"
        );
        assert_eq!(environment.get_variable_type("zero"), Some(nat.clone()));
        assert_eq!(
            environment.get_variable_type("plus"),
            Some(arrow(nat.clone(), arrow(nat.clone(), nat.clone()))),
            "Declared functions arent given their curried type"
        );
        assert_eq!(
            environment.get_predicate("even"),
            Some(vec![nat.clone()]),
            "Declared predicates arent registered with their argument sorts"
        );
    }

    #[test]
    fn test_default_types() {
        let i = sort("$i");
        let environment = parse_tptp(
            "fof(a, axiom, ![X]: (p(f(X), c) | q(3) | r(1/2, 2.5))).",
        )
        .unwrap()
        .environment()
        .unwrap();

        assert_eq!(
            environment.get_variable_type("f"),
            Some(arrow(i.clone(), i.clone())),
            "Undeclared functions dont default to $i types"
        );
        assert_eq!(environment.get_variable_type("c"), Some(i.clone()));
        assert_eq!(
            environment.get_predicate("p"),
            Some(vec![i.clone(), i.clone()]),
            "Undeclared predicates dont default to $i arguments"
        );
        assert_eq!(environment.get_variable_type("3"), Some(sort("$int")));
        assert_eq!(environment.get_variable_type("1/2"), Some(sort("$rat")));
        assert_eq!(environment.get_variable_type("2.5"), Some(sort("$real")));
    }

    #[test]
    fn test_invalid_signatures() {
        assert!(
            parse_tptp("tff(f, type, f: foo > $i).")
                .unwrap()
                .environment()
                .is_err(),
            "Declarations over undeclared sorts are accepted"
        );
        assert!(
            parse_tptp("tff(f1, type, f: $i > $i). tff(f2, type, f: $i).")
                .unwrap()
                .environment()
                .is_err(),
            "Conflicting declarations are accepted"
        );
        assert!(
            parse_tptp("tff(a, axiom, $less(1, 2)).")
                .unwrap()
                .environment()
                .is_err(),
            "Interpreted arithmetic symbols are accepted"
        );
    }

    #[test]
    fn test_type_check() {
        assert!(
            parse_tptp(PEANO).unwrap().type_check().is_ok(),
            "A well typed TFF problem doesnt type check"
        );
        assert!(
            parse_tptp("fof(a, axiom, ![X]: (p(X) => ?[Y]: q(f(X), Y))).")
                .unwrap()
                .type_check()
                .is_ok(),
            "An untyped FOF problem doesnt type check with default types"
        );

        let ill_typed = [
            // predicate over nat applied to an individual
            "tff(bad, axiom, ![X: $i]: even(X)).",
            // equality between different sorts
            "tff(bad, axiom, ![X: nat]: X = c).",
            // function applied to too many arguments
            "tff(bad, axiom, even(succ(zero, zero))).",
            // binder over an undeclared sort
            "tff(bad, axiom, ![X: foo]: even(zero)).",
        ];
        for bad in ill_typed {
            let problem = parse_tptp(&format!("{}\n{}", PEANO, bad)).unwrap();
            assert!(
                problem.type_check().is_err(),
                "Ill typed formula `{}` type checks",
                bad
            );
        }
    }

    #[test]
    fn test_tff_refutation() {
        let clauses = parse_tptp(PEANO).unwrap().to_clauses().unwrap();
        let selection_fn = get_selection_fn(SelectionFunction::Maximal);
        assert!(
            saturate(&clauses, &selection_fn, pick_clause).is_ok(),
            "SUP cant refute a clausified TFF problem"
        );
    }
}
