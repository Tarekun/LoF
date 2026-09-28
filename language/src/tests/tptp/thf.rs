#[cfg(test)]
mod unit_tests {
    use crate::{
        error::LofError,
        tptp::{
            problem::{parse_tptp, TptpFormula},
            thf::{thf_formula, thf_type, thf_type_declaration},
        },
        type_theory::grammars::f::{
            FTerm::{
                self, Abstraction, Application, TypeAbstraction,
                TypeApplication, Variable,
            },
            FType::{self, Arrow, Atomic, Forall, MetaVariable},
        },
    };

    fn var(name: &str) -> FTerm {
        Variable(name.to_string())
    }
    fn ty(name: &str) -> FType {
        Atomic(name.to_string())
    }
    fn kind() -> FType {
        ty("*")
    }
    fn arrow(domain: FType, codomain: FType) -> FType {
        Arrow(Box::new(domain), Box::new(codomain))
    }
    fn app(fun: FTerm, args: Vec<FTerm>) -> FTerm {
        args.into_iter()
            .fold(fun, |fun, arg| Application(Box::new(fun), Box::new(arg)))
    }
    fn type_app(fun: FTerm, type_arg: FType) -> FTerm {
        TypeApplication(Box::new(fun), type_arg)
    }
    fn lambda(var_name: &str, var_type: FType, body: FTerm) -> FTerm {
        Abstraction(var_name.to_string(), var_type, Box::new(body))
    }
    fn hole() -> FType {
        MetaVariable("?".to_string())
    }

    /// Parses `input` expecting it to be entirely consumed
    fn parse(input: &str) -> Result<FTerm, LofError> {
        match thf_formula(input) {
            Ok(("", term)) => Ok(term),
            Ok((rest, _)) => {
                Err(LofError::custom(format!("leftover: {}", rest)))
            }
            Err(err) => Err(err.into()),
        }
    }

    #[test]
    fn test_types() {
        let (i, o) = (ty("$i"), ty("$o"));
        assert_eq!(
            thf_type("$i > $i > $o"),
            Ok(("", arrow(i.clone(), arrow(i.clone(), o.clone())))),
            "Mapping types arent right associative"
        );
        assert_eq!(
            thf_type("($i > $o) > $o"),
            Ok(("", arrow(arrow(i.clone(), o.clone()), o.clone())))
        );
        assert_eq!(
            thf_type("!>[A: $tType, B]: (A > B)"),
            Ok((
                "",
                Forall(
                    "A".to_string(),
                    Box::new(kind()),
                    Box::new(Forall(
                        "B".to_string(),
                        Box::new(kind()),
                        Box::new(arrow(ty("A"), ty("B")))
                    ))
                )
            )),
            "Polymorphic types arent parsed to nested Foralls"
        );
        assert_eq!(thf_type("$tType"), Ok(("", kind())));
    }

    #[test]
    fn test_type_declarations() {
        assert_eq!(
            thf_type_declaration("nat: $tType"),
            Ok(("", ("nat".to_string(), kind())))
        );
        assert_eq!(
            thf_type_declaration("( succ: nat > nat )"),
            Ok(("", ("succ".to_string(), arrow(ty("nat"), ty("nat")))))
        );
        assert!(
            thf_type_declaration("list: $tType > $tType").is_err(),
            "Type constructors are accepted without System Fω"
        );
        assert!(
            thf_type_declaration("t: !>[F: $tType > $tType]: $o").is_err(),
            "Higher kinded type variables are accepted"
        );
    }

    #[test]
    fn test_application() {
        assert_eq!(
            parse("f @ X @ a"),
            Ok(app(var("f"), vec![var("X"), var("a")])),
            "Application isnt left associative"
        );
        assert_eq!(
            parse("f @ ($i > $o)"),
            Ok(type_app(var("f"), arrow(ty("$i"), ty("$o")))),
            "Compound types arent parsed as type arguments"
        );
        assert!(
            parse("p @ q & r").is_err(),
            "Application mixed with connectives without parentheses is accepted"
        );
    }

    #[test]
    fn test_connectives() {
        let (p, q, r) = (var("p"), var("q"), var("r"));
        let not = |φ: FTerm| app(var("~"), vec![φ]);

        assert_eq!(
            parse("p & q & r"),
            Ok(app(
                var("&"),
                vec![app(var("&"), vec![p.clone(), q.clone()]), r.clone()]
            ))
        );
        assert_eq!(
            parse("p <= q"),
            Ok(app(var("=>"), vec![q.clone(), p.clone()]))
        );
        assert_eq!(
            parse("p ~| q"),
            Ok(not(app(var("|"), vec![p.clone(), q.clone()])))
        );
        assert_eq!(parse("~ p"), Ok(not(p.clone())));
        assert_eq!(
            parse("(&) @ p @ q"),
            Ok(app(var("&"), vec![p.clone(), q.clone()])),
            "Connectives used as terms arent parsed"
        );
        assert!(parse("p & q | r").is_err());
    }

    #[test]
    fn test_equality_and_binders() {
        assert_eq!(
            parse("a != b"),
            Ok(app(
                var("~"),
                vec![app(type_app(var("="), hole()), vec![var("a"), var("b")])]
            )),
            "Equality isnt encoded as the polymorphic `=` with an implicit type"
        );
        assert_eq!(
            parse("![X: $i, Y]: (r @ X @ Y)"),
            Ok(app(
                type_app(var("!!"), ty("$i")),
                vec![lambda(
                    "X",
                    ty("$i"),
                    app(
                        type_app(var("!!"), ty("$i")),
                        vec![lambda(
                            "Y",
                            ty("$i"),
                            app(var("r"), vec![var("X"), var("Y")])
                        )]
                    )
                )]
            )),
            "Universal quantification isnt encoded as `!!` of a λ"
        );
        assert_eq!(
            parse("?[X: nat]: (p @ X)"),
            Ok(app(
                type_app(var("??"), ty("nat")),
                vec![lambda("X", ty("nat"), app(var("p"), vec![var("X")]))]
            ))
        );
        assert_eq!(parse("^[X: $i]: X"), Ok(lambda("X", ty("$i"), var("X"))));
        assert_eq!(
            parse("!>[A: $tType]: (p @ A)"),
            Ok(TypeAbstraction(
                "A".to_string(),
                Box::new(kind()),
                Box::new(app(var("p"), vec![var("A")]))
            ))
        );
        assert!(
            parse("![A: $tType]: p").is_err(),
            "Type variables are accepted in term binders"
        );
        assert!(parse("@+[X: $i]: p @ X").is_err());
    }

    const PEANO: &str = "
        thf(nat_type, type, nat: $tType).
        thf(zero_decl, type, zero: nat).
        thf(succ_decl, type, succ: nat > nat).
        thf(even_decl, type, even: nat > $o).
        thf(id_decl, type, id: !>[A: $tType]: (A > A)).
        thf(zero_even, axiom, even @ zero).
        thf(succ_succ, axiom,
            ![X: nat]: ((even @ X) => (even @ (succ @ (succ @ X))))).
        thf(beta, axiom, (^[X: nat]: (even @ X)) @ zero).
        thf(id_zero, axiom, (id @ nat @ zero) = zero).
        thf(induction, axiom,
            ![P: nat > $o]: ((P @ zero) => (?[X: nat]: (P @ X)))).
        thf(functions, axiom, succ = succ).
        thf(bare_pi, axiom, !! @ even).
        thf(reflexivity, axiom, !>[A: $tType]: ![X: A]: (X = X)).
        thf(goal, conjecture, even @ (succ @ (succ @ zero))).";

    #[test]
    fn test_annotated_thf() {
        let problem = parse_tptp(PEANO).unwrap();
        assert_eq!(
            problem.inputs[2].formula,
            TptpFormula::ThfDeclaration(
                "succ".to_string(),
                arrow(ty("nat"), ty("nat"))
            )
        );
        assert!(matches!(problem.inputs[5].formula, TptpFormula::Thf(_)));
        assert!(problem.to_clauses().is_err(), "THF problems are clausified");
    }

    #[test]
    fn test_type_check() {
        let (_, formulas) = parse_tptp(PEANO)
            .unwrap()
            .type_check_thf()
            .expect("A well typed THF problem doesnt type check");
        let formula = |name: &str| {
            formulas
                .iter()
                .find(|(formula_name, _)| formula_name == name)
                .map(|(_, term)| term.clone())
                .unwrap()
        };

        assert_eq!(
            formula("id_zero"),
            app(
                type_app(var("="), ty("nat")),
                vec![
                    app(type_app(var("id"), ty("nat")), vec![var("zero")]),
                    var("zero")
                ]
            ),
            "Elaboration doesnt resolve type arguments and equality's type"
        );
        assert_eq!(
            formula("functions"),
            app(
                type_app(var("="), arrow(ty("nat"), ty("nat"))),
                vec![var("succ"), var("succ")]
            ),
            "Equality between functions isnt instantiated at the function type"
        );
        assert_eq!(
            formula("bare_pi"),
            app(type_app(var("!!"), ty("nat")), vec![var("even")]),
            "Bare `!!` isnt instantiated with the domain of its argument"
        );
    }

    #[test]
    fn test_ill_typed() {
        let ill_typed = [
            // predicate applied to a predicate
            "thf(bad, axiom, even @ even).",
            // equality between different types
            "thf(bad, axiom, even = zero).",
            // a term that isnt a formula
            "thf(bad, axiom, succ @ zero).",
            // undeclared constant
            "thf(bad, axiom, odd @ zero).",
            // binder over an undeclared type
            "thf(bad, axiom, ![X: foo]: (even @ zero)).",
            // type argument that cant be determined
            "thf(bad, axiom, (=) = (=)).",
            // declaration over an undeclared type
            "thf(bad, type, f: foo > $o).",
        ];
        for bad in ill_typed {
            let problem = parse_tptp(&format!("{}\n{}", PEANO, bad)).unwrap();
            assert!(
                problem.type_check_thf().is_err(),
                "Ill typed input `{}` type checks",
                bad
            );
        }
    }
}
