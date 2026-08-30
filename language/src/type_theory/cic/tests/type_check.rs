#[cfg(test)]
mod tests {
    use crate::type_theory::{cic::{
        cic::{
            Cic, CicStm::{Fun, InductiveDef}, CicTerm::{self, Abstraction, Application, Let, Match, Meta, Product, Sort, Variable}, GLOBAL_INDEX, PLACEHOLDER_DBI
        }, evaluation::evaluate_inductive, type_check::{inductive_eliminator, type_check_inductive}
    }, environment::Environment};
    use crate::type_theory::interface::Kernel;
    use crate::type_theory::interface::TypeTheory;

    fn var(name: &str) -> CicTerm {
        Variable(name.to_string(), PLACEHOLDER_DBI)
    }
    fn vardbi(name: &str, dbi: i32) -> CicTerm {
        Variable(name.to_string(), dbi)
    }
    fn app(fun_name: &str, mut args: Vec<CicTerm>) -> CicTerm {
        if args.len() == 0 {
            var(fun_name)
        } else {
            let last_arg = args.pop().unwrap();
            let partially_applied = app(fun_name, args);
            Application(
                Box::new(partially_applied),
                Box::new(last_arg.clone()),
            )
        }
    }
    fn packed_env() -> Environment<Cic>{
        let mut test_env = Cic::default_environment();
        let boolean = Variable("Bool".to_string(), GLOBAL_INDEX);
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let list = Variable("List".to_string(), GLOBAL_INDEX);
        let type_var = Variable("T".to_string(), GLOBAL_INDEX);

        let _ = evaluate_inductive(
            &mut test_env,
            "List",
            &vec![("T".to_string(), Sort("TYPE".to_string()))],
            &Sort("TYPE".to_string()),
            &vec![
                ("nil".to_string(), Application(
                    Box::new(list.clone()), 
                    Box::new(type_var.clone())
                )),
                ("cons".to_string(), Product(
                    "e".to_string(), 
                    Box::new(type_var.clone()), 
                    Box::new(Product(
                        "l".to_string(), 
                        Box::new(Application(
                            Box::new(list.clone()), 
                            Box::new(type_var.clone())
                        )), 
                        Box::new(Application(
                            Box::new(list.clone()), 
                            Box::new(type_var.clone())
                        ))
                    ))
                ))
            ],
        );
        let _ = evaluate_inductive(
            &mut test_env,
            "Bool",
            &vec![],
            &Sort("TYPE".to_string()),
            &vec![
                ("true".to_string(), boolean.clone()),
                ("false".to_string(), boolean.clone()),
            ],
        );
        let _ = evaluate_inductive(
            &mut test_env,
            "Nat",
            &vec![],
            &Sort("TYPE".to_string()),
            &vec![
                ("0".to_string(), nat.clone()),
                ("s".to_string(), Product(
                    "_".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ))
            ],
        );

        return test_env;
    }

    #[test]
    fn test_type_check_sort_n_vars() {
        let nat = Variable("nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env
            .add_to_context("nat", &Sort("TYPE".to_string()));
        // assumption, the type statement is included in the context
        test_env.add_to_context(
            "n",
            &nat,
        );
        // definition, we have the variabled and a typed body
        test_env.add_substitution_with_type(
            "m",
            &Variable("n".to_string(), GLOBAL_INDEX),
            &nat,
        );

        // sorts
        assert_eq!(
            Cic::type_check_term(
                &Sort("TYPE".to_string()),
                &mut test_env
            )
            .unwrap(),
            Sort("TYPE".to_string()),
            "Sort 'TYPE' type checking failed"
        );
        assert!(
            Cic::type_check_term(
                &Sort("PROP".to_string()),
                &mut test_env
            )
            .is_ok(),
            "Sort 'PROP' type checking failed"
        );
        assert!(
            Cic::type_check_term(
                &Sort("StupidInvalidSort".to_string()),
                &mut test_env
            )
            .is_err(),
            "Sort type checker accepts illegal sort"
        );
        assert!(
            Cic::type_check_term(
                &Variable("TYPE".to_string(), GLOBAL_INDEX),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses sorts when used as variables"
        );

        // variables
        assert_eq!(
            Cic::type_check_term(
                &Variable("n".to_string(), GLOBAL_INDEX),
                &mut test_env
            )
            .unwrap(),
            nat.clone(),
            "Type checker refuses existing variable"
        );
        assert!(
            Cic::type_check_term(
                &Variable("m".to_string(), GLOBAL_INDEX),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses defined variable"
        );
        assert!(
            Cic::type_check_term(
                &Sort("stupidInvalidVar".to_string()),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts unbound variable"
        );
    }

    #[test]
    fn test_type_check_abstraction() {
        let nat = Variable("nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env
            .add_to_context("nat", &Sort("TYPE".to_string()));
        // assumption, the type statement is included in the context
        test_env.add_to_context(
            "o",
            &nat,
        );
        // function over nat
        test_env.add_to_context(
            "s",
            &Product(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );

        assert_eq!(
            Cic::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Variable("x".to_string(), 0)),
                ),
                &mut test_env
            )
            .unwrap(),
            Product(
                "x".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone())
            ),
            "Type checker refuses simple identity function"
        );
        assert_eq!(
            test_env.get_from_context("x"),
            None,
            "Abstraction type checker stains context with local variable"
        );
        assert!(
            Cic::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Application(
                        Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                        Box::new(Variable("x".to_string(), 0)),
                    )),
                ),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses function with more complex body"
        );
        assert!(
            Cic::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(Variable(
                        "StupidInvalidType".to_string(), GLOBAL_INDEX
                    )),
                    Box::new(Variable("x".to_string(), 0)),
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts function defined over non existant type"
        );
    }

    #[test]
    fn test_type_check_product() {
        let mut test_env = Cic::default_environment();
        // polymorphic type constructor
        test_env.add_to_context(
            "list",
            &Product(
                "T".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Sort("TYPE".to_string())),
            ),
        );

        assert_eq!(
            Cic::type_check_term(
                &Product(
                    "T".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable("T".to_string(), 0)),
                ),
                &mut test_env
            )
            .unwrap(),
            Sort("TYPE".to_string()),
            "Type checker refuses simple polymorphic identity type"
        );
        assert_eq!(
            test_env.get_from_context("T"),
            None,
            "Product type checker stains context with local variable"
        );
        assert!(
            Cic::type_check_term(
                &Product(
                    "T".to_string(),
                    Box::new(Sort("StupidInvalidSort".to_string())),
                    Box::new(Variable("T".to_string(), 0)),
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts polymorphic type over illegal sort"
        );
        assert!(
            Cic::type_check_term(
                &Product(
                    "T".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Application(
                        Box::new(Variable("list".to_string(), GLOBAL_INDEX)),
                        Box::new(Variable("T".to_string(), 0))
                    ))
                ),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses polymorphic types with more complex bodies"
        );
    }

    #[test]
    fn test_type_check_application() {
        let nat = Variable("nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env
            .add_to_context("nat", &Sort("TYPE".to_string()));
        // assumption, the type statement is included in the context
        test_env.add_to_context(
            "n",
            &nat,
        );
        // definition, we have the variabled and a typed body
        test_env.add_substitution_with_type(
            "m",
            &Variable("n".to_string(), GLOBAL_INDEX),
            &nat.clone(),
        );
        // function over nat
        test_env.add_to_context(
            "s",
            &Product(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );

        assert_eq!(
            Cic::type_check_term(
                &Application(
                    Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                    Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
                ),
                &mut test_env
            )
            .unwrap(),
            nat.clone(),
            "Type checker refuses function application over nat"
        );
        assert!(
            Cic::type_check_term(
                &Application(
                    Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                    Box::new(Variable("m".to_string(), GLOBAL_INDEX)),
                ),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses function application over a variable when defined and not assumed"
        );
        assert!(
            Cic::type_check_term(
                &Application(
                    Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                    Box::new(Variable("TYPE".to_string(), GLOBAL_INDEX)),
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts illegal function application"
        );
    }

    #[test]
    fn test_argument_dependent_function() {
        let unit = Variable("Unit".to_string(), GLOBAL_INDEX);
        let boolean = Variable("Bool".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Bool", &Sort("TYPE".to_string()));
        test_env
            .add_to_context("true", &boolean);
        test_env.add_to_context("Unit", &Sort("TYPE".to_string()));
        test_env.add_to_context("it", &unit);
        let type_var_name = "T";
        // if : ∀ T:TYPE. ∀ exp:Bool. ∀ ifTrue:Unit->T. T
        test_env.add_to_context(
            "if",
            &Product(
                type_var_name.to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Product(
                    "exp".to_string(),
                    Box::new(boolean.clone()),
                    Box::new(Product(
                        "ifTrue".to_string(),
                        Box::new(Product(
                            "_".to_string(),
                            Box::new(unit.clone()),
                            Box::new(Variable(type_var_name.to_string(), 0)),
                        )),
                        Box::new(Variable(type_var_name.to_string(), 0)),
                    )),
                )),
            ),
        );

        assert!(
            Cic::type_check_term(
                &Application(
                    Box::new(Application(
                        Box::new(Application(
                            Box::new(Variable("if".to_string(), GLOBAL_INDEX)),
                            Box::new(unit.clone()),
                        )),
                        Box::new(Variable("true".to_string(), GLOBAL_INDEX))
                    )),
                    Box::new(Abstraction(
                        "_".to_string(), 
                        Box::new(unit.clone()),
                        Box::new(Variable("it".to_string(), GLOBAL_INDEX)),
                    ))
                ),
                &mut test_env
            )
            .is_ok(),
            "Type checker refutes nested application when following argument types depend on previous"
        );
        assert_eq!(test_env.get_from_deltas(type_var_name), None, "Argument dependent application type checking stains Δ with local variable names");
        assert!(
            Cic::type_check_stm(
                &Fun(
                    "unifyResult".to_string(),
                    vec![("b".to_string(), boolean.clone())],
                    Box::new(unit.clone()),
                    Box::new(Application(
                        Box::new(Application(
                            Box::new(Application(
                                Box::new(Variable("if".to_string(), GLOBAL_INDEX)),
                                Box::new(unit.clone()),
                            )),
                            Box::new(Variable("b".to_string(), 0))
                        )),
                        Box::new(Abstraction(
                            "_".to_string(), 
                            Box::new(unit.clone()),
                            Box::new(Variable("it".to_string(), GLOBAL_INDEX)),
                        ))
                    )),
                    false
                ),
                &mut test_env
            )
            .is_ok(), 
            "Type checker cant unify function output type with the result of a polymorphic expression"
        );
    }

    #[test]
    fn test_type_check_let() {
        let mut test_env = Cic::default_environment();
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let zero = Variable("z".to_string(), GLOBAL_INDEX);
        test_env.add_to_context("z", &nat);

        assert!(
            Cic::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(Some(nat.clone())),
                    Box::new(zero.clone()),
                    Box::new(Variable("n".to_string(), 1)),
                ),
                &mut test_env
            ).is_ok(),
            "Type checker doesnt support let definitions"
        );
        assert!(
            Cic::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(None),
                    Box::new(zero.clone()),
                    Box::new(Variable("n".to_string(), 1)),
                ),
                &mut test_env
            ).is_ok(),
            "Let type checker doesnt supported untyped definitions"
        );
        assert!(
            Cic::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(Some(Variable("UnboundType".to_string(), GLOBAL_INDEX))),
                    Box::new(zero.clone()),
                    Box::new(Variable("n".to_string(), 1)),
                ),
                &mut test_env
            ).is_err(),
            "Let type checker accepts definition with unbound annotated type"
        );
        assert!(
            Cic::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(Some(nat.clone())),
                    Box::new(Variable("unbound_term".to_string(), 1)),
                    Box::new(Variable("n".to_string(), 1)),
                ),
                &mut test_env
            ).is_err(),
            "Let type checker accepts definition with ill-typed body"
        );
        assert!(
            Cic::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(Some(nat.clone())),
                    Box::new(zero.clone()),
                    Box::new(Variable("unbound_term".to_string(), 1)),
                ),
                &mut test_env
            ).is_err(),
            "Let type checker accepts definition with ill-typed scope"
        );
    }

    #[test]
    fn test_list_match() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let list = Variable("List".to_string(), GLOBAL_INDEX);
        let nil = Variable("nil".to_string(), GLOBAL_INDEX);
        let cons = Variable("cons".to_string(), GLOBAL_INDEX);
        let type_var = Variable("T".to_string(), 0);
        let sort = Sort("TYPE".to_string());
        let mut test_env = Cic::default_environment();

        let _ = evaluate_inductive(
            &mut test_env,
            "List",
            &vec![("T".to_string(), Sort("TYPE".to_string()))],
            &Sort("TYPE".to_string()),
            &vec![
                ("nil".to_string(), Application(
                    Box::new(list.clone()), 
                    Box::new(type_var.clone())
                )),
                ("cons".to_string(), Product(
                    "e".to_string(), 
                    Box::new(type_var.clone()), 
                    Box::new(Product(
                        "l".to_string(), 
                        Box::new(Application(
                            Box::new(list.clone()), 
                            Box::new(type_var.clone())
                        )), 
                        Box::new(Application(
                            Box::new(list.clone()), 
                            Box::new(type_var.clone())
                        ))
                    ))
                ))
            ],
        );
        
        test_env.add_to_context(
            "test_list",
            &Application(
                    Box::new(list.clone()), 
                    Box::new(nat.clone())
                )
        );
        test_env
            .add_to_context("Nat", &sort);

        assert!(
            Cic::type_check_term(
                &Match(
                    Box::new(Variable("test_list".to_string(), GLOBAL_INDEX)),
                    vec![
                        (
                            Application(
                                Box::new(nil.clone()),
                                Box::new(nat.clone()),
                            ),
                            Variable("test_list".to_string(), GLOBAL_INDEX)
                        ),
                        (
                            Application(
                                Box::new(Application(
                                    Box::new(Application(
                                        Box::new(cons.clone()),
                                        Box::new(nat.clone()),
                                    )),
                                    Box::new(Variable("n".to_string(), 0))
                                )),
                                Box::new(Variable("l".to_string(), 1)),
                            ),
                            Variable("test_list".to_string(), GLOBAL_INDEX)
                        ),
                    ]
                ),
                &mut test_env
            )
            .is_ok(),
            "match type checking doesnt work with type dependent types"
        );
        // assert!(
        //     Cic::type_check_term(
        //         &Match(
        //             Box::new(Variable("test_list".to_string(), GLOBAL_INDEX)),
        //             vec![
        //                 (
        //                     vec![
        //                         nil.clone(), 
        //                         Meta(0),
        //                     ],
        //                     Variable("test_list".to_string(), GLOBAL_INDEX)
        //                 ),
        //                 (
        //                     vec![
        //                         cons.clone(),
        //                         Meta(0),
        //                         Variable("n".to_string(), 0),
        //                         Variable("l".to_string(), 1),
        //                     ],
        //                     Variable("test_list".to_string(), GLOBAL_INDEX)
        //                 ),
        //             ]
        //         ),
        //         &mut test_env
        //     )
        //     .is_ok(),
        //     "match type checking doesnt support unification in pattern"
        // );
    }

    #[test]
    fn test_match_inference() {
        let mut test_env = packed_env();

        let tt = var("true");
        let matched = app("nil", vec![var("Bool")]);
        let matc = Match(
            Box::new(matched),
            vec![
                (app("nil", vec![Meta(0)]), tt.clone()),
                (app("cons", vec![Meta(0), var("h"), var("l")]), tt.clone()),
            ],
        );

        assert_eq!(
            Cic::type_check_term(&matc, &mut test_env),
            Ok(Variable("Bool".to_string(), GLOBAL_INDEX)),
            "Match type checking fails when pattern make use of metavariables"
        );
    }

    #[test]
    fn test_nested_pattern_match() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = packed_env();
        test_env.add_to_context("c", &nat.clone());

        assert_eq!(
            Cic::type_check_term(
                &Match(
                    Box::new(var("c")),
                    vec![
                        (var("0"), var("0")),
                        // s (s n) => n : unpacks the argument of the nested
                        // `s` constructor instead of binding it as a whole
                        (
                            app("s", vec![app("s", vec![var("n")])]),
                            var("n")
                        ),
                    ]
                ),
                &mut test_env
            )
            .unwrap(),
            nat.clone(),
            "Type checker refuses match with a nested constructor pattern unpacking an argument of the same inductive type"
        );

        assert_eq!(
            Cic::type_check_term(
                &Match(
                    Box::new(var("c")),
                    vec![
                        (var("0"), var("0")),
                        // s (s (s n)) => n : unpacking should keep working at
                        // arbitrary nesting depth
                        (
                            app(
                                "s",
                                vec![app("s", vec![app("s", vec![var("n")])])]
                            ),
                            var("n")
                        ),
                    ]
                ),
                &mut test_env
            )
            .unwrap(),
            nat.clone(),
            "Type checker refuses match with a doubly nested constructor pattern"
        );
    }

    #[test]
    fn test_nested_pattern_match_recursive_type() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let list = Variable("List".to_string(), GLOBAL_INDEX);
        let mut test_env = packed_env();
        test_env.add_to_context(
            "test_list",
            &Application(Box::new(list.clone()), Box::new(nat.clone())),
        );

        // cons Nat n (cons Nat m nil) => m : unpacks a nested list pattern
        // where a recursive `List` constructor argument is expected
        let double_nested_pattern = app(
            "cons",
            vec![
                nat.clone(),
                var("n"),
                app(
                    "cons",
                    vec![nat.clone(), var("m"), app("nil", vec![nat.clone()])],
                ),
            ],
        );
        assert_eq!(
            Cic::type_check_term(
                &Match(
                    Box::new(var("test_list")),
                    vec![
                        (app("nil", vec![nat.clone()]), var("0")),
                        (double_nested_pattern, var("m")),
                    ]
                ),
                &mut test_env
            )
            .unwrap(),
            nat.clone(),
            "Type checker refuses match unpacking a nested list constructor pattern"
        );

        // cons Nat n (cons Nat m (cons Nat o nil)) => o : unpacking should
        // also work with a triply nested pattern
        let triple_nested_pattern = app(
            "cons",
            vec![
                nat.clone(),
                var("n"),
                app(
                    "cons",
                    vec![
                        nat.clone(),
                        var("m"),
                        app(
                            "cons",
                            vec![
                                nat.clone(),
                                var("o"),
                                app("nil", vec![nat.clone()]),
                            ],
                        ),
                    ],
                ),
            ],
        );
        assert_eq!(
            Cic::type_check_term(
                &Match(
                    Box::new(var("test_list")),
                    vec![
                        (app("nil", vec![nat.clone()]), var("0")),
                        (triple_nested_pattern, var("o")),
                    ]
                ),
                &mut test_env
            )
            .unwrap(),
            nat.clone(),
            "Type checker refuses match unpacking a triply nested list constructor pattern"
        );
    }

    #[test]
    fn test_nested_pattern_match_type_mismatch() {
        let nat = Variable("nat".to_string(), GLOBAL_INDEX);
        let wrapped = Variable("Wrapped".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("o", &nat);
        test_env.add_to_context(
            "s",
            &Product(
                "_".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );
        test_env.add_to_context("c", &nat.clone());
        // a second, unrelated inductive type whose constructor also expects
        // an argument, so it can be used to build an ill-typed nested pattern
        test_env.add_to_context("Wrapped", &Sort("TYPE".to_string()));
        test_env.add_to_context(
            "wrap",
            &Product(
                "_".to_string(),
                Box::new(nat.clone()),
                Box::new(wrapped.clone()),
            ),
        );

        assert!(
            Cic::type_check_term(
                &Match(
                    Box::new(var("c")),
                    vec![
                        (var("o"), var("o")),
                        // s (wrap o) => o : `wrap o` produces `Wrapped`, but
                        // `s` expects an argument of type `nat`
                        (
                            app("s", vec![app("wrap", vec![var("o")])]),
                            var("o")
                        ),
                    ]
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts a nested pattern that produces a type incompatible with the expected argument type"
        );
    }

    #[test]
    //TODO add check of exaustiveness of patterns
    fn test_type_check_match() {
        let nat = Variable("nat".to_string(), GLOBAL_INDEX);
        let boolean = Variable("Bool".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env
            .add_to_context("nat", &Sort("TYPE".to_string()));

        let _ = evaluate_inductive(
            &mut test_env,
            "nat",
            &vec![],
            &Sort("TYPE".to_string()),
            &vec![
                ("o".to_string(), nat.clone()),
                ("s".to_string(), Product(
                    "_".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ))
            ],
        );
        let _ = evaluate_inductive(
            &mut test_env,
            "Bool",
            &vec![],
            &Sort("TYPE".to_string()),
            &vec![
                ("true".to_string(), boolean.clone()),
                ("false".to_string(), boolean.clone()),
            ],
        );
        test_env.add_to_context(
            "c",
            &nat.clone(),
        );

        assert_eq!(
            Cic::type_check_term(
                &Match(
                    Box::new(Variable("c".to_string(), GLOBAL_INDEX)),
                    vec![
                        (
                            Variable("o".to_string(), GLOBAL_INDEX),
                            Variable("o".to_string(), GLOBAL_INDEX)
                        ),
                        (
                            Application(
                                Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                                Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
                            ),
                            Variable("c".to_string(), GLOBAL_INDEX)
                        ),
                    ]
                ),
                &mut test_env
            )
            .unwrap(),
            nat.clone(),
            "Type checker refuses matching over naturals"
        );
        assert!(
            Cic::type_check_term(
                &Match(
                    Box::new(Variable(
                        "stupidUnboundVariable".to_string(), GLOBAL_INDEX
                    )),
                    vec![
                        (
                            Variable("o".to_string(), GLOBAL_INDEX),
                            Variable("o".to_string(), GLOBAL_INDEX)
                        ),
                        (
                            Application(
                                Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                                Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
                            ),
                            Variable("c".to_string(), GLOBAL_INDEX)
                        ),
                    ]
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts matching over unbound variable"
        );
        assert!(
            Cic::type_check_term(
                &Match(
                    Box::new(Variable("c".to_string(), GLOBAL_INDEX)),
                    vec![
                        (
                            Variable("o".to_string(), GLOBAL_INDEX),
                            Variable("o".to_string(), GLOBAL_INDEX)
                        ),
                        (
                            Application(
                                Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                                Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
                            ),
                            Variable("true".to_string(), GLOBAL_INDEX) //this body has type : Bool
                        ),
                    ]
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts match with inconsistent branch types"
        );

        //TODO this should be address: do we want pattern variable to override names in context
        //or should the declared variables names be fresh?
        // assert!(
        //     Cic::type_check_term(
        //         Match(
        //             Box::new(Variable("c".to_string())),
        //             vec![
        //                 (
        //                     vec![Variable("c".to_string())], //random variable in place of constr
        //                     Variable("o".to_string())
        //                 ),
        //                 (
        //                     vec![
        //                         Variable("s".to_string()),
        //                         Variable("n".to_string())
        //                     ],
        //                     Variable("n".to_string())
        //                 ),
        //             ]
        //         ),
        //         &mut test_env
        //     )
        //     .is_err(),
        //     "Type checker accepts match with random (properly typed) variable in place of constructor"
        // );
    }

    #[test]
    fn test_match_exhaustiveness() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = packed_env();
        test_env.add_to_context(
            "n",
            &nat,
        );

        assert!(
            Cic::type_check_term(&Match(
                Box::new(var("n")), vec![
                    (var("0"), var("0"))
                ]), &mut test_env
            ).is_err(),
            "Match type checking accepts natural matching without a successor case"
        );
        assert!(
            Cic::type_check_term(&Match(
                Box::new(var("n")), vec![
                    (Application(
                        Box::new(var("s")),
                        Box::new(var("m"))
                    ), var("0"))
                ]), &mut test_env
            ).is_err(),
            "Match type checking accepts natural matching without a 0 base case"
        );
        // TODO for a fix see issue #267
        // assert!(
        //     Cic::type_check_term(&Match(
        //         Box::new(var("n")), vec![
        //             (var("0"), var("0")),
        //             (Application(
        //                 Box::new(var("s")), 
        //                 Box::new(var("0")),
        //             ), var("0")),
        //         ]), &mut test_env
        //     ).is_err(),
        //     "Match type checking accepts natural matching that covers all constructor but one not exhaustively"
        // );
    }

    #[test]
    fn test_type_check_inductive() {
        let nat = Variable("nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        #[allow(non_snake_case)]
        let TYPE = Sort("TYPE".to_string());

        assert!(
            type_check_inductive(
                &mut test_env,
                "Empty",
                &vec![],
                &TYPE,
                &vec![]
            )
            .is_ok(),
            "Inductive type checking is refuting empty type"
        );
        assert!(
            type_check_inductive(
                &mut test_env,
                "inc",
                &vec![],
                &TYPE,
                &vec![
                    ("correct".to_string(), Variable("inc".to_string(), GLOBAL_INDEX)),
                    ("wrong".to_string(), Variable("wrongType".to_string(), GLOBAL_INDEX))
                ]
            )
            .is_err(),
            "Inductive type checking is accepting ill typed constructor"
        );
        assert!(
            type_check_inductive(
                &mut test_env,
                "fail",
                &vec![],
                &Sort("UNBOUND_SORT".to_string()),
                &vec![]
            )
            .is_err(),
            "Inductive type checking is accepting definition on non existent arieties"
        );
        assert!(
            test_env.with_local_assumptions(&vec![
                ("nat".to_string(), TYPE.clone()),
                ("zero".to_string(), nat.clone())
            ], |local_env| {
                type_check_inductive(
                    local_env,
                    "fail",
                    &vec![],
                    &Variable("zero".to_string(), GLOBAL_INDEX),  //bound, non-sort variable
                    &vec![("cons".to_string(), Variable("zero".to_string(), GLOBAL_INDEX))]
                )
                .is_err()
            }),
            "Inductive type checking is accepting definition with simple term (non-type) ariety"
        );
        assert!(
            test_env.with_local_assumptions(&vec![
                ("nat".to_string(), TYPE.clone()),
                ("zero".to_string(), nat.clone())
            ], |local_env| {
                type_check_inductive(
                    local_env,
                    "fail",
                    &vec![],
                    &TYPE,
                    &vec![("cons".to_string(), Variable("zero".to_string(), GLOBAL_INDEX))]
                )
                .is_err()
            }),
            "Inductive type checking is accepting definition with simple term (non-type) constructor type"
        );
        assert!(
            Cic::type_check_stm(
                &InductiveDef(
                    "Empty".to_string(),
                    vec![],
                    Box::new(TYPE.clone()),
                    vec![]
                ),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support inductive definitions"
        );
    }

    #[test]
    fn test_inductive_equality() {
        let mut test_env = Cic::default_environment();
        #[allow(non_snake_case)]
        let TYPE = Sort("TYPE".to_string());

        assert!(
            type_check_inductive(
                &mut test_env,
                "Eq",
                &vec![
                    ("T".to_string(), TYPE.clone()),
                    ("x".to_string(), Variable("T".to_string(), 0))
                ],
                &Product(
                    "_".to_string(),
                    Box::new(Variable("T".to_string(), 0)),
                    Box::new(Sort("PROP".to_string()))
                ),
                &vec![(
                    "refl".to_string(),
                    Application(
                        Box::new(Application(
                            Box::new(Application(
                                Box::new(Variable("Eq".to_string(), GLOBAL_INDEX)),
                                Box::new(Variable("T".to_string(), 0))
                            )),
                            Box::new(Variable("x".to_string(), 1))
                        )),
                        Box::new(Variable("x".to_string(), 1))
                    )
                )]
            )
            .is_ok(),
            "Inductive type checker doesnt accept equality definition"
        );

        let equality_type = test_env.get_from_context("Eq");
        assert!(
            equality_type.is_some(), 
            "Inductive definition wasnt included in context after type checking"
        );
        let (_, equality_type) = equality_type.unwrap();
        assert_eq!(
            equality_type,
            Product(
                "T".to_string(),
                Box::new(TYPE.clone()),
                Box::new(Product(
                    "x".to_string(), 
                    Box::new(Variable("T".to_string(), 0)),
                    Box::new(Product(
                        "_".to_string(),
                        Box::new(Variable("T".to_string(), 0)),
                        Box::new(Sort("PROP".to_string()))
                    ))
                ))
            )
        );

        let refl_type = test_env.get_from_context("refl");
        assert!(
            refl_type.is_some(), 
            "Inductive constructor wasnt included in context after type checking"
        );
        let (_, refl_type) = refl_type.unwrap();
        assert_eq!(
            refl_type,
            Product(
                "T".to_string(),
                Box::new(TYPE.clone()),
                Box::new(Product(
                    "x".to_string(), 
                    Box::new(Variable("T".to_string(), 0)),
                    Box::new(Application(
                        Box::new(Application(
                            Box::new(Application(
                                Box::new(Variable("Eq".to_string(), GLOBAL_INDEX)),
                                Box::new(Variable("T".to_string(), 0))
                            )),
                            Box::new(Variable("x".to_string(), 1))
                        )),
                        Box::new(Variable("x".to_string(), 1))
                    ))
                ))
            ),
            "Inductive constructor doesnt have the proper type"
        );
    }

    #[test]
    fn test_inductive_naturals() {
        let mut test_env = Cic::default_environment();
        #[allow(non_snake_case)]
        let TYPE = Sort("TYPE".to_string());
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let constructors = vec![
            ("o".to_string(), nat.clone()),
            (
                "s".to_string(),
                Product(
                    "_".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
            ),
        ];

        assert!(
            type_check_inductive(
                &mut test_env,
                "Nat",
                &vec![],
                &TYPE,
                &constructors
            ).is_ok(),
            "Inductive type checking isnt passing nat definition"
        );

        let nat_type = test_env.get_from_context("Nat");
        assert!(
            nat_type.is_some(), 
            "Inductive definition wasnt included in context after type checking"
        );
        let (_, nat_type) = nat_type.unwrap();
        assert_eq!(
            nat_type,
            TYPE,
            "Inductive type wasnt constructed properly"
        );
        
        let zero_type = test_env.get_from_context("o");
        assert!(
            zero_type.is_some(), 
            "Zero constructor wasnt included in context after type checking"
        );
        let (_, zero_type) = zero_type.unwrap();
        assert_eq!(
            zero_type,
            Variable("Nat".to_string(), GLOBAL_INDEX),
            "Zero constructor type wasnt constructed properly"
        );
        
        let succ_type = test_env.get_from_context("s");
        assert!(
            succ_type.is_some(), 
            "Successor constructor wasnt included in context after type checking"
        );
        let (_, succ_type) = succ_type.unwrap();
        assert_eq!(
            succ_type,
            Product(
                "_".to_string(),
                Box::new(Variable("Nat".to_string(), GLOBAL_INDEX)),
                Box::new(Variable("Nat".to_string(), GLOBAL_INDEX)),
            ),
            "Successor constructor type wasnt constructed properly"
        );
    }

    #[test]
    fn test_inductive_lists() {
        let mut test_env = Cic::default_environment();
        #[allow(non_snake_case)]
        let TYPE = Sort("TYPE".to_string());

        let list_of_t = Application(
            Box::new(Variable("list".to_string(), GLOBAL_INDEX)),
            Box::new(Variable("T".to_string(), 0)),
        );
        let constructors = vec![
            ("nil".to_string(), list_of_t.clone()),
            (
                "cons".to_string(),
                Product(
                    "_".to_string(),
                    Box::new(Variable("T".to_string(), 0)),
                    Box::new(Product(
                        "_".to_string(),
                        Box::new(list_of_t.clone()),
                        Box::new(list_of_t.clone()),
                    )),
                ),
            ),
        ];
        let wrong_constructors = vec![
            ("nil".to_string(), list_of_t.clone()),
            (
                "cons".to_string(),
                Product(
                    "_".to_string(),
                    Box::new(Variable("T_T".to_string(), 0)), //unbound variable
                    Box::new(Product(
                        "_".to_string(),
                        Box::new(list_of_t.clone()),
                        Box::new(list_of_t.clone()),
                    )),
                ),
            ),
        ];
        assert!(
            type_check_inductive(
                &mut test_env,
                "list",
                &vec![("T".to_string(), TYPE.clone())],
                &TYPE,
                &constructors
            )
            .is_ok(),
            "Inductive type checking isnt working with dependent inductive types"
        );
        assert!(
            type_check_inductive(
                &mut test_env,
                "list",
                &vec![("T".to_string(), TYPE.clone())],
                &TYPE,
                &wrong_constructors
            )
            .is_err(),
            "Inductive type checking isnt working with dependent inductive types"
        );
    }

    #[test]
    fn test_type_check_fun() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = packed_env();

        assert!(
            Cic::type_check_stm(
                &Fun(
                    "f".to_string(),
                    vec![("t".to_string(), Sort("TYPE".to_string()))],
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable("t".to_string(), 0)),
                    false
                ),
                &mut test_env,
            )
            .is_ok(),
            "Type checking refuses identity function"
        );

        let args = vec![
            ("n".to_string(), nat.clone()),
            ("m".to_string(), nat.clone()),
        ];
        let zerobranch = (
            //patter
            Variable("0".to_string(), GLOBAL_INDEX),
            //body
            Variable("m".to_string(), GLOBAL_INDEX),
        );
        let succbranch = (
            //patter
            Application(
                Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                Box::new(Variable("nn".to_string(), GLOBAL_INDEX)),
            ),
            //body
            Application(
                Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                Box::new(Application(
                    Box::new(Application(
                        Box::new(Variable("add".to_string(), GLOBAL_INDEX)),
                        Box::new(Variable("nn".to_string(), GLOBAL_INDEX)),
                    )),
                    Box::new(Variable("m".to_string(), GLOBAL_INDEX)),
                )),
            ),
        );
        assert!(
            Cic::type_check_stm(
                &Fun(
                    "add".to_string(),
                    args.clone(),
                    Box::new(Sort("Nat".to_string())),
                    Box::new(Match(
                        Box::new(Variable("n".to_string(), 0)),
                        vec![zerobranch.clone(), succbranch.clone()]
                    )),
                    false
                ),
                &mut test_env,
            )
            .is_err(),
            "Type checking accepts recursive function not marked as recursive"
        );
        let res = Cic::type_check_stm(
            &Fun(
                "add".to_string(),
                args.clone(),
                Box::new(nat.clone()),
                Box::new(Match(
                    Box::new(Variable("n".to_string(), 0)),
                    vec![zerobranch, succbranch],
                )),
                true
            ),
            &mut test_env,
        );
        assert!(
            res.is_ok(),
            "Type checking refuses recursive functions:\n{:?}",
            res.err()
        );

        assert!(
            Cic::type_check_stm(
                &Fun(
                    "f".to_string(),
                    vec![], 
                    Box::new(nat.clone()),
                    Box::new(Sort("TYPE".to_string())),
                    false
                ),
                &mut test_env,
            ).is_err(),
            "Type checking accept function with a inconsistent declared and result type",
        );
    }

    #[test]
    fn test_inductive_eliminator() {
        let unit = Variable("Unit".to_string(), GLOBAL_INDEX);
        let boolean = Variable("Bool".to_string(), GLOBAL_INDEX);
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let list = Variable("List".to_string(), GLOBAL_INDEX);
        let vec = Variable("Vec".to_string(), GLOBAL_INDEX);

        // Unit
        assert_eq!(
            inductive_eliminator(
                "Unit".to_string(),
                vec![],
                Sort("TYPE".to_string()),
                vec![("it".to_string(), unit.clone())]
            ),
            Product(
                "er_Unit".to_string(),
                Box::new(Product(
                    "instance".to_string(),
                    Box::new(unit.clone()),
                    Box::new(Sort("TYPE".to_string())),
                )),
                Box::new(Product(
                    "c_0".to_string(),
                    Box::new(Application(
                        Box::new(Variable("er_Unit".to_string(), 0)),
                        Box::new(Variable("it".to_string(), GLOBAL_INDEX)),
                    )),
                    Box::new(Product(
                        "t".to_string(),
                        Box::new(unit.clone()),
                        Box::new(Application(
                            Box::new(Variable("er_Unit".to_string(), 0)),
                            Box::new(Variable("t".to_string(), 2)),
                        )),
                    ))
                ))
            ),
            "Unit inductive eliminator not properly constructed"
        );
        // Bool
        assert_eq!(
            inductive_eliminator(
                "Bool".to_string(),
                vec![],
                Sort("TYPE".to_string()),
                vec![
                    ("true".to_string(), boolean.clone()),
                    ("false".to_string(), boolean.clone())
                ]
            ),
            Product(
                "er_Bool".to_string(),
                Box::new(Product(
                    "instance".to_string(),
                    Box::new(boolean.clone()),
                    Box::new(Sort("TYPE".to_string())),
                )),
                Box::new(Product(
                    "c_0".to_string(),
                    Box::new(Application(
                        Box::new(Variable("er_Bool".to_string(), 0)),
                        Box::new(Variable("true".to_string(), GLOBAL_INDEX)),
                    )),
                    Box::new(Product(
                        "c_1".to_string(),
                        Box::new(Application(
                            Box::new(Variable("er_Bool".to_string(), 0)),
                            Box::new(Variable("false".to_string(), GLOBAL_INDEX)),
                        )),
                        Box::new(Product(
                            "t".to_string(),
                            Box::new(boolean.clone()),
                            Box::new(Application(
                                Box::new(Variable("er_Bool".to_string(), 0)),
                                Box::new(Variable("t".to_string(), 3)),
                            ))
                        ))
                    ))
                ))
            ),
            "Boolean inductive eliminator not properly constructed"
        );
        // these next tests are copied straight from the examples in
        // Inductive Families (Dybjer) paper
        // Nat
        assert_eq!(
            inductive_eliminator(
                "Nat".to_string(),
                vec![],
                Sort("TYPE".to_string()),
                vec![
                    ("z".to_string(), nat.clone()),
                    (
                        "s".to_string(),
                        Product(
                            "r_0".to_string(),
                            Box::new(nat.clone()),
                            Box::new(nat.clone())
                        )
                    )
                ]
            ),
            Product(
                "er_Nat".to_string(),
                Box::new(Product(
                    "instance".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Sort("TYPE".to_string())),
                )),
                Box::new(Product(
                    "c_0".to_string(),
                    Box::new(Application(
                        Box::new(Variable("er_Nat".to_string(), 0)),
                        Box::new(Variable("z".to_string(), GLOBAL_INDEX)),
                    )),
                    Box::new(Product(
                        "c_1".to_string(),
                        Box::new(Product(
                            "r_0".to_string(),
                            Box::new(nat.clone()),
                            Box::new(Product(
                                "ih_0".to_string(),
                                Box::new(Application(
                                    Box::new(Variable("er_Nat".to_string(), 0)),
                                    Box::new(Variable("r_0".to_string(), 3))
                                )),
                                Box::new(Application(
                                    Box::new(Variable("er_Nat".to_string(), 0)),
                                    Box::new(Application(
                                        Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                                        Box::new(Variable("r_0".to_string(), 3))
                                    ))
                                ))
                            ))
                        )),
                        Box::new(Product(
                            "t".to_string(),
                            Box::new(nat.clone()),
                            Box::new(Application(
                                Box::new(Variable("er_Nat".to_string(), 0)),
                                Box::new(Variable("t".to_string(), 3))
                            ))
                        ))
                    ))
                )),
            ),
            "Naturals inductive eliminator not properly constructed"
        );
        // List
        assert_eq!(
            inductive_eliminator(
                "List".to_string(),
                vec![("T".to_string(), Sort("TYPE".to_string()))],
                Sort("TYPE".to_string()),
                vec![
                    (
                        "nil".to_string(),
                        Application(
                            Box::new(list.clone()),
                            Box::new(Variable("T".to_string(), 0))
                        )
                    ),
                    (
                        "cons".to_string(),
                        Product(
                            "elem".to_string(),
                            Box::new(Variable("T".to_string(), 0)),
                            Box::new(Product(
                                "l".to_string(),
                                Box::new(Application(
                                    Box::new(list.clone()),
                                    Box::new(Variable("T".to_string(), 0))
                                )),
                                Box::new(Application(
                                    Box::new(list.clone()),
                                    Box::new(Variable("T".to_string(), 0))
                                ))
                            ))
                        )
                    )
                ]
            ),
            Product(
                "T".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Product(
                    "er_List".to_string(),
                    Box::new(Product(
                        "instance".to_string(),
                        Box::new(Application(
                            Box::new(list.clone()),
                            Box::new(Variable("T".to_string(), 0))
                        )),
                        Box::new(Sort("TYPE".to_string()))
                    )),
                    Box::new(Product(
                        "c_0".to_string(),
                        Box::new(Application(
                            Box::new(Variable("er_List".to_string(), 1)),
                            Box::new(Application(
                                Box::new(Variable("nil".to_string(), GLOBAL_INDEX)),
                                Box::new(Variable("T".to_string(), 0))
                            )),
                        )),
                        Box::new(Product(
                            "c_1".to_string(),
                            Box::new(Product(
                                "nr_0".to_string(),
                                Box::new(Variable("T".to_string(), 0)),
                                Box::new(Product(
                                    "r_1".to_string(),
                                    Box::new(Application(
                                        Box::new(list.clone()),
                                        Box::new(Variable("T".to_string(), 0))
                                    )),
                                    Box::new(Product(
                                        "ih_0".to_string(),
                                        Box::new(Application(
                                            Box::new(Variable(
                                                "er_List".to_string(), 1
                                            )),
                                            Box::new(Variable(
                                                "r_1".to_string(), 5
                                            ))
                                        )),
                                        Box::new(Application(
                                            Box::new(Variable(
                                                "er_List".to_string(), 1
                                            )),
                                            Box::new(Application(
                                                Box::new(Application(
                                                    Box::new(Application(
                                                        Box::new(Variable(
                                                            "cons".to_string(), GLOBAL_INDEX
                                                        )),
                                                        Box::new(Variable(
                                                            "T".to_string(), 0
                                                        ))
                                                    )),
                                                    Box::new(Variable(
                                                        "nr_0".to_string(), 4
                                                    ))
                                                )),
                                                Box::new(Variable(
                                                    "r_1".to_string(), 5
                                                ))
                                            ))
                                        ))
                                    ))
                                ))
                            )),
                            Box::new(Product(
                                "t".to_string(),
                                Box::new(Application(
                                    Box::new(list.clone()),
                                    Box::new(Variable("T".to_string(), 0))
                                )),
                                Box::new(Application(
                                    Box::new(Variable("er_List".to_string(), 1)),
                                    Box::new(Variable("t".to_string(), 4))
                                ))
                            ))
                        )),
                    ))
                ))
            ),
            "List inductive eliminator not properly constructed"
        );
        // Vec
        assert_eq!(
            inductive_eliminator(
                "Vec".to_string(),
                vec![("T".to_string(), Sort("TYPE".to_string()))],
                Product(
                    "len".to_string(), 
                    Box::new(nat.clone()), 
                    Box::new(Sort("TYPE".to_string()))
                ), 
                vec![
                    ("nul".to_string(), Application(
                        Box::new(Application(
                            Box::new(vec.clone()), 
                            Box::new(Variable("T".to_string(), 0))
                        )),
                        Box::new(Variable("z".to_string(), GLOBAL_INDEX))
                    )),
                    ("cons".to_string(), Product(
                        "nr_0".to_string(), 
                        Box::new(Variable("T".to_string(), 0)), 
                        Box::new(Product(
                            "nr_1".to_string(),
                            Box::new(nat.clone()), 
                            Box::new(Product(
                                "r_2".to_string(), 
                                Box::new(Application(
                                    Box::new(Application(
                                        Box::new(vec.clone()), 
                                        Box::new(Variable("T".to_string(), 0))
                                    )),
                                    Box::new(Variable("nr_1".to_string(), 2))
                                )), 
                                Box::new(Application(
                                    Box::new(Application(
                                        Box::new(vec.clone()), 
                                        Box::new(Variable("T".to_string(), 0))
                                    )),
                                    Box::new(Application(
                                        Box::new(Variable("s".to_string(), GLOBAL_INDEX)), 
                                        Box::new(Variable("nr_1".to_string(), 2))
                                    ))
                                )) 
                            )) 
                        )) 
                    ))
                ]
            ),

            Product(
                "T".to_string(), 
                Box::new(Sort("TYPE".to_string())),
                Box::new(Product(
                    "er_Vec".to_string(),
                    Box::new(Product(
                        "len".to_string(),
                        Box::new(nat.clone()),
                        Box::new(Product(
                            "instance".to_string(), 
                            Box::new(Application(
                                Box::new(Application(
                                    Box::new(vec.clone()), 
                                    Box::new(Variable("T".to_string(), 0))
                                )),
                                Box::new(Variable("len".to_string(), 2))
                            )), 
                            Box::new(Sort("TYPE".to_string())) 
                        ))
                    )),
                    Box::new(Product(
                        "c_0".to_string(), 
                        Box::new(Application(
                            Box::new(Application(
                                Box::new(Variable("er_Vec".to_string(), 1)), 
                                Box::new(Variable("z".to_string(), GLOBAL_INDEX))
                            )),
                            Box::new(Application(
                                Box::new(Variable("nul".to_string(), GLOBAL_INDEX)),
                                Box::new(Variable("T".to_string(), 0))
                            ))
                        )),
                        Box::new(Product(
                            "c_1".to_string(),
                            Box::new(Product(
                                "nr_0".to_string(), 
                                Box::new(Variable("T".to_string(), 0)), 
                                Box::new(Product(
                                    "nr_1".to_string(),
                                    Box::new(nat.clone()),
                                    Box::new(Product(
                                        "r_2".to_string(), 
                                        Box::new(Application(
                                            Box::new(Application(
                                                Box::new(vec.clone()), 
                                                Box::new(Variable("T".to_string(), 0))
                                            )),
                                            Box::new(Variable("nr_1".to_string(), 5))
                                        )), 
                                        Box::new(Product(
                                            "ih_0".to_string(), 
                                            Box::new(Application(
                                                Box::new(Application(
                                                    Box::new(Variable("er_Vec".to_string(), 1)), 
                                                    Box::new(Variable("nr_1".to_string(), 5))
                                                )),
                                                Box::new(Variable("r_2".to_string(), 6))
                                            )), 
                                            Box::new(Application(
                                                Box::new(Application(
                                                    Box::new(Variable("er_Vec".to_string(), 1)), 
                                                    Box::new(Application(
                                                        Box::new(Variable("s".to_string(), GLOBAL_INDEX)), 
                                                        Box::new(Variable("nr_1".to_string(), 5))
                                                    ))
                                                )),
                                                Box::new(Application(
                                                    Box::new(Application(
                                                        Box::new(Application(
                                                            Box::new(Application(
                                                                Box::new(Variable("cons".to_string(), GLOBAL_INDEX)),
                                                                Box::new(Variable("T".to_string(), 0))
                                                            )),
                                                            Box::new(Variable("nr_0".to_string(), 4))
                                                        )),
                                                        Box::new(Variable("nr_1".to_string(), 5))
                                                    )),
                                                    Box::new(Variable("r_2".to_string(), 6))
                                                ))
                                            )) 
                                        )) 
                                    ))
                                ))
                            )),
                            Box::new(Product(
                                "rp_0".to_string(),
                                Box::new(nat.clone()),
                                Box::new(Product(
                                    "t".to_string(), 
                                    Box::new(Application(
                                        Box::new(Application(
                                            Box::new(vec.clone()), 
                                            Box::new(Variable("T".to_string(), 0))
                                        )),
                                        Box::new(Variable("rp_0".to_string(), 4))
                                    )), 
                                    Box::new(Application(
                                        Box::new(Application(
                                            Box::new(Variable("er_Vec".to_string(), 1)), 
                                            Box::new(Variable("rp_0".to_string(), 4))
                                        )),
                                        Box::new(Variable("t".to_string(), 5))
                                    )) 
                                ))
                            ))
                        )), 
                    ))
                ))
            ),
            
            "Length-indexed vector inductive eliminator not properly constructed"
        );
    }

    #[test]
    fn test_positivity_check() {
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Empty", &Sort("TYPE".to_string()));

        assert!(
            Cic::type_check_stm(
                &InductiveDef(
                    "CurrysParadox".to_string(), 
                    vec![], 
                    Box::new(Sort("PROP".to_string())),
                    vec![("paradox".to_string(), Product(
                        "negative".to_string(), 
                        Box::new(Product(
                            "_".to_string(), 
                            Box::new(Variable("CurrysParadox".to_string(), GLOBAL_INDEX)), 
                            Box::new(Variable("Empty".to_string(), GLOBAL_INDEX)) 
                        )), 
                        Box::new(Variable("CurrysParadox".to_string(), GLOBAL_INDEX)), 
                    ))]
                ), 
                &mut test_env
            ).is_err(),
            "Oh no, Curry's paradox is accepted"
        );
    }


    #[test]
    fn test_abstraction_inference() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env
            .add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context(
            "s", 
            &Product(
                "_".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone())
            )
        );
        // id : ? -> ?
        test_env.add_to_context(
            "id", 
            &Product(
                "x".to_string(),
                Box::new(Meta(1)),
                Box::new(Meta(1))
            )
        );

        assert_eq!(
            Cic::type_check_term(
                // λ n:?. s n
                &Abstraction(
                    "n".to_string(), 
                    Box::new(Meta(0)), 
                    Box::new(Application(
                        Box::new(Variable("s".to_string(), GLOBAL_INDEX)), 
                        Box::new(Variable("n".to_string(), 0))
                    ))
                ), 
                &mut test_env
            ),
            Ok(Product("n".to_string(), Box::new(nat.clone()), Box::new(nat.clone()))),
            "Type checking cant inference the type of argument applied to a function Nat->Nat"
        );

        assert_eq!(
            Cic::type_check_term(
                // λ n:Nat. id n
                &Abstraction(
                    "n".to_string(), 
                    Box::new(nat.clone()), 
                    Box::new(Application(
                        Box::new(Variable("id".to_string(), GLOBAL_INDEX)), 
                        Box::new(Variable("n".to_string(), 0))
                    ))
                ), 
                &mut test_env
            ),
            Ok(Product("n".to_string(), Box::new(nat.clone()), Box::new(nat.clone()))),
            "Type checking cant inference the output type of a function Nat->Nat"
        );
    }

    #[test]
    fn test_application_inference() {
        let list = Variable("List".to_string(), GLOBAL_INDEX);
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env
            .add_to_context("Nat", &Sort("TYPE".to_string()));

        test_env.add_to_context(
            "List", 
            &Product(
                "T".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Sort("TYPE".to_string()))
            )
        );
        test_env.add_to_context(
            "cons", 
            &Product(
                "T".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Product(
                    "e".to_string(),
                    Box::new(Variable("T".to_string(), 0)),
                    Box::new(Product(
                        "l".to_string(),
                        Box::new(Application(
                            Box::new(list.clone()),
                            Box::new(Variable("T".to_string(), 0)),
                        )),
                        Box::new(Application(
                            Box::new(list.clone()),
                            Box::new(Variable("T".to_string(), 0)),
                        ))
                    ))
                ))
            )
        );
        test_env.add_to_context("elem", &nat.clone());
        test_env.add_to_context("li", &Application(
            Box::new(list.clone()),
            Box::new(nat.clone()),
        ));
    
        assert_eq!(
            Cic::type_check_term(
                &Application(
                    Box::new(Application(
                        Box::new(Application(
                            Box::new(Variable("cons".to_string(), GLOBAL_INDEX)), 
                            Box::new(Meta(10))
                        )),
                        Box::new(Variable("elem".to_string(), GLOBAL_INDEX))
                    )), 
                    Box::new(Variable("li".to_string(), GLOBAL_INDEX))
                ),
                &mut test_env
            ),
            Ok(Application(
                Box::new(list.clone()),
                Box::new(nat.clone()),
            )),
            "vediamo un po"
        );    
    }

}
