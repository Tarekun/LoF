use crate::type_theory::{
    cic::{
        cic::{
            Cic,
            CicTerm::{
                Abstraction, Application, Let, Product, Sort, Variable,
            },
            GLOBAL_INDEX,
        },
        evaluation::{
            matches_pattern, one_step_reduction, reduce_match,
            reduce_variable,
        },
    },
    interface::TypeTheory,
};

#[test]
fn test_check_pattern_matching() {
    let zero = Variable("z".to_string(), GLOBAL_INDEX);
    let succ = Variable("s".to_string(), GLOBAL_INDEX);

    assert!(
        matches_pattern(&zero, &zero),
        "Pattern matching refutes identical constants"
    );
    assert!(
        !matches_pattern(&zero, &succ),
        "Pattern matching accepts different constants"
    );
    assert!(
        matches_pattern(
            &Application(Box::new(succ.clone()), Box::new(zero.clone())),
            &Application(
                Box::new(succ.clone()),
                Box::new(Variable("renamed_argument".to_string(), 0)),
            )
        ),
        "Pattern matching refutes application with renamed argument"
    );
    assert!(
        !matches_pattern(
            &Application(
                Box::new(Application(
                    Box::new(Variable("cons".to_string(), GLOBAL_INDEX)),
                    Box::new(zero.clone()),
                )),
                Box::new(Variable("l".to_string(), GLOBAL_INDEX))
            ),
            &Application(
                Box::new(Variable("cons".to_string(), GLOBAL_INDEX)),
                Box::new(zero),
            )
        ),
        "Pattern matching accepts only partial pattern"
    );
}

#[test]
fn test_var_reduction() {
    let mut test_env = Cic::default_environment();
    test_env.add_substitution_with_type(
        "test",
        &Variable("Unit".to_string(), GLOBAL_INDEX),
        &Sort("TYPE".to_string()),
    );

    assert_eq!(
        reduce_variable(
            &test_env,
            "constant",
            &Variable("constant".to_string(), GLOBAL_INDEX),
        ),
        Variable("constant".to_string(), GLOBAL_INDEX),
        "Constant δ-reduces to something other than itself"
    );
    assert_eq!(
        reduce_variable(
            &test_env,
            "test",
            &Variable("test".to_string(), 0)
        ),
        Variable("Unit".to_string(), GLOBAL_INDEX),
        "Defined variable doesnt δ-reduce to its body"
    );
}

#[test]
fn test_app_reduction() {
    let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
    let succ = Variable("s".to_string(), GLOBAL_INDEX);
    let zero = Variable("z".to_string(), GLOBAL_INDEX);
    let mut test_env = Cic::default_environment();
    test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
    test_env.add_to_context("z", &nat);
    test_env.add_to_context(
        "s",
        &Product(
            "".to_string(),
            Box::new(nat.clone()),
            Box::new(nat.clone()),
        ),
    );
    test_env.add_substitution_with_type(
        "add_one",
        &Abstraction(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(Application(
                Box::new(succ.clone()),
                Box::new(Variable("n".to_string(), 0)),
            )),
        ),
        &Product(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(nat.clone()),
        ),
    );

    assert_eq!(
        one_step_reduction(
            &mut test_env,
            &Application(Box::new(succ.clone()), Box::new(zero.clone()))
        ),
        Application(Box::new(succ.clone()), Box::new(zero)),
        "Function application of normal form returns a different term"
    );
    assert_eq!(
        one_step_reduction(
            &mut test_env,
            &Application(
                Box::new(Variable("add_one".to_string(), GLOBAL_INDEX)),
                Box::new(Variable("arg".to_string(), GLOBAL_INDEX))
            )
        ),
        Application(
            Box::new(succ.clone()),
            Box::new(Variable("arg".to_string(), GLOBAL_INDEX)),
        ),
        "Function application doesnt reduce to the function body with substituted variable"
    );
}

#[test]
fn test_let_reduction() {
    let mut test_env = Cic::default_environment();
    let zero = Variable("z".to_string(), GLOBAL_INDEX);
    test_env.add_to_context("Nat", &Sort("TYPE".to_string()));

    assert_eq!(
        one_step_reduction(
            &mut test_env,
            &Let(
                "n".to_string(),
                Box::new(None),
                Box::new(zero.clone()),
                Box::new(Variable("n".to_string(), 0)),
            ),
        ),
        zero.to_owned(),
        "Let definition doesnt reduce to its scope with substituted variable"
    );
}

#[test]
fn test_match_reduction() {
    let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
    let succ = Variable("s".to_string(), GLOBAL_INDEX);
    let mut test_env = Cic::default_environment();
    let zero = Variable("z".to_string(), GLOBAL_INDEX);
    let succ_pattern = Application(
        Box::new(succ.clone()),
        Box::new(Variable("n".to_string(), 0)),
    );
    let true_term = Variable("true".to_string(), GLOBAL_INDEX);
    let false_term = Variable("false".to_string(), GLOBAL_INDEX);

    test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
    test_env.add_to_context("z", &nat.clone());
    test_env.add_to_context(
        "s",
        &Product(
            "_".to_string(),
            Box::new(nat.clone()),
            Box::new(nat.clone()),
        ),
    );
    test_env.add_substitution_with_type("x", &zero, &nat.clone());

    assert_eq!(
        reduce_match(
            &mut test_env,
            &zero,
            &vec![
                (zero.clone(), true_term.clone()),
                (succ_pattern.clone(), false_term.clone())
            ]
        ),
        true_term,
        "Match term doesnt δ-reduce to the right branch body"
    );
    assert_eq!(
        reduce_match(
            &mut test_env,
            &Variable("x".to_string(), 0),
            &vec![
                (zero.clone(), true_term.clone()),
                (succ_pattern.clone(), false_term.clone())
            ]
        ),
        true_term,
        "Match term doesnt δ-reduce if matching a variable that needs reduction"
    );
    assert_eq!(
        reduce_match(
            &mut test_env,
            &Application(
                Box::new(succ),
                Box::new(Variable("z".to_string(), GLOBAL_INDEX))
            ),
            &vec![
                (zero.clone(), true_term.clone()),
                (succ_pattern.clone(), false_term.clone())
            ]
        ),
        false_term,
        "Match term doesnt δ-reduce if matching an application pattern"
    );
}

#[test]
fn test_match_reduction_binds_pattern_variables() {
    let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
    let succ = Variable("s".to_string(), GLOBAL_INDEX);
    let zero = Variable("z".to_string(), GLOBAL_INDEX);
    let mut test_env = Cic::default_environment();
    // pattern `s(n)` whose body just returns the bound variable `n`
    let succ_pattern = Application(
        Box::new(succ.clone()),
        Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
    );
    let body_returning_bound_var = Variable("n".to_string(), GLOBAL_INDEX);

    test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
    test_env.add_to_context("z", &nat.clone());
    test_env.add_to_context(
        "s",
        &Product(
            "_".to_string(),
            Box::new(nat.clone()),
            Box::new(nat.clone()),
        ),
    );

    assert_eq!(
        reduce_match(
            &mut test_env,
            &Application(Box::new(succ), Box::new(zero.clone())),
            &vec![(zero.clone(), zero.clone()), (
                succ_pattern,
                body_returning_bound_var
            )]
        ),
        zero,
        "Match reduction doesnt substitute the constructor argument for the pattern's bound variable in the branch body"
    );
}

/// An inductive's auto-generated eliminator must actually *compute* when
/// applied to a concrete constructor, not just type check: without that,
/// anything defined through an eliminator has no definitional behaviour and
/// even a ground equation becomes unprovable by reflexivity.
mod eliminator_iota_reduction {
    use super::*;
    use crate::type_theory::cic::cic::CicTerm;
    use crate::type_theory::environment::Environment;

    /// `Nat`, its constructors and `e_Nat` - registered the way
    /// `evaluate_inductive` registers a real inductive definition.
    fn nat_environment() -> Environment<Cic> {
        let mut env = Cic::default_environment();
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        env.add_to_context("Nat", &Sort("TYPE".to_string()));
        env.add_to_context("z", &nat);
        env.add_to_context(
            "s",
            &Product(
                "_".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );
        env.add_constructor_store(
            "Nat",
            vec![
                ("z".to_string(), nat.clone()),
                (
                    "s".to_string(),
                    Product(
                        "_".to_string(),
                        Box::new(nat.clone()),
                        Box::new(nat.clone()),
                    ),
                ),
            ],
        );
        env.add_inductive_param_count("Nat", 0);
        env
    }

    fn apply(function: CicTerm, arguments: Vec<CicTerm>) -> CicTerm {
        arguments.into_iter().fold(function, |acc, argument| {
            Application(Box::new(acc), Box::new(argument))
        })
    }

    #[test]
    fn test_eliminator_reduces_to_the_base_case_on_zero() {
        let env = nat_environment();
        let motive = Variable("C".to_string(), GLOBAL_INDEX);
        let base = Variable("base".to_string(), GLOBAL_INDEX);
        let step = Variable("step".to_string(), GLOBAL_INDEX);

        let term = apply(
            Variable("e_Nat".to_string(), GLOBAL_INDEX),
            vec![
                motive,
                base.clone(),
                step,
                Variable("z".to_string(), GLOBAL_INDEX),
            ],
        );

        assert_eq!(
            one_step_reduction(&env, &term),
            base,
            "e_Nat applied to `z` must ι-reduce to its base case"
        );
    }

    #[test]
    fn test_eliminator_reduces_to_the_step_case_with_an_induction_hypothesis() {
        let env = nat_environment();
        let motive = Variable("C".to_string(), GLOBAL_INDEX);
        let base = Variable("base".to_string(), GLOBAL_INDEX);
        let step = Variable("step".to_string(), GLOBAL_INDEX);
        let zero = Variable("z".to_string(), GLOBAL_INDEX);
        let one = Application(
            Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
            Box::new(zero.clone()),
        );

        let term = apply(
            Variable("e_Nat".to_string(), GLOBAL_INDEX),
            vec![motive.clone(), base.clone(), step.clone(), one],
        );

        // step applied to the predecessor and to the eliminator re-applied
        // to that predecessor (the induction hypothesis)
        let expected = apply(
            step.clone(),
            vec![
                zero.clone(),
                apply(
                    Variable("e_Nat".to_string(), GLOBAL_INDEX),
                    vec![motive, base, step, zero],
                ),
            ],
        );

        assert_eq!(
            one_step_reduction(&env, &term),
            expected,
            "e_Nat applied to `s(z)` must ι-reduce to the step case, with the eliminator re-applied to `z` as the induction hypothesis"
        );
    }

    #[test]
    fn test_eliminator_is_stuck_on_an_opaque_scrutinee() {
        let env = nat_environment();
        let term = apply(
            Variable("e_Nat".to_string(), GLOBAL_INDEX),
            vec![
                Variable("C".to_string(), GLOBAL_INDEX),
                Variable("base".to_string(), GLOBAL_INDEX),
                Variable("step".to_string(), GLOBAL_INDEX),
                // a bound variable, not a constructor application
                Variable("n".to_string(), 0),
            ],
        );

        assert_eq!(
            one_step_reduction(&env, &term),
            term,
            "an eliminator whose scrutinee isn't constructor-headed must stay stuck rather than picking a branch"
        );
    }
}

/// η-conversion for single-constructor inductives: an *opaque* value of a
/// one-constructor, index-free, non-recursive type is treated as being
/// literally an application of that constructor to its own projections, so
/// a `match`/eliminator over it is no longer stuck.
///
/// The eligibility conditions matter as much as the rule: η for an
/// *indexed* single-constructor type (`Eq`) would say every proof of
/// `Eq(T,x,y)` is `refl`, ie hand out UIP/axiom K, and η for a *recursive*
/// one would feed the rule its own output forever.
mod single_constructor_eta {
    use super::*;
    use crate::type_theory::cic::cic::CicTerm::{self, Match, Proj};
    use crate::type_theory::cic::evaluation::eta_eligible_constructor;
    use crate::type_theory::environment::Environment;

    fn apply(function: CicTerm, arguments: Vec<CicTerm>) -> CicTerm {
        arguments.into_iter().fold(function, |acc, argument| {
            Application(Box::new(acc), Box::new(argument))
        })
    }

    fn global(name: &str) -> CicTerm {
        Variable(name.to_string(), GLOBAL_INDEX)
    }

    /// A `Box(A) := mk(A -> A -> Box(A))`-shaped world:
    /// - `Boxed`: one constructor, no indices, no recursion => eligible
    /// - `Eq`:    one constructor but *indexed*                => not
    /// - `Wrap`:  one constructor but *recursive*              => not
    /// - `Nat`:   two constructors                             => not
    fn eta_environment() -> Environment<Cic> {
        let mut env = Cic::default_environment();
        let type_sort = Sort("TYPE".to_string());
        let nat = global("Nat");

        env.add_to_context("Nat", &type_sort);
        env.add_constructor_store(
            "Nat",
            vec![("z".to_string(), nat.clone()), (
                "s".to_string(),
                Product(
                    "_".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
            )],
        );
        env.add_inductive_param_count("Nat", 0);

        // inductive Boxed : TYPE { | mk : Nat -> Nat -> Boxed }
        let boxed = global("Boxed");
        env.add_to_context("Boxed", &type_sort);
        env.add_constructor_store(
            "Boxed",
            vec![(
                "mk".to_string(),
                Product(
                    "first".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Product(
                        "second".to_string(),
                        Box::new(nat.clone()),
                        Box::new(boxed.clone()),
                    )),
                ),
            )],
        );
        env.add_inductive_param_count("Boxed", 0);

        // inductive Eq (T:TYPE, x:T) : T -> PROP { | refl : Eq(T,x,x) }
        // one constructor, but the type former takes an *index* beyond its
        // two parameters
        env.add_to_context(
            "Eq",
            &Product(
                "T".to_string(),
                Box::new(type_sort.clone()),
                Box::new(Product(
                    "x".to_string(),
                    Box::new(global("T")),
                    Box::new(Product(
                        "_".to_string(),
                        Box::new(global("T")),
                        Box::new(Sort("PROP".to_string())),
                    )),
                )),
            ),
        );
        env.add_constructor_store("Eq", vec![(
            "refl".to_string(),
            Product(
                "T".to_string(),
                Box::new(type_sort.clone()),
                Box::new(Product(
                    "x".to_string(),
                    Box::new(global("T")),
                    Box::new(apply(global("Eq"), vec![
                        global("T"),
                        global("x"),
                        global("x"),
                    ])),
                )),
            ),
        )]);
        env.add_inductive_param_count("Eq", 2);

        // inductive Wrap : TYPE { | wrap : Wrap -> Wrap }
        let wrap = global("Wrap");
        env.add_to_context("Wrap", &type_sort);
        env.add_constructor_store("Wrap", vec![(
            "wrap".to_string(),
            Product(
                "_".to_string(),
                Box::new(wrap.clone()),
                Box::new(wrap.clone()),
            ),
        )]);
        env.add_inductive_param_count("Wrap", 0);

        env
    }

    #[test]
    fn test_only_single_constructor_index_free_non_recursive_types_are_eligible()
    {
        let env = eta_environment();

        let eligible = eta_eligible_constructor(&env, "Boxed");
        assert!(
            matches!(&eligible, Some((name, _, fields)) if name == "mk" && *fields == 2),
            "a one-constructor, index-free, non-recursive type must be eta-eligible, got {:?}",
            eligible.map(|(name, _, fields)| (name, fields))
        );

        assert!(
            eta_eligible_constructor(&env, "Eq").is_none(),
            "an INDEXED single-constructor type must never be eta-eligible: eta for `Eq` is UIP/axiom K"
        );
        assert!(
            eta_eligible_constructor(&env, "Wrap").is_none(),
            "a RECURSIVE single-constructor type must not be eta-eligible: the rule would feed its own output back in forever"
        );
        assert!(
            eta_eligible_constructor(&env, "Nat").is_none(),
            "a type with more than one constructor has no canonical shape to eta-expand into"
        );
    }

    #[test]
    fn test_projection_of_a_concrete_constructor_application_computes() {
        let env = eta_environment();
        let value = apply(global("mk"), vec![global("a"), global("b")]);

        assert_eq!(
            one_step_reduction(
                &env,
                &Proj("Boxed".to_string(), 0, Box::new(value.clone()))
            ),
            global("a"),
            "projecting field 0 of a concrete `mk(a,b)` must compute to `a`"
        );
        assert_eq!(
            one_step_reduction(
                &env,
                &Proj("Boxed".to_string(), 1, Box::new(value))
            ),
            global("b"),
            "projecting field 1 of a concrete `mk(a,b)` must compute to `b`"
        );
    }

    #[test]
    fn test_projection_of_an_opaque_value_is_its_own_normal_form() {
        let env = eta_environment();
        let projection =
            Proj("Boxed".to_string(), 0, Box::new(Variable("bx".to_string(), 0)));

        assert_eq!(
            one_step_reduction(&env, &projection),
            projection,
            "a projection of an opaque value must stay stuck - re-expanding it is what would loop forever"
        );
    }

    #[test]
    fn test_match_on_an_opaque_single_constructor_scrutinee_now_reduces() {
        let env = eta_environment();
        let scrutinee = Variable("bx".to_string(), 0);
        // match bx with | mk(first, second) => second
        let term = Match(
            Box::new(scrutinee.clone()),
            vec![(
                apply(global("mk"), vec![global("first"), global("second")]),
                global("second"),
            )],
        );

        assert_eq!(
            one_step_reduction(&env, &term),
            Proj("Boxed".to_string(), 1, Box::new(scrutinee)),
            "a match over an opaque value of an eta-eligible type must reduce, binding each pattern variable to the corresponding projection"
        );
    }

    #[test]
    fn test_match_on_an_opaque_multi_constructor_scrutinee_stays_stuck() {
        let env = eta_environment();
        let term = Match(
            Box::new(Variable("n".to_string(), 0)),
            vec![
                (global("z"), global("base")),
                (
                    apply(global("s"), vec![global("nn")]),
                    global("step"),
                ),
            ],
        );

        assert_eq!(
            one_step_reduction(&env, &term),
            term,
            "eta must not fire for a multi-constructor type: `n` is genuinely not known to be either `z` or `s(..)`"
        );
    }
}
