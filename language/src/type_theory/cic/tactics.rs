use super::cic::CicTerm;
use super::cic::CicTerm::{Abstraction, Application, Match, Product, Variable};
use super::cic_utils::swap_body;
use crate::error::LofError;
use crate::parser::api::Tactic::{self, Apply, Exact, Induction, Intro};
use crate::type_theory::cic::cic::{Cic, GLOBAL_INDEX, PLACEHOLDER_DBI};
use crate::type_theory::cic::cic_utils::{
    apply_arguments, get_applied_function, get_arg_types, get_prod_innermost,
    is_instance_of, substitute,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{
    Interactive, Kernel, Reducer, Refiner, TypeInference, TypeTheory,
};

pub fn type_check_tactic(
    environment: &mut Environment<Cic>,
    tactic: &Tactic<CicTerm>,
    target: &CicTerm,
    partial_proof: &CicTerm,
) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
    match tactic {
        Intro(ass_name, ass_type) => type_check_intro(
            environment,
            target,
            partial_proof,
            ass_name,
            ass_type,
        ),
        Exact(proof_term) => {
            type_check_exact(environment, target, partial_proof, proof_term)
        }
        Apply(lemma) => {
            type_check_apply(environment, target, partial_proof, lemma)
        }
        Induction(var_name) => {
            type_check_induction(environment, target, partial_proof, var_name)
        }
        _ => Err(LofError::custom(format!(
            "Tactic {:?} currently not type-checkable in CIC",
            tactic
        ))),
    }
}
//
//
fn type_check_intro(
    environment: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    ass_name: &str,
    ass_type: &CicTerm,
) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
    match target {
        Product(_, domain, codomain) => {
            if Cic::base_type_equality(ass_type, domain).is_ok() {
                environment.add_to_context(ass_name, domain);
                let partial_proof = swap_body(partial_proof, &Abstraction(
                    ass_name.to_string(),
                    Box::new(ass_type.to_owned()),
                    Box::new(Cic::proof_hole())
                ));

                Ok((partial_proof, vec![(**codomain).clone()]))
            } else {
                Err(LofError::type_mismatch(
                    format!("assumption `{}`", ass_name),
                    domain,
                    ass_type,
                ))
            }
        },
        _ => {
            Err(LofError::custom(format!(
                "Intro tactic not allowed: current proof target {:?} is not a dependent product",
                target
            )))
        }
    }
}
//
//
fn type_check_exact(
    environment: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    proof_term: &CicTerm,
) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
    // TODO reevaluate if normalization is needed here: normal forms are already computed by CIC unification
    let proof_type = Cic::type_check_term(proof_term, environment)?;
    let proof_type_reduced = Cic::normalize_term(environment, &proof_type);
    let target_reduced = Cic::normalize_term(environment, target);

    Cic::types_unify(environment, &proof_type_reduced, &target_reduced)?;
    Ok((swap_body(partial_proof, proof_term), vec![]))
}
//
//
fn type_check_apply(
    _: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    lemma: &CicTerm,
) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
    // TODO see if i should be able to use a bigger term than the innermost as conclusion to unify
    let conclusion = get_prod_innermost(lemma);
    if Cic::type_unify(target, conclusion).is_ok() {
        let premises = get_arg_types(lemma);
        let new_proof = swap_body(
            partial_proof,
            &Application(
                Box::new(lemma.to_owned()),
                Box::new(Cic::proof_hole()),
            ),
        );

        Ok((new_proof, premises))
    } else {
        Err(LofError::unification_failure(target, conclusion))
    }
}
//
//
/// Proves `target` (which may depend on `var_name : I` for some inductive type
/// `I`) by case-splitting on `I`'s constructors. For each constructor a subgoal
/// is produced (`target` with `var_name` replaced by that constructor's
/// pattern), and for each recursive argument of the constructor an induction
/// hypothesis (`target` with `var_name` replaced by that argument) is bound
/// into the environment alongside the argument itself, ready for the
/// subsequent tactics that close each subgoal.
fn type_check_induction(
    environment: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    var_name: &str,
) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
    let var_type =
        environment.get_variable_type(var_name).ok_or_else(|| {
            LofError::custom(format!(
                "Induction tactic: variable `{}` not found in context",
                var_name
            ))
        })?;
    let type_name = match get_applied_function(&var_type) {
        Variable(name, _) => name,
        _ => {
            return Err(LofError::custom(format!(
                "Induction tactic: type {:?} of `{}` is not an inductive type",
                var_type, var_name
            )))
        }
    };

    let constructors = environment
        .get_constructors(&type_name)
        .cloned()
        .ok_or_else(|| {
            LofError::custom(format!(
                "Induction tactic: `{}` is not a registered inductive type",
                type_name
            ))
        })?;

    let mut branches = vec![];
    let mut subgoals = vec![];

    for (constr_name, constr_type) in &constructors {
        let arg_types = get_arg_types(constr_type);
        let n_args = arg_types.len();
        let mut pattern_args = vec![];

        for (index, arg_type) in arg_types.iter().enumerate() {
            let arg_name = if n_args == 1 {
                var_name.to_string()
            } else {
                format!("{}_{}", var_name, index)
            };
            environment.add_to_context(&arg_name, arg_type);
            pattern_args.push(Variable(arg_name.clone(), PLACEHOLDER_DBI));

            if is_instance_of(arg_type, &type_name) {
                let ih_name = if n_args == 1 {
                    format!("ih_{}", var_name)
                } else {
                    format!("ih_{}_{}", var_name, index)
                };
                let ih_type = substitute(
                    target,
                    var_name,
                    &Variable(arg_name, PLACEHOLDER_DBI),
                );
                environment.add_to_context(&ih_name, &ih_type);
            }
        }

        let pattern = apply_arguments(
            &Variable(constr_name.to_owned(), GLOBAL_INDEX),
            pattern_args,
        );
        let case_target = substitute(target, var_name, &pattern);

        subgoals.push(case_target);
        branches.push((pattern, Cic::proof_hole()));
    }
    // the subgoal stack is LIFO (see `solver` in commons/type_check.rs), so
    // reverse: the first-declared constructor's subgoal must be the last one
    // pushed in order to be the first one popped/addressed by the script
    subgoals.reverse();

    let match_term = Match(
        Box::new(Variable(var_name.to_string(), PLACEHOLDER_DBI)),
        branches,
    );
    let new_partial_proof = swap_body(partial_proof, &match_term);

    Ok((new_partial_proof, subgoals))
}

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::Tactic::{Apply, Induction, Intro},
        type_theory::{
            cic::{
                cic::{
                    Cic, CicTerm,
                    CicTerm::{
                        Abstraction, Application, Match, Meta, Product, Sort,
                        Variable,
                    },
                    GLOBAL_INDEX, PLACEHOLDER_DBI,
                },
                tactics::{
                    type_check_exact, type_check_induction, type_check_intro,
                    type_check_tactic,
                },
            },
            interface::{Interactive, TypeTheory},
        },
    };

    #[test]
    fn test_intro() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();

        assert_eq!(
            type_check_intro(
                &mut test_env,
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole(),
                "n",
                &nat.clone(),
            ),
            Ok((
                Abstraction(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Cic::proof_hole()),
                ),
                vec![nat.clone()]
            )),
            "Intro tactic checking isnt working as expected"
        );
        assert!(
            type_check_intro(
                &mut test_env,
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole(),
                "ass",
                &nat.clone(),
            ).is_ok(),
            "Intro tactic checking isnt working with missmatched variable names"
        );

        assert!(
            type_check_intro(
                &mut test_env,
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole(),
                "ass",
                &Meta(0),
            ).is_ok(),
            "Intro tactic checking isnt working with unspecified assumption type"
        );

        assert!(
            type_check_tactic(
                &mut test_env,
                &Intro("ass".to_string(), nat.clone()),
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole()
            )
            .is_ok(),
            "Top-level tactic checker doesnt support intro"
        );

        assert!(
            type_check_intro(
                &mut test_env,
                &nat,
                &Cic::proof_hole(),
                "ass",
                &nat.clone(),
            )
            .is_err(),
            "Intro tactic checking accepts tactic with unassumable target"
        );
    }

    #[test]
    fn test_exact() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let boolean = Variable("Bool".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("Bool", &Sort("TYPE".to_string()));
        test_env.add_to_context("n", &nat);

        let proof_term = Variable("n".to_string(), GLOBAL_INDEX);
        assert_eq!(
            type_check_exact(
                &mut test_env,
                &nat,
                &Cic::proof_hole(),
                &proof_term
            ),
            Ok((proof_term.clone(), vec![])),
            "Exact tactic checking doesnt accept simple type inhabiting"
        );
        assert!(
            type_check_exact(
                &mut test_env,
                &boolean,
                &Cic::proof_hole(),
                &proof_term
            )
            .is_err(),
            "Exact tactic checking accepts term with wrong type"
        );
    }

    #[test]
    fn test_apply() {
        let mut test_env = Cic::default_environment();
        let premise1 = Variable("Premise1".to_string(), GLOBAL_INDEX);
        let premise2 = Variable("Premise2".to_string(), GLOBAL_INDEX);
        let conclusion = Variable("Conclusion".to_string(), GLOBAL_INDEX);
        let simple_implication = Product(
            "_".to_string(),
            Box::new(premise1.clone()),
            Box::new(conclusion.clone()),
        );
        let hole = Cic::proof_hole();

        let (proof, subgoals) = Cic::type_check_tactic(
            &mut test_env,
            &Apply(simple_implication.clone()),
            &conclusion,
            &hole,
        )
        .unwrap();
        assert_eq!(
            proof,
            Application(Box::new(simple_implication), Box::new(hole.clone())),
            "The constructed partial proof is not the expected one"
        );
        assert_eq!(subgoals, vec![premise1.clone()], "The returned subgoals dont match the premises of the applied implication");

        let double_implication = Product(
            "_".to_string(),
            Box::new(premise1.clone()),
            Box::new(Product(
                "_".to_string(),
                Box::new(premise2.clone()),
                Box::new(conclusion.clone()),
            )),
        );
        let (_, subgoals) = Cic::type_check_tactic(
            &mut test_env,
            &Apply(double_implication.clone()),
            &conclusion,
            &hole,
        )
        .unwrap();
        assert_eq!(
            subgoals,
            vec![premise1, premise2],
            "Apply tactic doesnt track all premises of the applied lemma"
        );
    }

    #[test]
    fn test_intro_binds_context() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();

        assert_eq!(
            test_env.get_variable_type("n"),
            None,
            "Sanity check: `n` isnt bound before intro runs"
        );

        let _ = type_check_intro(
            &mut test_env,
            &Product(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
            &Cic::proof_hole(),
            "n",
            &nat.clone(),
        );

        assert_eq!(
            test_env.get_variable_type("n"),
            Some(nat),
            "Intro tactic must bind the introduced variable into the environment context"
        );
    }

    #[test]
    fn test_induction() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let succ_type = Product(
            "_".to_string(),
            Box::new(nat.clone()),
            Box::new(nat.clone()),
        );
        let predicate = |arg: CicTerm| {
            Application(
                Box::new(Variable("P".to_string(), GLOBAL_INDEX)),
                Box::new(arg),
            )
        };

        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("z", &nat);
        test_env.add_to_context("s", &succ_type);
        test_env.add_to_context("n", &nat);
        test_env.add_constructor_store(
            "Nat",
            vec![
                ("z".to_string(), nat.clone()),
                ("s".to_string(), succ_type.clone()),
            ],
        );

        let target = predicate(Variable("n".to_string(), PLACEHOLDER_DBI));

        let (proof, subgoals) = type_check_induction(
            &mut test_env,
            &target,
            &Cic::proof_hole(),
            "n",
        )
        .expect(
            "Induction tactic should succeed on a registered inductive type",
        );

        let z_pattern = Variable("z".to_string(), GLOBAL_INDEX);
        let s_pattern = Application(
            Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
            Box::new(Variable("n".to_string(), PLACEHOLDER_DBI)),
        );
        assert_eq!(
            proof,
            Match(
                Box::new(Variable("n".to_string(), PLACEHOLDER_DBI)),
                vec![
                    (z_pattern.clone(), Cic::proof_hole()),
                    (s_pattern.clone(), Cic::proof_hole()),
                ],
            ),
            "Induction tactic must produce a Match with one holed branch per constructor, in declaration order"
        );

        assert_eq!(
            subgoals,
            vec![predicate(s_pattern.clone()), predicate(z_pattern.clone())],
            "Induction tactic must push subgoals reversed so the first-declared constructor is addressed first"
        );

        assert_eq!(
            test_env.get_variable_type("ih_n"),
            Some(predicate(Variable("n".to_string(), PLACEHOLDER_DBI))),
            "Induction tactic must bind the induction hypothesis for the recursive case into context"
        );

        assert!(
            type_check_tactic(
                &mut test_env,
                &Induction("n".to_string()),
                &target,
                &Cic::proof_hole(),
            )
            .is_ok(),
            "Top-level tactic checker doesnt support induction"
        );
    }
}
