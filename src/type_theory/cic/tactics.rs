use super::cic::CicTerm;
use super::cic::CicTerm::{Abstraction, Product};
use super::cic_utils::swap_body;
use crate::parser::api::Tactic::{self, By, Suppose};
use crate::type_theory::cic::cic::Cic;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Interactive, Kernel, Refiner, TypeTheory};

pub fn type_check_tactic(
    environment: &mut Environment<Cic>,
    tactic: &Tactic<CicTerm>,
    target: &CicTerm,
    partial_proof: &CicTerm,
) -> Result<(CicTerm, CicTerm), String> {
    match tactic {
        Suppose(ass_name, ass_type) => type_check_suppose(
            environment,
            target,
            partial_proof,
            ass_name,
            ass_type,
        ),
        By(proof_term) => {
            type_check_by(environment, target, partial_proof, proof_term)
        }
        _ => Err("TODO".to_string()),
    }
}
//
//
fn type_check_suppose(
    environment: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    ass_name: &str,
    ass_type: &CicTerm,
) -> Result<(CicTerm, CicTerm), String> {
    match target {
        Product(_, domain, codomain) => {
            if Cic::base_type_equality(ass_type, domain).is_ok() {
                let partial_proof = swap_body(partial_proof, &Abstraction(
                    ass_name.to_string(),
                    Box::new(ass_type.to_owned()),
                    Box::new(Cic::proof_hole())
                ));

                Ok((partial_proof, (**codomain).clone()))
            } else {
                Err(format!(
                    "{} has inconsistent type: expected {:?}, found {:?}", 
                    ass_name, domain, ass_type
                ))
            }
        },
        _ => {
            Err(format!(
                "Suppose tactic not allowed: current proof target {:?} is not a dependent product",
                target
            ))
        }
    }
}
//
//
fn type_check_by(
    environment: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    proof_term: &CicTerm,
) -> Result<(CicTerm, CicTerm), String> {
    let proof_type = Cic::type_check_term(proof_term, environment)?;

    if Cic::types_unify(environment, &proof_type, target) {
        Ok((swap_body(partial_proof, proof_term), Cic::empty_target()))
    } else {
        Err(format!(
            "Term type and target don't unify: target is {:?} while expression has type {:?}",
            target, proof_type
        ))
    }
}
//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::Tactic::Suppose,
        type_theory::{
            cic::{
                cic::{
                    Cic,
                    CicTerm::{Abstraction, Meta, Product, Sort, Variable},
                    GLOBAL_INDEX,
                },
                tactics::{
                    type_check_by, type_check_suppose, type_check_tactic,
                },
            },
            interface::{Interactive, TypeTheory},
        },
    };

    #[test]
    fn test_suppose() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();

        assert_eq!(
            type_check_suppose(
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
                nat.clone()
            )),
            "Suppose tactic checking isnt working as expected"
        );
        assert!(
            type_check_suppose(
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
            "Suppose tactic checking isnt working with missmatched variable names"
        );

        assert!(
            type_check_suppose(
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
            "Suppose tactic checking isnt working with unspecified assumption type"
        );

        assert!(
            type_check_tactic(
                &mut test_env,
                &Suppose("ass".to_string(), nat.clone()),
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole()
            )
            .is_ok(),
            "Top-level tactic checker doesnt support suppose"
        );

        assert!(
            type_check_suppose(
                &mut test_env,
                &nat,
                &Cic::proof_hole(),
                "ass",
                &nat.clone(),
            )
            .is_err(),
            "Suppose tactic checking accepts tactic with unassumable target"
        );
    }

    #[test]
    fn test_by() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let boolean = Variable("Bool".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("Bool", &Sort("TYPE".to_string()));
        test_env.add_to_context("n", &nat);

        let proof_term = Variable("n".to_string(), GLOBAL_INDEX);
        assert_eq!(
            type_check_by(&mut test_env, &nat, &Cic::proof_hole(), &proof_term),
            Ok((proof_term.clone(), Cic::empty_target())),
            "By tactic checking doesnt accept simple type inhabiting"
        );
        assert!(
            type_check_by(
                &mut test_env,
                &boolean,
                &Cic::proof_hole(),
                &proof_term
            )
            .is_err(),
            "By tactic checking accepts term with wrong type"
        );
    }
}
