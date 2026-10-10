use crate::{
    error::LofError,
    misc::simple_map,
    type_theory::grammars::{
        fol::{
            FolFormula::{
                Arrow, Conjunction, Disjunction, Exist, ForAll, Not, Predicate,
            },
            FolTerm::{Abstraction, Application, Let, Tuple, Variable},
        },
        traits::NamedSubstitution,
    },
};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
/// A term of typed First Order Logic. Next to plain `Variable`s and curried
/// `Application`s it contains the lambda `Abstraction`, `Tuple`s and `Let`
/// definitions
pub enum FolTerm {
    /// var_name
    Variable(String),
    /// var_name, var_type, body
    Abstraction(String, Box<FolFormula>, Box<FolTerm>),
    /// fun, arg
    Application(Box<FolTerm>, Box<FolTerm>),
    /// [terms]
    Tuple(Vec<FolTerm>),
    /// var_name, var_type, body, scope
    Let(String, Box<Option<FolFormula>>, Box<FolTerm>, Box<FolTerm>),
}

#[derive(Clone, PartialEq)]
/// A formula of typed First Order Logic (FOL), with `Predicate`
/// application as atoms, the usual connectives and typed quantifiers
pub enum FolFormula {
    //TODO add predicate application
    /// pred_name, [args]
    Predicate(String, Vec<FolTerm>),
    /// assumption, conclusion
    Arrow(Box<FolFormula>, Box<FolFormula>),
    Not(Box<FolFormula>),
    /// [conjuncts]
    Conjunction(Vec<FolFormula>),
    /// [disjuncts]
    Disjunction(Vec<FolFormula>),
    /// var_name, var_type, formula
    ForAll(String, Box<FolFormula>, Box<FolFormula>),
    /// var_name, var_type, formula
    Exist(String, Box<FolFormula>, Box<FolFormula>),
}

//############################# DEBUG LOGS
impl FolFormula {
    pub fn to_string(&self) -> String {
        match self {
            Predicate(name, args) => format!("{}({:?})", name, args),
            Not(f) => format!("¬{}", f.to_string()),
            Arrow(l, r) => format!("{} → {}", l.to_string(), r.to_string()),
            Conjunction(fs) => fs
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join("∧"),
            Disjunction(fs) => fs
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join("∨"),
            ForAll(var, ty, f) => {
                format!("∀{}:{}. {}", var, ty.to_string(), f.to_string())
            }
            Exist(var, ty, f) => {
                format!("∃{}:{}. {}", var, ty.to_string(), f.to_string())
            }
        }
    }
    pub fn parethesized(&self) -> String {
        match self {
            Predicate(name, args) => format!("{}({:?})", name, args),
            Not(f) => format!("¬({})", f.parethesized()),
            Arrow(l, r) => {
                format!("({} → {})", l.parethesized(), r.parethesized())
            }
            Conjunction(fs) => {
                let tmp = fs
                    .iter()
                    .map(|f| f.parethesized())
                    .collect::<Vec<_>>()
                    .join("∧");
                format!("({})", tmp)
            }
            Disjunction(fs) => {
                let tmp = fs
                    .iter()
                    .map(|f| f.parethesized())
                    .collect::<Vec<_>>()
                    .join("∨");
                format!("({})", tmp)
            }
            ForAll(var, ty, f) => {
                format!(
                    "∀{}:{}. ({})",
                    var,
                    ty.parethesized(),
                    f.parethesized()
                )
            }
            Exist(var, ty, f) => {
                format!(
                    "∃{}:{}. ({})",
                    var,
                    ty.parethesized(),
                    f.parethesized()
                )
            }
        }
    }
}
impl fmt::Display for FolFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}
impl fmt::Debug for FolFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.parethesized())
    }
}
//############################# DEBUG LOGS
//
//
//############################# LOOKUPS

impl FolTerm {
    /// Given a curried application, returns the name of the applied function
    /// together with the ordered vector of its arguments
    pub fn get_application_components(
        &self,
    ) -> Result<(String, Vec<FolTerm>), LofError> {
        match self {
            Variable(fun_name) => Ok((fun_name.to_string(), vec![])),
            // TODO i have no idea how to handle anonymous functions
            Abstraction(_, _, _) => Ok(("".to_string(), vec![])),
            Application(left, right) => {
                let (fun_name, mut left_args) =
                    left.get_application_components()?;
                left_args.push((**right).clone());
                Ok((fun_name, left_args))
            }
            _ => Err(LofError::custom(format!(
                "Term {:?} is not an application",
                self
            ))),
        }
    }
}

//############################# LOOKUPS
//
//
//############################# EXPRESSIONS MANIPULATION

impl FolTerm {
    /// Returns the curried application of `fun_name` to `args`
    pub fn make_multiarg_app(fun_name: &str, args: &[FolTerm]) -> FolTerm {
        args.into_iter()
            .fold(Variable(fun_name.to_string()), |acc, arg| {
                Application(Box::new(acc), Box::new(arg.clone()))
            })
    }
}

impl NamedSubstitution<FolTerm> for FolTerm {
    fn substitute_name(&mut self, target_name: &str, arg: &FolTerm) {
        match self {
            Variable(var_name) => {
                if var_name == target_name {
                    *self = arg.to_owned();
                }
            }
            Abstraction(var_name, var_type, body) => {
                // the name is overridden in `body`'s scope
                if var_name != target_name {
                    var_type.substitute_name(target_name, arg);
                    body.substitute_name(target_name, arg);
                }
            }
            Application(left, right) => {
                left.substitute_name(target_name, arg);
                right.substitute_name(target_name, arg);
            }
            Tuple(terms) => terms
                .iter_mut()
                .for_each(|t| t.substitute_name(target_name, arg)),
            Let(var_name, var_type, body, scope) => {
                if let Some(var_type) = &mut **var_type {
                    var_type.substitute_name(target_name, arg);
                }
                body.substitute_name(target_name, arg);
                // the name is overridden in `body`'s scope
                if var_name != target_name {
                    scope.substitute_name(target_name, arg);
                }
            }
        }
    }
}

impl FolFormula {
    /// Given `self` expected to be in PNF, returns the same quantification over
    /// the new formula `new_body`
    pub fn swap_binded_formula(&self, new_body: &FolFormula) -> FolFormula {
        match self {
            ForAll(var_name, var_type, body) => ForAll(
                var_name.to_string(),
                var_type.to_owned(),
                Box::new(body.swap_binded_formula(new_body)),
            ),
            Exist(var_name, var_type, body) => Exist(
                var_name.to_string(),
                var_type.to_owned(),
                Box::new(body.swap_binded_formula(new_body)),
            ),
            _ => new_body.to_owned(),
        }
    }
}

impl NamedSubstitution<FolTerm> for FolFormula {
    fn substitute_name(&mut self, target_name: &str, arg: &FolTerm) {
        match self {
            Predicate(_, args) => args
                .iter_mut()
                .for_each(|t| t.substitute_name(target_name, arg)),
            Arrow(left, right) => {
                left.substitute_name(target_name, arg);
                right.substitute_name(target_name, arg);
            }
            Not(formula) => formula.substitute_name(target_name, arg),
            Conjunction(formulas) | Disjunction(formulas) => formulas
                .iter_mut()
                .for_each(|f| f.substitute_name(target_name, arg)),
            ForAll(var_name, var_type, body)
            | Exist(var_name, var_type, body) => {
                // the name is overridden in `body`'s scope
                if var_name != target_name {
                    var_type.substitute_name(target_name, arg);
                    body.substitute_name(target_name, arg);
                }
            }
        }
    }
}

//############################# EXPRESSIONS MANIPULATION
//
//
//############################# NORMAL FORMS

impl FolFormula {
    /// Removes implications and pushes negations to atomic predicates
    pub fn negation_normal_form(&self) -> FolFormula {
        fn solver(φ: &FolFormula, negate: bool) -> FolFormula {
            match φ {
                Predicate(_, _) => {
                    if negate {
                        Not(Box::new(φ.to_owned()))
                    } else {
                        φ.to_owned()
                    }
                }
                Arrow(assumption, conclusion) => {
                    let not_assumption = solver(assumption, !negate);
                    let conclusion = solver(conclusion, negate);
                    Disjunction(vec![not_assumption, conclusion])
                }
                Not(ψ) => match &**ψ {
                    // simplify double negation
                    Not(gamma) => solver(&*gamma, negate),
                    _ => solver(ψ, !negate),
                },
                Conjunction(formulas) => {
                    let solved =
                        simple_map(formulas.to_owned(), |ψ| solver(&ψ, negate));
                    if negate {
                        Disjunction(solved)
                    } else {
                        Conjunction(solved)
                    }
                }
                Disjunction(formulas) => {
                    let solved =
                        simple_map(formulas.to_owned(), |ψ| solver(&ψ, negate));
                    if negate {
                        Conjunction(solved)
                    } else {
                        Disjunction(solved)
                    }
                }
                ForAll(var_name, var_type, ψ) => {
                    // im not recurring on the variable type as i assume its a sort
                    let ψ = solver(ψ, negate);
                    if negate {
                        Exist(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(ψ),
                        )
                    } else {
                        ForAll(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(ψ),
                        )
                    }
                }
                Exist(var_name, var_type, ψ) => {
                    // im not recurring on the variable type as i assume its a sort
                    let ψ = solver(ψ, negate);
                    if negate {
                        ForAll(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(ψ),
                        )
                    } else {
                        Exist(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(ψ),
                        )
                    }
                }
            }
        }

        solver(self, false)
    }

    /// Pulls quantifiers to the top level of the formula
    pub fn prenex_normal_form(&self) -> FolFormula {
        /// Renames bound variables to fresh names to avoid clashes
        fn rectify_variables(φ: &FolFormula) -> FolFormula {
            φ.to_owned()
        }

        fn handle_arrow_components(
            φ: &FolFormula,
            quantification: FolFormula,
        ) -> (FolFormula, FolFormula) {
            let tmp_hole = Predicate("tmp".to_string(), vec![]);
            match φ {
                ForAll(var_name, var_type, body) => {
                    let (quantification, resolved) = solver(
                        body,
                        quantification.swap_binded_formula(&Exist(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(tmp_hole.clone()),
                        )),
                    );
                    (quantification, resolved)
                }
                Exist(var_name, var_type, body) => {
                    let (quantification, resolved) = solver(
                        body,
                        quantification.swap_binded_formula(&ForAll(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(tmp_hole.clone()),
                        )),
                    );
                    (quantification, resolved)
                }
                _ => (quantification, φ.to_owned()),
            }
        }

        fn solver(
            φ: &FolFormula,
            mut quantification: FolFormula,
        ) -> (FolFormula, FolFormula) {
            let tmp_hole = Predicate("tmp".to_string(), vec![]);
            // TODO quantifiers might need to recur on a conjunct of body and the existance of a variable of the given type
            match φ {
                // expected to be in NNF so ¬ is already a literal (base case)
                Predicate(_, _) | Not(_) => (quantification, φ.to_owned()),
                ForAll(var_name, var_type, body) => {
                    let quantification =
                        quantification.swap_binded_formula(&ForAll(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(tmp_hole.clone()),
                        ));
                    solver(body, quantification)
                }
                Exist(var_name, var_type, body) => {
                    quantification =
                        quantification.swap_binded_formula(&Exist(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(tmp_hole.clone()),
                        ));
                    solver(body, quantification)
                }
                Conjunction(formulas) => {
                    let mut quantifier_free = vec![];
                    for ψ in formulas {
                        let (q, ψ) = solver(ψ, quantification);
                        quantification = q;
                        quantifier_free.push(ψ);
                    }

                    (quantification, Conjunction(quantifier_free))
                }
                Disjunction(formulas) => {
                    let mut quantifier_free = vec![];
                    for ψ in formulas {
                        let (q, ψ) = solver(ψ, quantification);
                        quantification = q;
                        quantifier_free.push(ψ);
                    }

                    (quantification, Disjunction(quantifier_free))
                }
                Arrow(assumption, conclusion) => {
                    let (q, assumption) =
                        handle_arrow_components(assumption, quantification);
                    quantification = q;
                    let (q, conclusion) =
                        handle_arrow_components(conclusion, quantification);
                    quantification = q;

                    (
                        quantification,
                        Arrow(Box::new(assumption), Box::new(conclusion)),
                    )
                }
            }
        }

        let rectified = rectify_variables(self);
        let (quantification, quantifier_free) =
            solver(&rectified, Predicate("tmp".to_string(), vec![]));
        quantification.swap_binded_formula(&quantifier_free)
    }

    /// Removes existential quantifiers via Skolemization
    pub fn skolemize(&self) -> FolFormula {
        fn solver(
            φ: &FolFormula,
            mut args: Vec<FolTerm>,
            witness_idx: i32,
        ) -> FolFormula {
            match φ {
                Exist(var_name, _, ψ) => {
                    //TODO should i type the witness function?
                    let skolem_witness = FolTerm::make_multiarg_app(
                        &format!("sw_{}", witness_idx),
                        &args,
                    );
                    let mut ψ = (**ψ).clone();
                    ψ.substitute_name(var_name, &skolem_witness);
                    solver(&ψ, args, witness_idx + 1)
                }
                ForAll(var_name, var_type, ψ) => {
                    args.push(Variable(var_name.to_string()));

                    ForAll(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(solver(ψ, args, witness_idx)),
                    )
                }
                Conjunction(subformulas) => {
                    Conjunction(simple_map(subformulas.to_owned(), |ψ| {
                        solver(&ψ, args.clone(), witness_idx)
                    }))
                }
                Disjunction(subformulas) => {
                    Disjunction(simple_map(subformulas.to_owned(), |ψ| {
                        solver(&ψ, args.clone(), witness_idx)
                    }))
                }
                Arrow(left, right) => Arrow(
                    Box::new(solver(left, args.clone(), witness_idx)),
                    Box::new(solver(right, args, witness_idx)),
                ),
                Not(ψ) => Not(Box::new(solver(ψ, args, witness_idx))),
                Predicate(_, _) => φ.to_owned(),
            }
        }

        solver(self, vec![], 0)
    }

    /// Transforms the formula into a CNF logically equivalent one.
    /// Returns the vector of (conjuncted) clauses
    pub fn conjunction_normal_form(&self) -> Vec<FolFormula> {
        /// Creates a flattened disjunction φ ∨ ψ keeping the AST height constant. Given
        /// * φ := α ∨ β
        /// * ψ := γ ∨ δ
        ///
        /// Instead of blindly returning (α ∨ β) ∨ (γ ∨ δ) constructs the flattened
        /// (ie in one vector) (α ∨ β ∨ γ ∨ δ)
        fn combine_disjunctions(
            φ: &FolFormula, ψ: &FolFormula
        ) -> FolFormula {
            let mut subformulas = match φ {
                Disjunction(left) => left.to_owned(),
                _ => vec![φ.to_owned()],
            };
            if let Disjunction(right) = ψ {
                subformulas.extend(right.to_vec());
            } else {
                subformulas.push(ψ.to_owned());
            }

            Disjunction(subformulas)
        }

        fn to_cnf(φ: &FolFormula) -> Vec<FolFormula> {
            match φ {
                Predicate(_, _) | Not(_) => vec![φ.clone()],
                Conjunction(formulas) => {
                    formulas.iter().flat_map(|ψ| to_cnf(ψ)).collect()
                }
                Disjunction(formulas) => {
                    let mut result = vec![];
                    for ψ in formulas {
                        let ψ_clauses = to_cnf(ψ);

                        if result.is_empty() {
                            result.extend(ψ_clauses);
                        } else {
                            let mut distributed_result = vec![];
                            for literal in result {
                                for gamma in &ψ_clauses {
                                    let distributed_literal =
                                        combine_disjunctions(&literal, gamma);
                                    distributed_result
                                        .push(distributed_literal);
                                }
                            }
                            result = distributed_result;
                        }
                    }

                    result
                }
                ForAll(_, _, ψ) => to_cnf(ψ),
                Exist(_, _, _) => unreachable!(
                    "Existential quantifiers should be removed by skolemization"
                ),
                Arrow(_, _) => unreachable!(
                    "Implications should be removed by negation normal form"
                ),
            }
        }

        to_cnf(self)
    }
}

//############################# NORMAL FORMS

#[cfg(test)]
#[path = "../../tests/type_theory/grammars/fol.rs"]
mod tests;
