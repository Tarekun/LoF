use super::fol::{
    Fol,
    FolFormula::{
        self, Arrow, Conjunction, Disjunction, Exist, ForAll, Not, Predicate,
    },
    FolTerm::{Abstraction, Application, Let, Tuple, Variable},
};
use crate::{
    misc::simple_map,
    type_theory::{
        commons::utils::generic_multiarg_fun_type,
        fol::fol::FolTerm,
        sup::sup::{
            SupFormula::{self, Clause},
            SupTerm,
        },
    },
};
use std::fmt::{self};

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

pub fn make_multiarg_fun_type(
    arg_types: &[(String, FolFormula)],
    base: &FolFormula,
) -> FolFormula {
    generic_multiarg_fun_type::<Fol, _>(
        arg_types,
        base,
        |_, arg_type, sub_type| Arrow(Box::new(arg_type), Box::new(sub_type)),
    )
}

pub fn make_multiarg_app(fun_name: &str, args: &[FolTerm]) -> FolTerm {
    args.into_iter()
        .fold(Variable(fun_name.to_string()), |acc, arg| {
            Application(Box::new(acc), Box::new(arg.clone()))
        })
}

pub fn get_application_components(
    app: &FolTerm,
) -> Result<(String, Vec<FolTerm>), String> {
    match app {
        Variable(fun_name) => Ok((fun_name.to_string(), vec![])),
        // TODO i have no idea how to handle anonymous functions
        Abstraction(_, _, _) => Ok(("".to_string(), vec![])),
        Application(left, right) => {
            let (fun_name, mut left_args) = get_application_components(left)?;
            left_args.push((**right).clone());
            Ok((fun_name, left_args))
        }
        _ => Err(format!("Term {:?} is not an application", app)),
    }
}

/// Given a `term` and a variable, returns a term where each instance of
/// `var_name` is substituted with `arg`
pub fn substitute_term(
    term: &FolTerm,
    target_name: &str,
    arg: &FolTerm,
) -> FolTerm {
    match term {
        Variable(var_name) => {
            if var_name == target_name {
                arg.clone()
            } else {
                term.clone()
            }
        }
        Abstraction(var_name, var_type, body) => {
            // the name is overridden in `body`'s scope
            if var_name != target_name {
                Abstraction(
                    var_name.to_string(),
                    Box::new(substitute_formula(var_type, target_name, arg)),
                    Box::new(substitute_term(body, target_name, arg)),
                )
            } else {
                term.to_owned()
            }
        }
        Application(left, right) => Application(
            Box::new(substitute_term(left, target_name, arg)),
            Box::new(substitute_term(right, target_name, arg)),
        ),
        Tuple(terms) => Tuple(simple_map(terms.to_owned(), |term| {
            substitute_term(&term, target_name, arg)
        })),
        Let(var_name, var_type, body, scope) => {
            let var_type = if var_type.is_some() {
                Some(substitute_formula(
                    &(**var_type).as_ref().unwrap(),
                    target_name,
                    arg,
                ))
            } else {
                None
            };
            let body = substitute_term(body, target_name, arg);
            // the name is overridden in `body`'s scope
            let scope = if var_name != target_name {
                substitute_term(scope, target_name, arg)
            } else {
                (**scope).to_owned()
            };

            Let(
                var_name.to_string(),
                Box::new(var_type),
                Box::new(body),
                Box::new(scope),
            )
        }
    }
}

pub fn substitute_formula(
    formula: &FolFormula,
    target_name: &str,
    arg: &FolTerm,
) -> FolFormula {
    match formula {
        Predicate(name, args) => Predicate(
            name.to_string(),
            simple_map(args.to_owned(), |term| {
                substitute_term(&term, target_name, arg)
            }),
        ),
        Arrow(left, right) => Arrow(
            Box::new(substitute_formula(left, target_name, arg)),
            Box::new(substitute_formula(right, target_name, arg)),
        ),
        Not(formula) => {
            Not(Box::new(substitute_formula(formula, target_name, arg)))
        }
        Conjunction(formulas) => {
            Conjunction(simple_map(formulas.to_owned(), |term| {
                substitute_formula(&term, target_name, arg)
            }))
        }
        Disjunction(formulas) => {
            Disjunction(simple_map(formulas.to_owned(), |term| {
                substitute_formula(&term, target_name, arg)
            }))
        }
        ForAll(var_name, var_type, body) => {
            // the name is overridden in `body`'s scope
            if var_name != target_name {
                ForAll(
                    var_name.to_string(),
                    Box::new(substitute_formula(var_type, target_name, arg)),
                    Box::new(substitute_formula(body, target_name, arg)),
                )
            } else {
                formula.to_owned()
            }
        }
        Exist(var_name, var_type, body) => {
            // the name is overridden in `body`'s scope
            if var_name != target_name {
                Exist(
                    var_name.to_string(),
                    Box::new(substitute_formula(var_type, target_name, arg)),
                    Box::new(substitute_formula(body, target_name, arg)),
                )
            } else {
                formula.to_owned()
            }
        }
    }
}

/// Given a formula `φ` expected to be in PNF, returns the same quantification over
/// the new formula `new_body`
pub fn swap_binded_formula(
    φ: &FolFormula,
    new_body: &FolFormula,
) -> FolFormula {
    match φ {
        ForAll(var_name, var_type, body) => ForAll(
            var_name.to_string(),
            var_type.to_owned(),
            Box::new(swap_binded_formula(body, new_body)),
        ),
        Exist(var_name, var_type, body) => Exist(
            var_name.to_string(),
            var_type.to_owned(),
            Box::new(swap_binded_formula(body, new_body)),
        ),
        _ => new_body.to_owned(),
    }
}

/// Removes implications and pushes negations to atomic predicates
pub fn negation_normal_form(φ: &FolFormula) -> FolFormula {
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
                // ¬(φ ∧ ψ ∧ γ) => ¬φ ∨ ¬ψ ∨ ¬γ
                Conjunction(formulas) => {
                    Disjunction(simple_map(formulas.to_owned(), |ψ| {
                        solver(&ψ, !negate)
                    }))
                }
                // ¬(φ ∨ ψ ∨ γ) => ¬φ ∧ ¬ψ ∧ ¬γ
                Disjunction(formulas) => {
                    Conjunction(simple_map(formulas.to_owned(), |ψ| {
                        solver(&ψ, !negate)
                    }))
                }
                ForAll(var_name, var_type, ψ) => {
                    let ψ = solver(&*ψ, !negate);
                    Exist(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(ψ),
                    )
                }
                Exist(var_name, var_type, ψ) => {
                    let ψ = solver(&*ψ, !negate);
                    ForAll(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(ψ),
                    )
                }
                _ => solver(ψ, !negate),
            },
            Conjunction(formulas) => {
                Conjunction(simple_map(formulas.to_owned(), |ψ| {
                    solver(&ψ, negate)
                }))
            }
            Disjunction(formulas) => {
                Disjunction(simple_map(formulas.to_owned(), |ψ| {
                    solver(&ψ, negate)
                }))
            }
            ForAll(var_name, var_type, ψ) => {
                let ψ = solver(ψ, negate);
                // im not recurring on the variable type as i assume its a sort
                ForAll(var_name.to_string(), var_type.to_owned(), Box::new(ψ))
            }
            Exist(var_name, var_type, ψ) => {
                let ψ = solver(ψ, negate);
                // im not recurring on the variable type as i assume its a sort
                Exist(var_name.to_string(), var_type.to_owned(), Box::new(ψ))
            }
        }
    }

    solver(φ, false)
}

/// Pulls quantifiers to the top level of the formula
pub fn prenex_normal_form(φ: &FolFormula) -> FolFormula {
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
                    swap_binded_formula(
                        &quantification,
                        &Exist(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(tmp_hole.clone()),
                        ),
                    ),
                );
                (quantification, resolved)
            }
            Exist(var_name, var_type, body) => {
                let (quantification, resolved) = solver(
                    body,
                    swap_binded_formula(
                        &quantification,
                        &ForAll(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(tmp_hole.clone()),
                        ),
                    ),
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
                let quantification = swap_binded_formula(
                    &quantification,
                    &ForAll(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(tmp_hole.clone()),
                    ),
                );
                solver(body, quantification)
            }
            Exist(var_name, var_type, body) => {
                quantification = swap_binded_formula(
                    &quantification,
                    &Exist(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(tmp_hole.clone()),
                    ),
                );
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

    let rectified = rectify_variables(&φ);
    let (quantification, quantifier_free) =
        solver(&rectified, Predicate("tmp".to_string(), vec![]));
    swap_binded_formula(&quantification, &quantifier_free)
}

/// Removes existential quantifiers via Skolemization
pub fn skolemize(φ: &FolFormula) -> FolFormula {
    fn solver(
        φ: &FolFormula,
        mut args: Vec<FolTerm>,
        witness_idx: i32,
    ) -> FolFormula {
        match φ {
            Exist(var_name, _, ψ) => {
                //TODO should i type the witness function?
                let skolem_witness =
                    make_multiarg_app(&format!("sw_{}", witness_idx), &args);
                let ψ = substitute_formula(ψ, var_name, &skolem_witness);
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

    solver(φ, vec![], 0)
}

/// Transforms the formula into a CNF logically equivalent one.
/// Returns the vector of (conjuncted) clauses
pub fn conjunction_normal_form(φ: &FolFormula) -> Vec<FolFormula> {
    /// Creates a flattened disjunction φ ∨ ψ keeping the AST height constant. Given
    /// * φ := α ∨ β
    /// * ψ := γ ∨ δ
    ///
    /// Instead of blindly returning (α ∨ β) ∨ (γ ∨ δ) constructs the flattened
    /// (ie in one vector) (α ∨ β ∨ γ ∨ δ)
    fn combine_disjunctions(φ: &FolFormula, ψ: &FolFormula) -> FolFormula {
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
                                distributed_result.push(distributed_literal);
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

    to_cnf(φ)
}

#[allow(non_snake_case)]
pub fn clausify(φ: &FolFormula) -> Result<Vec<SupFormula>, String> {
    fn clauses_to_sup(
        clauses: Vec<FolFormula>,
    ) -> Result<Vec<SupFormula>, String> {
        // collect errors across all clauses
        let mut errors = vec![];
        let mut sup_clauses = vec![];

        for clause in clauses {
            match clause_to_sup(clause) {
                Ok(clause) => sup_clauses.push(clause),
                Err(message) => errors.push(message),
            }
        }

        if errors.is_empty() {
            Ok(sup_clauses)
        } else {
            Err(errors.join("\n\n"))
        }
    }

    fn term_to_sup(term: FolTerm) -> Result<SupTerm, String> {
        match &term {
            Variable(name) => Ok(SupTerm::Variable(name.to_string())),
            Application(_, _) => {
                let (fun_name, args) = get_application_components(&term)?;
                let mut sup_args = vec![];
                for arg in args {
                    sup_args.push(term_to_sup(arg)?);
                }
                Ok(SupTerm::Application(fun_name, sup_args))
            }
            _ => Err(format!(
                "FOL term {:?} doesn't have a corresponding SUP term",
                term
            )),
        }
    }

    fn clause_to_sup(C: FolFormula) -> Result<SupFormula, String> {
        let C = match C {
            Predicate(name, args) => {
                let mut sup_args = vec![];
                for arg in args {
                    sup_args.push(term_to_sup(arg)?);
                }
                SupFormula::Atom(name, sup_args)
            }
            Disjunction(lits) => Clause(clauses_to_sup(lits)?),
            Not(D) => SupFormula::Not(Box::new(clause_to_sup(*D)?)),
            _ => {
                return Err(format!("Not a Clause: {:?}", C));
            }
        };

        Ok(C)
    }

    let nnf = negation_normal_form(φ);
    let pnf = prenex_normal_form(&nnf);
    let skolemized = skolemize(&pnf);
    let cnf = conjunction_normal_form(&skolemized);
    clauses_to_sup(cnf)
}
