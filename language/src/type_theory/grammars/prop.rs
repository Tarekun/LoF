use crate::{
    error::LofError,
    type_theory::grammars::{
        cnf::CnfFormula,
        prop::{
            PropFormula::{
                Arrow, Atom, Bottom, Conjunction, Disjunction, Not, Top,
            },
            PropTerm::{Abstraction, Application, Let, Tuple, Variable},
        },
        traits::{Complement, NamedSubstitution, SyntacticalEq, ToCnfFormula},
    },
};
use std::collections::{BTreeSet, HashMap};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
/// A proof term of Propositional Logic. Next to plain `Variable`s and curried
/// `Application`s it contains the lambda `Abstraction`, `Tuple`s and `Let`
/// definitions, all annotated with formulas (types)
pub enum PropTerm {
    /// var_name
    Variable(String),
    /// var_name, var_type, body
    Abstraction(String, Box<PropFormula>, Box<PropTerm>),
    /// fun, arg
    Application(Box<PropTerm>, Box<PropTerm>),
    /// [terms]
    Tuple(Vec<PropTerm>),
    /// var_name, var_type, body, scope
    Let(
        String,
        Box<Option<PropFormula>>,
        Box<PropTerm>,
        Box<PropTerm>,
    ),
}

#[derive(Clone, PartialEq)]
/// A formula of Propositional Logic, with propositional variables as
/// `Atom`s, the constants `Top` and `Bottom` and the full set of connectives.
/// An empty `Conjunction` is equivalent to `Top`, an empty `Disjunction`
/// to `Bottom`
pub enum PropFormula {
    /// atom_name
    Atom(String),
    /// ⊤
    Top,
    /// ⊥
    Bottom,
    Not(Box<PropFormula>),
    /// [conjuncts]
    Conjunction(Vec<PropFormula>),
    /// [disjuncts]
    Disjunction(Vec<PropFormula>),
    /// assumption, conclusion
    Arrow(Box<PropFormula>, Box<PropFormula>),
}

//############################# DEBUG LOGS
impl PropFormula {
    /// Binding strength of the top level connective, higher binds tighter
    fn precedence(&self) -> u8 {
        match self {
            Arrow(_, _) => 2,
            Disjunction(fs) if !fs.is_empty() => 3,
            Conjunction(fs) if !fs.is_empty() => 4,
            _ => 5,
        }
    }

    /// Prints `self` wrapped in parentheses iff its connective doesn't
    /// bind at least as tight as `min_precedence`
    fn to_string_within(&self, min_precedence: u8) -> String {
        if self.precedence() < min_precedence {
            format!("({})", self)
        } else {
            self.to_string()
        }
    }

    /// Prints the formula with every connective explicitly parenthesized
    pub fn parenthesized(&self) -> String {
        let join = |fs: &[PropFormula], sep: &str| {
            fs.iter()
                .map(|f| f.parenthesized())
                .collect::<Vec<_>>()
                .join(sep)
        };
        match self {
            Atom(name) => name.to_string(),
            Top => "⊤".to_string(),
            Bottom => "⊥".to_string(),
            Not(f) => format!("¬({})", f.parenthesized()),
            Conjunction(fs) if fs.is_empty() => "⊤".to_string(),
            Conjunction(fs) => format!("({})", join(fs, " ∧ ")),
            Disjunction(fs) if fs.is_empty() => "⊥".to_string(),
            Disjunction(fs) => format!("({})", join(fs, " ∨ ")),
            Arrow(l, r) => {
                format!("({} → {})", l.parenthesized(), r.parenthesized())
            }
        }
    }
}
impl fmt::Display for PropFormula {
    /// Prints the formula with the minimal amount of parentheses, given
    /// the precedence ¬ > ∧ > ∨ > → > ↔ and → being right associative.
    /// Nested conjunctions/disjunctions are parenthesized to keep the
    /// structure of the AST visible
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let join = |fs: &[PropFormula], sep: &str, min_precedence: u8| {
            fs.iter()
                .map(|f| f.to_string_within(min_precedence))
                .collect::<Vec<_>>()
                .join(sep)
        };
        match self {
            Atom(name) => write!(f, "{}", name),
            Top => write!(f, "⊤"),
            Bottom => write!(f, "⊥"),
            Not(psi) => write!(f, "¬{}", psi.to_string_within(5)),
            Conjunction(fs) if fs.is_empty() => write!(f, "⊤"),
            Conjunction(fs) => write!(f, "{}", join(fs, " ∧ ", 5)),
            Disjunction(fs) if fs.is_empty() => write!(f, "⊥"),
            Disjunction(fs) => write!(f, "{}", join(fs, " ∨ ", 4)),
            Arrow(l, r) => write!(
                f,
                "{} → {}",
                l.to_string_within(3),
                r.to_string_within(2)
            ),
        }
    }
}
impl fmt::Debug for PropFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.parenthesized())
    }
}
//############################# DEBUG LOGS
//
//
//############################# CHECKS ON EXPRESSIONS

impl PropFormula {
    /// Returns `true` iff `self` is an atom or the negation of an atom
    pub fn is_literal(&self) -> bool {
        match self {
            Atom(_) => true,
            Not(psi) => matches!(**psi, Atom(_)),
            _ => false,
        }
    }

    /// Returns `true` iff `self` is a literal, a disjunction of literals or
    /// the empty clause `Bottom`
    pub fn is_clause(&self) -> bool {
        match self {
            Bottom => true,
            Disjunction(lits) => lits.iter().all(|lit| lit.is_literal()),
            _ => self.is_literal(),
        }
    }

    /// Returns `true` iff `self` is in negation normal form, ie it contains
    /// no implications/equivalences and negations only wrap atoms
    pub fn is_nnf(&self) -> bool {
        match self {
            Atom(_) | Top | Bottom => true,
            Not(_) => self.is_literal(),
            Conjunction(fs) | Disjunction(fs) => fs.iter().all(|f| f.is_nnf()),
            Arrow(_, _) => false,
        }
    }

    /// Returns `true` iff `self` is a clause, a conjunction of clauses or
    /// the empty conjunction `Top`
    pub fn is_cnf(&self) -> bool {
        match self {
            Top => true,
            Conjunction(clauses) => clauses.iter().all(|c| c.is_clause()),
            _ => self.is_clause(),
        }
    }

    /// Check if two literals are (syntactically) complements
    fn are_complements(&self, lit2: &PropFormula) -> bool {
        match (self, lit2) {
            (Atom(_), Not(q)) => **q == *self,
            (Not(p), Atom(_)) => **p == *lit2,
            _ => false,
        }
    }
}

//############################# CHECKS ON EXPRESSIONS
//
//
//############################# LOOKUPS

impl PropTerm {
    /// Given a curried application, returns the name of the applied function
    /// together with the ordered vector of its arguments
    pub fn get_application_components(
        &self,
    ) -> Result<(String, Vec<PropTerm>), LofError> {
        match self {
            Variable(fun_name) => Ok((fun_name.to_string(), vec![])),
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

    /// Returns the names of the variables occurring unbound in `self`
    pub fn free_variables(&self) -> BTreeSet<String> {
        match self {
            Variable(name) => BTreeSet::from([name.to_string()]),
            Abstraction(var_name, _, body) => {
                let mut free = body.free_variables();
                free.remove(var_name);
                free
            }
            Application(left, right) => {
                let mut free = left.free_variables();
                free.extend(right.free_variables());
                free
            }
            Tuple(terms) => {
                terms.iter().flat_map(|t| t.free_variables()).collect()
            }
            Let(var_name, _, body, scope) => {
                let mut free = scope.free_variables();
                free.remove(var_name);
                free.extend(body.free_variables());
                free
            }
        }
    }
}

impl PropFormula {
    /// Returns the names of all the atoms occurring in `self`
    pub fn atoms(&self) -> BTreeSet<String> {
        match self {
            Atom(name) => BTreeSet::from([name.to_string()]),
            Top | Bottom => BTreeSet::new(),
            Not(psi) => psi.atoms(),
            Conjunction(fs) | Disjunction(fs) => {
                fs.iter().flat_map(|f| f.atoms()).collect()
            }
            Arrow(l, r) => {
                let mut atoms = l.atoms();
                atoms.extend(r.atoms());
                atoms
            }
        }
    }

    /// Computes the truth value of `self` under `valuation`. Fails if an
    /// atom of `self` is not assigned by `valuation`
    pub fn evaluate(
        &self,
        valuation: &HashMap<String, bool>,
    ) -> Result<bool, LofError> {
        Ok(match self {
            Atom(name) => *valuation
                .get(name)
                .ok_or_else(|| LofError::unbound_variable(name))?,
            Top => true,
            Bottom => false,
            Not(psi) => !psi.evaluate(valuation)?,
            Conjunction(fs) => {
                for f in fs {
                    if !f.evaluate(valuation)? {
                        return Ok(false);
                    }
                }
                true
            }
            Disjunction(fs) => {
                for f in fs {
                    if f.evaluate(valuation)? {
                        return Ok(true);
                    }
                }
                false
            }
            Arrow(l, r) => !l.evaluate(valuation)? || r.evaluate(valuation)?,
        })
    }
}

//############################# LOOKUPS
//
//
//############################# EXPRESSIONS MANIPULATION

impl PropTerm {
    /// Returns the curried application of `fun_name` to `args`
    pub fn make_multiarg_app(fun_name: &str, args: &[PropTerm]) -> PropTerm {
        args.iter()
            .fold(Variable(fun_name.to_string()), |acc, arg| {
                Application(Box::new(acc), Box::new(arg.clone()))
            })
    }
}

impl NamedSubstitution<PropTerm> for PropTerm {
    /// Returns a new term identical to `self` where each instance of
    /// `target_name` is substituted with `arg`
    fn substitute_name(&self, target_name: &str, arg: &PropTerm) -> PropTerm {
        match self {
            Variable(var_name) => {
                if var_name == target_name {
                    arg.clone()
                } else {
                    self.clone()
                }
            }
            Abstraction(var_name, var_type, body) => {
                // the name is overridden in `body`'s scope
                if var_name != target_name {
                    Abstraction(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(body.substitute_name(target_name, arg)),
                    )
                } else {
                    self.to_owned()
                }
            }
            Application(left, right) => Application(
                Box::new(left.substitute_name(target_name, arg)),
                Box::new(right.substitute_name(target_name, arg)),
            ),
            Tuple(terms) => Tuple(
                terms
                    .iter()
                    .map(|term| term.substitute_name(target_name, arg))
                    .collect(),
            ),
            Let(var_name, var_type, body, scope) => {
                let body = body.substitute_name(target_name, arg);
                // the name is overridden in `body`'s scope
                let scope = if var_name != target_name {
                    scope.substitute_name(target_name, arg)
                } else {
                    (**scope).to_owned()
                };

                Let(
                    var_name.to_string(),
                    var_type.to_owned(),
                    Box::new(body),
                    Box::new(scope),
                )
            }
        }
    }
}

impl NamedSubstitution<PropFormula> for PropTerm {
    /// Returns a new term identical to `self` where each instance of the
    /// atom `target_name` in type annotations is substituted with `arg`
    fn substitute_name(
        &self,
        target_name: &str,
        arg: &PropFormula,
    ) -> PropTerm {
        match self {
            Variable(_) => self.to_owned(),
            Abstraction(var_name, var_type, body) => Abstraction(
                var_name.to_string(),
                Box::new(var_type.substitute_name(target_name, arg)),
                Box::new(body.substitute_name(target_name, arg)),
            ),
            Application(left, right) => Application(
                Box::new(left.substitute_name(target_name, arg)),
                Box::new(right.substitute_name(target_name, arg)),
            ),
            Tuple(terms) => Tuple(
                terms
                    .iter()
                    .map(|term| term.substitute_name(target_name, arg))
                    .collect(),
            ),
            Let(var_name, var_type, body, scope) => Let(
                var_name.to_string(),
                Box::new(
                    (**var_type)
                        .as_ref()
                        .map(|t| t.substitute_name(target_name, arg)),
                ),
                Box::new(body.substitute_name(target_name, arg)),
                Box::new(scope.substitute_name(target_name, arg)),
            ),
        }
    }
}

impl NamedSubstitution<PropFormula> for PropFormula {
    /// Returns a new formula identical to `self` where each instance of the
    /// atom `target_name` is substituted with `arg` (uniform substitution)
    fn substitute_name(
        &self,
        target_name: &str,
        arg: &PropFormula,
    ) -> PropFormula {
        let sub =
            |f: &PropFormula| Box::new(f.substitute_name(target_name, arg));
        let sub_all = |fs: &[PropFormula]| {
            fs.iter()
                .map(|f| f.substitute_name(target_name, arg))
                .collect()
        };
        match self {
            Atom(name) => {
                if name == target_name {
                    arg.to_owned()
                } else {
                    self.to_owned()
                }
            }
            Top | Bottom => self.to_owned(),
            Not(psi) => Not(sub(psi)),
            Conjunction(fs) => Conjunction(sub_all(fs)),
            Disjunction(fs) => Disjunction(sub_all(fs)),
            Arrow(l, r) => Arrow(sub(l), sub(r)),
        }
    }
}

//############################# EXPRESSIONS MANIPULATION
//
//
//############################# NORMAL FORMS

impl PropFormula {
    /// Removes implications and equivalences and pushes negations to atoms.
    /// Negated constants are resolved (¬⊤ = ⊥, ¬⊥ = ⊤)
    pub fn negation_normal_form(&self) -> PropFormula {
        fn solver(φ: &PropFormula, negate: bool) -> PropFormula {
            match φ {
                Atom(_) => {
                    if negate {
                        Not(Box::new(φ.to_owned()))
                    } else {
                        φ.to_owned()
                    }
                }
                Top => {
                    if negate {
                        Bottom
                    } else {
                        Top
                    }
                }
                Bottom => {
                    if negate {
                        Top
                    } else {
                        Bottom
                    }
                }
                Not(ψ) => solver(ψ, !negate),
                Conjunction(formulas) => {
                    let solved =
                        formulas.iter().map(|ψ| solver(ψ, negate)).collect();
                    if negate {
                        Disjunction(solved)
                    } else {
                        Conjunction(solved)
                    }
                }
                Disjunction(formulas) => {
                    let solved =
                        formulas.iter().map(|ψ| solver(ψ, negate)).collect();
                    if negate {
                        Conjunction(solved)
                    } else {
                        Disjunction(solved)
                    }
                }
                // A → B ≡ ¬A ∨ B
                Arrow(assumption, conclusion) => solver(
                    &Disjunction(vec![
                        Not(assumption.to_owned()),
                        (**conclusion).to_owned(),
                    ]),
                    negate,
                ),
            }
        }

        solver(self, false)
    }

    /// Computes the matrix of the conjunctive (`cnf = true`) or disjunctive
    /// (`cnf = false`) normal form of `self`, expected to be in NNF.
    /// The matrix is a vector of rows, each row a vector of literals: for
    /// CNF rows are disjuncted clauses that get conjuncted, for DNF rows are
    /// conjuncted cubes that get disjuncted. Duplicate literals are removed
    /// and rows containing complementary literals (tautological clauses or
    /// contradictory cubes) are dropped
    fn normal_form_matrix(&self, cnf: bool) -> Vec<Vec<PropFormula>> {
        /// Union of two rows, `None` if the result contains complements
        fn merge_rows(
            row1: &[PropFormula],
            row2: &[PropFormula],
        ) -> Option<Vec<PropFormula>> {
            let mut merged = row1.to_vec();
            for lit in row2 {
                if merged.iter().any(|l| l.are_complements(lit)) {
                    return None;
                }
                if !merged.contains(lit) {
                    merged.push(lit.to_owned());
                }
            }
            Some(merged)
        }

        match (self, cnf) {
            // neutral element of the outer connective: no rows
            (Top, true) | (Bottom, false) => vec![],
            // absorbing element of the outer connective: one empty row
            (Top, false) | (Bottom, true) => vec![vec![]],
            (Atom(_), _) | (Not(_), _) => vec![vec![self.to_owned()]],
            // outer connective, rows are concatenated
            (Conjunction(fs), true) | (Disjunction(fs), false) => {
                fs.iter().flat_map(|ψ| ψ.normal_form_matrix(cnf)).collect()
            }
            // inner connective, rows are distributed
            (Disjunction(fs), true) | (Conjunction(fs), false) => {
                let mut result = vec![vec![]];
                for ψ in fs {
                    let ψ_rows = ψ.normal_form_matrix(cnf);
                    result = result
                        .iter()
                        .flat_map(|row| {
                            ψ_rows
                                .iter()
                                .filter_map(|ψ_row| merge_rows(row, ψ_row))
                        })
                        .collect();
                }
                result
            }
            (Arrow(_, _), _) => unreachable!(
                "Implications should be removed by negation normal form"
            ),
        }
    }

    /// Transforms the formula into a CNF logically equivalent one.
    /// Returns the vector of (conjuncted) clauses, each one being either a
    /// literal, a `Disjunction` of literals or `Bottom` for the empty
    /// clause. An empty vector stands for `Top`
    pub fn conjunction_normal_form(&self) -> Vec<PropFormula> {
        self.negation_normal_form()
            .normal_form_matrix(true)
            .into_iter()
            .map(|mut clause| match clause.len() {
                0 => Bottom,
                1 => clause.remove(0),
                _ => Disjunction(clause),
            })
            .collect()
    }

    /// Transforms the formula into a DNF logically equivalent one.
    /// Returns the vector of (disjuncted) cubes, each one being either a
    /// literal, a `Conjunction` of literals or `Top` for the empty cube.
    /// An empty vector stands for `Bottom`
    pub fn disjunction_normal_form(&self) -> Vec<PropFormula> {
        self.negation_normal_form()
            .normal_form_matrix(false)
            .into_iter()
            .map(|mut cube| match cube.len() {
                0 => Top,
                1 => cube.remove(0),
                _ => Conjunction(cube),
            })
            .collect()
    }
}

//############################# NORMAL FORMS

impl SyntacticalEq for PropTerm {
    fn syntactically_equal(&self, other: &PropTerm) -> bool {
        *self == *other
    }
}
impl SyntacticalEq for PropFormula {
    fn syntactically_equal(&self, other: &PropFormula) -> bool {
        *self == *other
    }
}

impl Complement for PropFormula {
    /// Returns the negation of `self`, simplifying double negations and
    /// swapping constants
    fn complement(&self) -> PropFormula {
        match self {
            Not(psi) => (**psi).to_owned(),
            Top => Bottom,
            Bottom => Top,
            _ => Not(Box::new(self.to_owned())),
        }
    }
}

impl ToCnfFormula for PropFormula {
    /// Clausifies the formula into the CNF grammar, where each atom
    /// becomes a nullary predicate and each clause a `Clause` of literals
    fn to_cnf(&self) -> Vec<CnfFormula> {
        fn literal_to_cnf(lit: &PropFormula) -> CnfFormula {
            match lit {
                Atom(name) => CnfFormula::Atom(name.to_string(), vec![]),
                Not(atom) => CnfFormula::Not(Box::new(literal_to_cnf(atom))),
                _ => unreachable!("Normal form matrix only contains literals"),
            }
        }

        self.negation_normal_form()
            .normal_form_matrix(true)
            .iter()
            .map(|clause| {
                CnfFormula::Clause(clause.iter().map(literal_to_cnf).collect())
            })
            .collect()
    }
}

#[cfg(test)]
#[path = "../../tests/type_theory/grammars/prop.rs"]
mod tests;
