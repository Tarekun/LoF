use crate::{
    error::LofError,
    type_theory::grammars::{
        cnf::CnfFormula,
        prop::{
            PropFormula::{Arrow, Atom, Conjunction, Disjunction, Not},
            PropTerm::{Abstraction, Application, Let, Tuple, Variable},
        },
        traits::{
            BottomTop, Complement, NamedSubstitution, SyntacticalEq,
            ToCnfFormula,
        },
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
/// `Atom`s and the full set of connectives
pub enum PropFormula {
    /// atom_name
    Atom(String),
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
    /// the precedence ¬ > ∧ > ∨ > → and → being right associative.
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

    /// Returns `true` iff `self` is a literal or a disjunction of literals
    pub fn is_clause(&self) -> bool {
        match self {
            Disjunction(lits) => lits.iter().all(|lit| lit.is_literal()),
            _ => self.is_literal(),
        }
    }

    /// Returns `true` iff `self` is in negation normal form
    pub fn is_nnf(&self) -> bool {
        match self {
            Atom(_) => true,
            Not(_) => self.is_literal(),
            Conjunction(fs) | Disjunction(fs) => fs.iter().all(|f| f.is_nnf()),
            Arrow(_, _) => false,
        }
    }

    /// Returns `true` iff `self` is a clause or a conjunction of clauses
    pub fn is_cnf(&self) -> bool {
        match self {
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
    fn substitute_name(&mut self, target_name: &str, arg: &PropTerm) {
        match self {
            Variable(var_name) => {
                if var_name == target_name {
                    *self = arg.clone();
                }
            }
            Abstraction(var_name, _, body) => {
                // the name is overridden in `body`'s scope
                if var_name != target_name {
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
            Let(var_name, _, body, scope) => {
                body.substitute_name(target_name, arg);
                // the name is overridden in `body`'s scope
                if var_name != target_name {
                    scope.substitute_name(target_name, arg);
                }
            }
        }
    }
}

impl NamedSubstitution<PropFormula> for PropTerm {
    fn substitute_name(&mut self, target_name: &str, arg: &PropFormula) {
        match self {
            Variable(_) => {}
            Abstraction(_, var_type, body) => {
                var_type.substitute_name(target_name, arg);
                body.substitute_name(target_name, arg);
            }
            Application(left, right) => {
                left.substitute_name(target_name, arg);
                right.substitute_name(target_name, arg);
            }
            Tuple(terms) => terms
                .iter_mut()
                .for_each(|t| t.substitute_name(target_name, arg)),
            Let(_, var_type, body, scope) => {
                if let Some(var_type) = &mut **var_type {
                    var_type.substitute_name(target_name, arg);
                }
                body.substitute_name(target_name, arg);
                scope.substitute_name(target_name, arg);
            }
        }
    }
}

impl NamedSubstitution<PropFormula> for PropFormula {
    fn substitute_name(&mut self, target_name: &str, arg: &PropFormula) {
        match self {
            Atom(name) => {
                if name == target_name {
                    *self = arg.clone();
                }
            }
            Not(psi) => psi.substitute_name(target_name, arg),
            Conjunction(fs) | Disjunction(fs) => fs
                .iter_mut()
                .for_each(|f| f.substitute_name(target_name, arg)),
            Arrow(l, r) => {
                l.substitute_name(target_name, arg);
                r.substitute_name(target_name, arg);
            }
        }
    }
}

//############################# EXPRESSIONS MANIPULATION
//
//
//############################# NORMAL FORMS

// TODO fully drop and rely on FOL, using a .to_fol().to_cnf() pipeline
impl PropFormula {
    /// Removes implications and pushes negations to atoms
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
            (Atom(_), _) | (Not(_), _) => vec![vec![self.to_owned()]],
            // outer connective, rows are concatenated (no rows if empty)
            (Conjunction(fs), true) | (Disjunction(fs), false) => {
                fs.iter().flat_map(|ψ| ψ.normal_form_matrix(cnf)).collect()
            }
            // inner connective, rows are distributed (one empty row if empty)
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
    /// literal or a `Disjunction` of literals (⊥ for the empty clause).
    /// An empty vector stands for ⊤
    pub fn conjunction_normal_form(&self) -> Vec<PropFormula> {
        self.negation_normal_form()
            .normal_form_matrix(true)
            .into_iter()
            .map(|mut clause| match clause.len() {
                0 => Disjunction(vec![]),
                1 => clause.remove(0),
                _ => Disjunction(clause),
            })
            .collect()
    }

    /// Transforms the formula into a DNF logically equivalent one.
    /// Returns the vector of (disjuncted) cubes, each one being either a
    /// literal or a `Conjunction` of literals (⊤ for the empty cube).
    /// An empty vector stands for ⊥
    pub fn disjunction_normal_form(&self) -> Vec<PropFormula> {
        self.negation_normal_form()
            .normal_form_matrix(false)
            .into_iter()
            .map(|mut cube| match cube.len() {
                0 => Conjunction(vec![]),
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

impl BottomTop for PropFormula {
    /// ⊥ is the empty coproduct family
    fn is_bottom(&self) -> bool {
        matches!(self, Disjunction(fs) if fs.is_empty())
    }
    /// ⊤ is the empty product family
    fn is_top(&self) -> bool {
        matches!(self, Conjunction(fs) if fs.is_empty())
    }
}

impl Complement for PropFormula {
    /// Returns the negation of `self`, simplifying double negations and
    /// swapping constants
    fn complement(&self) -> PropFormula {
        match self {
            Not(psi) => (**psi).to_owned(),
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
