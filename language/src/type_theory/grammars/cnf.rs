use crate::type_theory::grammars::cnf::{
    CnfFormula::{Atom, Clause, Equality, ForAll, Not},
    CnfTerm::{Application, Variable},
};
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

#[derive(Clone, PartialEq)]
/// Representation of FOL term in the simplified grammar of CNF.
/// Contains unbound `Variable` variant and a function `Application`,
/// while constants are represented by `Application(k, vec![])`
pub enum CnfTerm {
    /// var_name
    Variable(String),
    /// fun_name, [args]
    Application(String, Vec<CnfTerm>),
}

#[derive(Clone, PartialEq)]
/// A formula in Conjunctive Normal Form (CNF). It contains an
/// `Atom` variant for single predicate application, together with
/// a `Not` that can be applied to it (these 2 form literals), an
/// explicit `Equality` variant between terms, a `Clause` formed
/// by a vector of literals, and a typed universal quantification
pub enum CnfFormula {
    /// pred_name, [args]
    Atom(String, Vec<CnfTerm>),
    Equality(CnfTerm, CnfTerm),
    Not(Box<CnfFormula>),
    /// [literals]
    Clause(Vec<CnfFormula>),
    /// var_name, var_type, formula
    ForAll(String, Box<CnfFormula>, Box<CnfFormula>),
}

//############################# DEBUG LOGS
impl fmt::Debug for CnfTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Variable(name) => write!(f, "{}", name),
            Application(name, args) => {
                if args.len() == 0 {
                    write!(f, "<{}>", name)
                } else {
                    write!(f, "{}(", name)?;
                    for i in 0..args.len() - 1 {
                        write!(f, "{:?}, ", args[i])?;
                    }
                    write!(f, "{:?})", args[args.len() - 1])
                }
            }
        }
    }
}
impl fmt::Debug for CnfFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom(name, args) => {
                if args.len() == 0 {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}(", name)?;
                    for i in 0..args.len() - 1 {
                        write!(f, "{:?}, ", args[i])?;
                    }
                    write!(f, "{:?})", args[args.len() - 1])
                }
            }
            Clause(lits) => {
                if lits.len() == 0 {
                    write!(f, "⊥")
                } else {
                    for i in 0..lits.len() - 1 {
                        write!(f, "{:?} ∨ ", lits[i])?;
                    }
                    write!(f, "{:?}", lits[lits.len() - 1])
                }
            }
            Not(psi) => match &**psi {
                Equality(s, t) => write!(f, "{:?}≠{:?}", s, t),
                _ => write!(f, "¬{:?}", psi),
            },
            Equality(l, r) => write!(f, "{:?} = {:?}", l, r),
            ForAll(var_name, var_type, psi) => {
                write!(f, "∀{}:{:?}. {:?}", var_name, var_type, psi)
            }
        }
    }
}
//############################# DEBUG LOGS
//
//
//############################# CHECKS ON EXPRESSIONS

impl CnfTerm {
    /// Returns `true` iff `self` and `term2` are exactly the same expression
    pub fn are_syntactically_equal(&self, term2: &CnfTerm) -> bool {
        *self == *term2
    }

    /// Returns `true` iff `term` contains `target` inside
    pub fn contains(&self, target: &CnfTerm) -> bool {
        if self.are_syntactically_equal(target) {
            return true;
        }

        match self {
            Application(_, args) => {
                for arg in args {
                    if arg.contains(target) {
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }
}

impl CnfFormula {
    /// Returns `true` iff `self` and `formula2` are exactly the same expression
    pub fn are_syntactically_equal(&self, formula2: &CnfFormula) -> bool {
        *self == *formula2
    }

    /// Check if two literals are (syntactically) complements
    fn are_complements(&self, lit2: &CnfFormula) -> bool {
        match (self, lit2) {
            (Atom(_, _), Not(q)) => **q == *self,
            (Not(p), Atom(_, _)) => **p == *lit2,
            _ => false,
        }
    }

    /// Returns `true` if the formula is *found* to be a tautology, but who knows...
    pub fn is_tautology(&self) -> bool {
        match self {
            //TODO look for axioms/sorts?
            Clause(literals) => {
                for (idx, lit) in literals.iter().enumerate() {
                    if lit.is_tautology() {
                        return true;
                    }

                    // excluded middle
                    for lit2 in &literals[0..idx] {
                        if lit.are_complements(lit2) {
                            return true;
                        }
                    }
                }

                false
            }
            // identity of equals
            Equality(left, right) => left.are_syntactically_equal(right),

            // TODO review
            _ => false,
        }
    }

    #[allow(non_snake_case)]
    /// Checks wheter clause `self` subsumes `D`, ie if `self`≐`E` where `E` is a subset
    /// of literals of `D`
    pub fn subsumes(&self, D: &CnfFormula) -> bool {
        let Clause(c_lits) = self else { return false };
        let Clause(d_lits) = D else { return false };

        // TODO if i implement Eq and Hash for CnfFormula in a way that supports
        // alpha equivalence this time complexity can be reduced from O(nm) to O(n+m)
        c_lits.iter().all(|c_lit| {
            d_lits
                .iter()
                //TODO currently this is syntactic equality with no mgu support
                .any(|d_lit| c_lit.are_syntactically_equal(d_lit))
        })
    }
}

//############################# CHECKS ON EXPRESSIONS
//
//
//############################# LOOKUPS

impl CnfTerm {}

impl CnfFormula {
    /// Given a clause formula, returns the vector of its literals.
    /// Treats literal variants as singleton clauses
    pub fn unpack_literals(&self) -> Vec<CnfFormula> {
        match self {
            Clause(literals) => literals.to_owned(),
            _ => vec![self.clone()],
        }
    }
}

//############################# CHECKS ON EXPRESSIONS
//
//
//############################# EXPRESSIONS MANIPULATION

impl CnfTerm {
    /// Returns a new term identical to `self` where every occurance of `target` is
    /// substituted by `arg`
    pub fn substitute_term(&self, target: &CnfTerm, arg: &CnfTerm) -> CnfTerm {
        if self.are_syntactically_equal(target) {
            return arg.to_owned();
        }

        match self {
            Application(fun_name, fun_args) => Application(
                fun_name.to_string(),
                fun_args
                    .iter()
                    .map(|fun_arg| fun_arg.substitute_term(target, arg))
                    .collect(),
            ),
            // non-recursive cases didnt pass equality against `target` by now
            _ => self.to_owned(),
        }
    }
}

static VAR_COUNTER: AtomicUsize = AtomicUsize::new(0);
impl CnfFormula {
    /// Returns a new formula identical to `self` where every variable name is
    /// suffixed with `_<id>` to make it disjoint from any other clause's variables.
    pub fn standardize_apart(&self) -> CnfFormula {
        fn rename_vars_term(term: &CnfTerm, id: usize) -> CnfTerm {
            match term {
                Variable(name) => Variable(format!("{}_{}", name, id)),
                Application(fun, args) => Application(
                    fun.clone(),
                    args.iter().map(|a| rename_vars_term(a, id)).collect(),
                ),
            }
        }

        fn rename_vars_formula(formula: &CnfFormula, id: usize) -> CnfFormula {
            match formula {
                Atom(pred, args) => Atom(
                    pred.clone(),
                    args.iter().map(|a| rename_vars_term(a, id)).collect(),
                ),
                Equality(l, r) => {
                    Equality(rename_vars_term(l, id), rename_vars_term(r, id))
                }
                Not(inner) => Not(Box::new(rename_vars_formula(inner, id))),
                Clause(lits) => Clause(
                    lits.iter().map(|l| rename_vars_formula(l, id)).collect(),
                ),
                ForAll(var, ty, body) => ForAll(
                    format!("{}_{}", var, id),
                    Box::new(rename_vars_formula(ty, id)),
                    Box::new(rename_vars_formula(body, id)),
                ),
            }
        }

        let id = VAR_COUNTER.fetch_add(1, Relaxed);
        rename_vars_formula(self, id)
    }

    /// Returns a new formula identical to `formula` where every occurance of `target` is
    /// substituted by `arg`
    pub fn substitute_formula(
        &self,
        target: &CnfTerm,
        arg: &CnfTerm,
    ) -> CnfFormula {
        match self {
            Atom(pred_name, pred_args) => Atom(
                pred_name.to_string(),
                pred_args
                    .iter()
                    .map(|pred_arg| pred_arg.substitute_term(target, arg))
                    .collect(),
            ),
            Equality(l, r) => Equality(
                l.substitute_term(target, arg),
                r.substitute_term(target, arg),
            ),
            Not(sub) => Not(Box::new(sub.substitute_formula(target, arg))),
            Clause(sub_formulas) => Clause(
                sub_formulas
                    .iter()
                    .map(|lit| lit.substitute_formula(target, arg))
                    .collect(),
            ),
            ForAll(var_name, var_type, body) => ForAll(
                var_name.to_string(),
                Box::new(var_type.substitute_formula(target, arg)),
                Box::new(body.substitute_formula(target, arg)),
            ),
        }
    }
}

//############################# EXPRESSIONS MANIPULATION
