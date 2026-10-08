//! Metavariable context of the CIC refiner.
//!
//! Holes (`?`) are plain syntax (`Meta(HOLE_INDEX)`): they carry no identity and
//! no information. The refiner turns every hole into a *metavariable*, an
//! unknown term declared in the metavariable context as `Γ ⊢ ?m : T`, ie
//! with the local context `Γ` it lives in, its type `T`, and eventually its
//! assignment. Metavariables only exist inside the context that created them:
//! every refinement owns its context and must solve all of its metavariables
//! before its output reaches the kernel. Tactic goals are metavariables too.
use super::cic::CicTerm::{self, Meta};
use super::cic_utils::{free_locals, map_subterms, meta_occurs};
use crate::error::LofError;
use std::collections::BTreeMap;

/// Declaration of a metavariable: `context ⊢ ?m : typee`
#[derive(Debug, Clone, PartialEq)]
pub struct MetaDecl {
    /// local assumptions (local name, type) in scope of the metavariable,
    /// outermost first
    pub context: Vec<(String, CicTerm)>,
    /// type of the metavariable
    pub typee: CicTerm,
    /// value of the metavariable, once solved
    pub assignment: Option<CicTerm>,
}
#[derive(Debug, Clone, Default)]
pub struct MetaContext {
    decls: BTreeMap<i32, MetaDecl>,
    next_index: i32,
    /// constraints `expected ≐ actual` with a flexible head (eg `?f x`),
    /// waiting for their metavariables to be solved
    pub postponed: Vec<(CicTerm, CicTerm)>,
}

impl MetaContext {
    /// Declares a new metavariable `context ⊢ ?m : typee`
    pub fn fresh_meta(
        &mut self,
        context: Vec<(String, CicTerm)>,
        typee: CicTerm,
    ) -> CicTerm {
        let index = self.next_index;
        self.next_index += 1;
        self.decls.insert(
            index,
            MetaDecl {
                context,
                typee,
                assignment: None,
            },
        );
        Meta(index)
    }

    pub fn decl(&self, index: &i32) -> Option<&MetaDecl> {
        self.decls.get(index)
    }

    pub fn meta_type(&self, index: &i32) -> Option<CicTerm> {
        self.decls
            .get(index)
            .map(|decl| self.instantiate(&decl.typee))
    }

    /// Assigns `value` to the (unassigned) metavariable `index`, checking
    /// that the assignment is well scoped: `value` cannot mention the
    /// metavariable itself (occurs check) nor local variables that are not in
    /// the context of the metavariable
    pub fn assign(
        &mut self,
        index: i32,
        value: &CicTerm,
    ) -> Result<(), LofError> {
        let decl = self.decls.get(&index).ok_or_else(|| {
            LofError::custom(format!("Unknown metavariable ?[{}]", index))
        })?;
        if let Some(assigned) = &decl.assignment {
            return Err(LofError::conflicting_substitution(
                format!("?[{}]", index),
                assigned,
                value,
            ));
        }
        let value = self.instantiate(value);
        if meta_occurs(index, &value) {
            return Err(LofError::occurs_check_in_term(
                format!("?[{}]", index),
                &value,
            ));
        }
        if let Some(escaping) = free_locals(&value)
            .into_iter()
            .find(|name| !decl.context.iter().any(|(local, _)| local == name))
        {
            return Err(LofError::custom(format!(
                "Cannot solve ?[{}] with {:?}: {} is not in scope of the metavariable",
                index, value, escaping
            )));
        }

        self.decls.get_mut(&index).unwrap().assignment = Some(value);
        Ok(())
    }

    /// Replaces every assigned metavariable in `term` with its value
    pub fn instantiate(&self, term: &CicTerm) -> CicTerm {
        match term {
            Meta(index) => {
                match self.decls.get(index).and_then(|d| d.assignment.as_ref())
                {
                    // the occurs check guarantees this terminates
                    Some(value) => self.instantiate(value),
                    None => term.to_owned(),
                }
            }
            _ => map_subterms(term, |t| self.instantiate(t)),
        }
    }
}

/// Supply of fresh names for the local variables the refiner opens binders
/// with. A generated name is the user facing name of the binder followed by
/// `UNIQUE_NAME_SEPARATOR` and a counter: it cannot clash with user names
/// (which cannot contain the separator) nor with other generated names, so
/// every opened binder gets a truly unique local
#[derive(Debug, Clone, Default)]
pub struct NameGenerator {
    next_index: usize,
}

impl NameGenerator {
    /// Returns a fresh local name for a binder called `base`
    pub fn fresh_local_name(&mut self, base: &str) -> String {
        let index = self.next_index;
        self.next_index += 1;
        format!(
            "{}{}{}",
            strip_unique_name(base),
            UNIQUE_NAME_SEPARATOR,
            index
        )
    }
}

/// Separator between the user facing name of a binder and the unique suffix
/// the refiner appends when opening it (see `NameGenerator`)
pub const UNIQUE_NAME_SEPARATOR: char = '#';

pub fn strip_unique_name(name: &str) -> &str {
    match name.rsplit_once(UNIQUE_NAME_SEPARATOR) {
        Some((base, _)) => base,
        None => name,
    }
}
