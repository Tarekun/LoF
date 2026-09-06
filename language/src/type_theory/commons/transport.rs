use crate::type_theory::interface::TypeTheory;
use std::collections::HashMap;

/// A hand-authored bundle witnessing that two inductive types are
/// equivalent, together with the DepConstr/DepElim/Eta/Iota data needed to
/// mechanically transport *proof terms* about one into proof terms about
/// the other, following Ringer, Porter, Yazdani, Leo & Grossman,
/// "Proof Repair across Type Equivalences" (PUMPKIN Pi, arXiv:2010.00774).
///
/// Every field is hand-authored (registered via the `equivalence`
/// statement) rather than discovered automatically - this codebase does
/// not attempt the paper's own configuration-search heuristics, which the
/// paper itself describes as limited and often requiring manual override.
///
/// Kept generic over `T: TypeTheory` (mirroring `Environment`'s own
/// genericity) so the configuration data itself isn't hard-wired to CIC,
/// even though the term-walking transport engine that consumes it
/// (`type_theory::cic::transport`) is CIC-specific.
#[derive(Debug)]
pub struct EquivConfig<T: TypeTheory> {
    pub name: String,
    pub type_a: String,
    pub type_b: String,
    /// f : A -> B
    pub forward: T::Term,
    /// g : B -> A
    pub backward: T::Term,
    /// proof: forall a:A. Eq(A, g(f(a)), a)
    pub section: T::Term,
    /// proof: forall b:B. Eq(B, f(g(b)), b)
    pub retraction: T::Term,
    /// DepConstr: A's constructor name -> a B-side smart-constructor term.
    /// Not necessarily a raw constructor of B - eg for Nat/Bin, `s` maps
    /// to an ordinary `increment`-like function on Bin, not a Bin
    /// constructor, since Bin's constructors don't align 1-1 with Nat's.
    pub dep_constr: HashMap<String, T::Term>,
    /// DepElim: the induction/elimination principle to use over B in place
    /// of a raw match/eliminator on A. Often B's own auto-generated
    /// eliminator, but for equivalences whose recursion structure doesn't
    /// align with A's (eg Nat/Bin) this must be a derived lemma shaped
    /// like A's own recursor instead.
    pub dep_elim: T::Term,
    /// Eta: repacks a value produced mid-transport into the shape
    /// DepElim/DepConstr expect (relevant when B packages extra data, eg
    /// PackedVec's length index). Optional - omitted means "nothing to
    /// repack", which is the case for every equivalence handled so far,
    /// since each `dep_constr` already produces the canonical shape.
    pub eta: Option<T::Term>,
    /// Iota: for each A-constructor, a proof term bridging a case where a
    /// step that reduced definitionally on the old (A) side is only
    /// propositionally true on the new (B) side.
    pub iota: HashMap<String, T::Term>,
    /// Names already lifted under this equivalence by a prior `transport`
    /// of a `fun`/`global` (old_name -> new_name), consulted before
    /// falling back to `dep_constr`/pass-through whenever the transport
    /// engine meets an application of an auxiliary function. Grows
    /// monotonically as more `transport` statements run against this
    /// config.
    pub lifted_names: HashMap<String, String>,
}

impl<T: TypeTheory> Clone for EquivConfig<T>
where
    T::Term: Clone,
{
    fn clone(&self) -> Self {
        EquivConfig {
            name: self.name.clone(),
            type_a: self.type_a.clone(),
            type_b: self.type_b.clone(),
            forward: self.forward.clone(),
            backward: self.backward.clone(),
            section: self.section.clone(),
            retraction: self.retraction.clone(),
            dep_constr: self.dep_constr.clone(),
            dep_elim: self.dep_elim.clone(),
            eta: self.eta.clone(),
            iota: self.iota.clone(),
            lifted_names: self.lifted_names.clone(),
        }
    }
}
