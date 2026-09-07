-- Translated from library/tests/proofs/theorem_reuse.lof
inductive Nat' : Type where
  | z : Nat'
  | s : Nat' -> Nat'

inductive Eq' (T : Type) (x : T) : T -> Prop where
  | refl : Eq' T x x

theorem zero_eq_zero : Eq' Nat' z z :=
  Eq'.refl Nat' z

theorem reuse_term_mode : Eq' Nat' z z :=
  zero_eq_zero

theorem one_eq_one : Eq' Nat' (s z) (s z) := by
  exact Eq'.refl Nat' (s z)

theorem reuse_tactic_mode : Eq' Nat' (s z) (s z) := by
  exact one_eq_one

def plus (n m : Nat') : Nat' :=
  match n with
  | .z => m
  | .s nn => .s (plus nn m)

axiom P : Prop
axiom Q : Prop
axiom p_proof : P
axiom pq_impl : P -> Q

theorem q_holds : Q := by
  apply pq_impl
  exact p_proof

theorem q_holds_again : Q :=
  q_holds
