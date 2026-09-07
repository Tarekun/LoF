-- Translated from library/tests/proofs/intro_apply_tactics.lof
inductive Nat' : Type where
  | z : Nat'
  | s : Nat' -> Nat'

inductive Eq' (T : Type) (x : T) : T -> Prop where
  | refl : Eq' T x x

theorem single_intro : forall n : Nat', Eq' Nat' n n := by
  intro n
  exact Eq'.refl Nat' n

theorem double_intro : forall n : Nat', forall m : Nat', Eq' Nat' n n := by
  intro n
  intro m
  exact Eq'.refl Nat' n

axiom P : Prop
axiom Q : Prop
axiom pq : P -> Q
axiom p : P

theorem apply_then_exact : Q := by
  apply pq
  exact p
