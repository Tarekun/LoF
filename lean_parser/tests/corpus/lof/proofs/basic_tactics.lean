-- Translated from library/tests/proofs/basic_tactics.lof
inductive Eq' (T : Type) (x : T) : T -> Prop where
  | refl : Eq' T x x

inductive Nat' : Type where
  | z : Nat'
  | s : Nat' -> Nat'

def plus (n m : Nat') : Nat' :=
  match n with
  | .z => m
  | .s nn => .s (plus nn m)

theorem zero_plus_one_term : Eq' Nat' (plus z (s z)) (s z) :=
  Eq'.refl Nat' (s z)

theorem zero_plus_one_tac : Eq' Nat' (plus z (s z)) (s z) := by
  exact Eq'.refl Nat' (s z)
