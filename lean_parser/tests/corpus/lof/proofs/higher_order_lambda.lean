-- Translated from library/tests/proofs/higher_order_lambda.lof
-- Regression coverage: a lambda whose body applies a constructor / a
-- user-defined function to its own bound variable.
inductive Nat' : Type where
  | z : Nat'
  | s : Nat' -> Nat'

inductive Eq' (T : Type) (x : T) : T -> Prop where
  | refl : Eq' T x x

def pred (n : Nat') : Nat' :=
  match n with
  | .z => .z
  | .s nn => nn

theorem lambda_applying_constructor :
    Eq' Nat' ((fun n => s n) z) (s z) :=
  Eq'.refl Nat' (s z)

theorem lambda_applying_function :
    Eq' Nat' ((fun n => pred n) (s z)) z :=
  Eq'.refl Nat' z
