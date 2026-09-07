-- Translated from library/tests/proofs/match_pattern_substitution.lof
inductive Eq' (T : Type) (x : T) : T -> Prop where
  | refl : Eq' T x x

inductive Nat' : Type where
  | z : Nat'
  | s : Nat' -> Nat'

def plus (n m : Nat') : Nat' :=
  match n with
  | .z => m
  | .s nn => .s (plus nn m)

def times (n m : Nat') : Nat' :=
  match n with
  | .z => .z
  | .s nn => plus (times nn m) m

theorem one_plus_one : Eq' Nat' (plus (s z) (s z)) (s (s z)) :=
  Eq'.refl Nat' (s (s z))

theorem two_plus_two :
    Eq' Nat' (plus (s (s z)) (s (s z))) (s (s (s (s z)))) :=
  Eq'.refl Nat' (s (s (s (s z))))

theorem two_times_two :
    Eq' Nat' (times (s (s z)) (s (s z))) (s (s (s (s z)))) :=
  Eq'.refl Nat' (s (s (s (s z))))

inductive List' (T : Type) : Type where
  | nil : List' T
  | cons : T -> List' T -> List' T

def len (l : List' _) : Nat' :=
  match l with
  | .nil => z
  | .cons _ ll => s (len ll)

def fold (A : Type) (combine : A -> A -> A) (l : List' A) (seed : A) : A :=
  match l with
  | .nil => seed
  | .cons h ll => fold A combine ll (combine h seed)

theorem len_two_elem_list :
    Eq' Nat' (len (List'.cons z (List'.cons z List'.nil))) (s (s z)) :=
  Eq'.refl Nat' (s (s z))

theorem fold_sums_two_elements :
    Eq' Nat'
      (fold Nat' plus (List'.cons (s z) (List'.cons (s z) List'.nil)) z)
      (s (s z)) :=
  Eq'.refl Nat' (s (s z))
