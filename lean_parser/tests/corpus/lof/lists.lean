-- Translated from library/lists.lof
import Nat'

inductive List' (T : Type) : Type where
  | nil : List' T
  | cons : T -> List' T -> List' T

def fold (A : Type) (combine : A -> A -> A) (l : List' A) (seed : A) : A :=
  match l with
  | .nil => seed
  | .cons h ll => fold A combine ll (combine h seed)

def map (A B : Type) (mapper : A -> B) (l : List' A) : List' B :=
  match l with
  | .nil => .nil
  | .cons h ll => .cons (mapper h) (map A B mapper ll)

def len (l : List' _) : Nat' :=
  match l with
  | .nil => z
  | .cons _ ll => s (len ll)
