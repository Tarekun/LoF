-- Translated from library/bool.lof
import Unit'

inductive Bool' : Type where
  | true : Bool'
  | false : Bool'

def not (b : Bool') : Bool' :=
  match b with
  | .true => .false
  | .false => .true

def and (l r : Bool') : Bool' :=
  match l with
  | .true => r
  | .false => .false

def or (l r : Bool') : Bool' :=
  match l with
  | .true => .true
  | .false => r

def impl (l r : Bool') : Bool' :=
  match l with
  | .true => r
  | .false => .true

-- LoF names this function `if`, but `if` is a reserved keyword in this
-- Lean grammar (as it is in real Lean 4), so it is renamed here.
def ite' (T : Type) (exp : Bool') (ifTrue : Unit' -> T) (ifFalse : Unit' -> T) : T :=
  match exp with
  | .true => ifTrue it
  | .false => ifFalse it

-- non-goal: LoF's trailing bare top-level expression statement (used
-- there to test inference) has no Lean equivalent -- Lean only allows
-- declarations at the top level, not bare expressions.
