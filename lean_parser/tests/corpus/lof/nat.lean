-- Translated from library/nat.lof
inductive Nat' : Type where
  | z : Nat'
  | s : Nat' -> Nat'

-- definition a la coq
inductive le' : Nat' -> Nat' -> Prop where
  | lez : forall n : Nat', le' z n
  | les : forall n : Nat', forall m : Nat', le' n m -> le' (s n) (s m)

-- note: in case of n = 0 the pred should be undefined
def pred (n : Nat') : Nat' :=
  match n with
  | .z => .z
  | .s nn => nn

def plus (n m : Nat') : Nat' :=
  match n with
  | .z => m
  | .s nn => .s (plus nn m)

-- non-goal: user notation (`sugar "_0 + _1" := "plus(_0, _1)"` in LoF) has
-- no Lean equivalent in scope -- that's `infixl`/`notation`, a non-goal.

-- note the case 0 - m always returns 0
-- in case m != 0 the function should be undefined
def minus (n m : Nat') : Nat' :=
  match n with
  | .z => .z
  | .s nn =>
    match m with
    | .z => n
    | .s mm => minus nn mm

def times (n m : Nat') : Nat' :=
  match n with
  | .z => .z
  | .s nn => plus (times nn m) m

-- n / m
def divwithacc (n m acc : Nat') : Nat' :=
  match n with
  | .z => acc
  | .s nn => divwithacc (minus n m) m (s acc)

def div (n m : Nat') : Nat' :=
  divwithacc n m z

def pow (b e : Nat') : Nat' :=
  match e with
  | .z => s z
  | .s ee => times (pow b ee) b
