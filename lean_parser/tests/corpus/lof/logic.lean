-- Translated from library/logic.lof
inductive Eq' (T : Type) (x : T) : T -> Prop where
  | refl : Eq' T x x

inductive True' : Prop where
  | it : True'

inductive False' : Prop where

-- if i make a proof that by assuming P i can construct False
-- then i constructed a proof of Not P
inductive Not' (P : Prop) : Prop where
  | notcon : (P -> False') -> Not' P

-- if i make a proof of P and a proof of Q
-- then i constructed a proof of And P Q
inductive And' (P Q : Prop) : Prop where
  | conj : P -> Q -> And' P Q

-- to construct a proof of Or P Q i can either
-- make a proof of P and use left
-- make a proof of Q and use right
inductive Or' (P Q : Prop) : Prop where
  | left : P -> Or' P Q
  | right : Q -> Or' P Q

-- if i make a proof of P t for some term t : T and predicate P
-- then i constructed a proof that Exists T P
inductive Exists' (T : Type) (P : T -> Prop) : Prop where
  | excon : forall t : T, P t -> Exists' T P
