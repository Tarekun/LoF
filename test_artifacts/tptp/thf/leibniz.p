%------------------------------------------------------------------------------
% File     : leibniz.p
% Domain   : Higher order logic
% Problem  : Equal individuals satisfy the same properties
% English  : Quantifies over predicates, so it isnt first order.
% Status   : Theorem
% SPC      : TH0_THM_EQU_NAR
%------------------------------------------------------------------------------
thf(a_decl, type, a: $i).
thf(b_decl, type, b: $i).
thf(a_is_b, axiom, a = b).
thf(leibniz, conjecture, ![P: $i > $o]: ((P @ a) => (P @ b))).
%------------------------------------------------------------------------------
