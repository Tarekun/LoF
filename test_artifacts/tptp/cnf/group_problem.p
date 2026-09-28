%------------------------------------------------------------------------------
% Includes only some of the group axioms, then states a negated conjecture
%------------------------------------------------------------------------------
include('Axioms/groups.ax', [left_identity, left_inverse]).

cnf(prove_right_identity, negated_conjecture,
    multiply(a, identity) != a).
%------------------------------------------------------------------------------
