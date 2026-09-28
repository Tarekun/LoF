%------------------------------------------------------------------------------
% Status   : Unsatisfiable
% Addition as a relation: 1 + 1 = 2 follows from the recursive definition
%------------------------------------------------------------------------------
cnf(add_zero, axiom, add(zero, X, X)).
cnf(add_succ, axiom, ~ add(X, Y, Z) | add(s(X), Y, s(Z))).
cnf(one_plus_one_isnt_two, negated_conjecture,
    ~ add(s(zero), s(zero), s(s(zero)))).
%------------------------------------------------------------------------------
