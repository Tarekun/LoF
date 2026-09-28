%------------------------------------------------------------------------------
% Status   : Unsatisfiable
% Group theory: the left identity is also a right identity
% Open: SUP doesnt find the refutation yet (runs out of time)
%------------------------------------------------------------------------------
include('../../cnf/Axioms/groups.ax').

cnf(prove_right_identity, negated_conjecture,
    multiply(a, identity) != a).
%------------------------------------------------------------------------------
