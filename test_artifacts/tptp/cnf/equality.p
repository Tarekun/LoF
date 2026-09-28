%------------------------------------------------------------------------------
% Equational clauses: left identity and associativity of a binary operation
%------------------------------------------------------------------------------
cnf(left_identity, axiom,
    multiply(identity, X) = X).

cnf(associativity, axiom,
    multiply(multiply(X, Y), Z) = multiply(X, multiply(Y, Z))).

cnf(distinct_elements, axiom,
    a != b).

cnf(conditional_equality, hypothesis,
    ( X = Y
    | ~ equivalent(X, Y)
    | f(X) != f(Y) )).
%------------------------------------------------------------------------------
