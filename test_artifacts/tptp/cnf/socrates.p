%------------------------------------------------------------------------------
% File     : socrates.p
% Problem  : Horn clauses: every man is mortal, Socrates is a man, is Socrates mortal?
% Status   : Unsatisfiable
% SPC      : CNF_UNS_EPR_NEQ_HRN
%------------------------------------------------------------------------------
cnf(men_are_mortal, axiom,
    ( ~ man(X)
    | mortal(X) )).

cnf(socrates_is_a_man, axiom,
    man(socrates)).

cnf(socrates_is_not_mortal, negated_conjecture,
    ~ mortal(socrates)).
%------------------------------------------------------------------------------
