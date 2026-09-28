%------------------------------------------------------------------------------
% Horn clauses: every man is mortal, Socrates is a man, is Socrates mortal?
%------------------------------------------------------------------------------
cnf(men_are_mortal, axiom,
    ( ~ man(X)
    | mortal(X) )).

cnf(socrates_is_a_man, axiom,
    man(socrates)).

cnf(socrates_is_not_mortal, negated_conjecture,
    ~ mortal(socrates)).
%------------------------------------------------------------------------------
