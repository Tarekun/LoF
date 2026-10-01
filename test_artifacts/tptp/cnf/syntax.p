%------------------------------------------------------------------------------
% File     : syntax.p
% Problem  : Lexical corner cases of the TPTP syntax
% Status   : Satisfiable
% SPC      : CNF_SAT_EPR_NEQ_NHN
%------------------------------------------------------------------------------
/* block comments
   spanning several lines */

% quoted words lose their quotes: 'abc' is the plain word abc
cnf(quoted_atoms, axiom,
    'abc'('Mixed Case', X)).

% integer names and annotations after the formula
cnf(7, plain,
    p(X) | q(X),
    inference(resolution, [status(thm)], [c1, c2])).
%------------------------------------------------------------------------------
