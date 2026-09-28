%------------------------------------------------------------------------------
% Lexical corner cases of the TPTP syntax
%------------------------------------------------------------------------------
/* block comments
   spanning several lines */

% quoted atoms: 'abc' is the plain atom abc, 'Mixed Case' keeps its quotes
cnf(quoted_atoms, axiom,
    'abc'('Mixed Case', X)).

% numbers and distinct objects are constants
cnf(literals, axiom,
    value("forty two", 42, -1/2)).

% integer names and annotations after the formula
cnf(7, plain,
    p(X) | q(X),
    inference(resolution, [status(thm)], [c1, c2])).

% the empty clause, written as $false
cnf(bottom, negated_conjecture,
    $false).
%------------------------------------------------------------------------------
