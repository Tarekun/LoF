%------------------------------------------------------------------------------
% File     : satisfiable.p
% Domain   : Propositional logic
% Problem  : A satisfiable set of axioms
% English  : Satisfied by q true, whatever p is.
% Status   : Satisfiable
% SPC      : FOF_SAT_PRP
%------------------------------------------------------------------------------
fof(c1, axiom, p | q).
fof(c2, axiom, ~ p | q).
%------------------------------------------------------------------------------
