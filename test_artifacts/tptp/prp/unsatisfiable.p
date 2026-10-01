%------------------------------------------------------------------------------
% File     : unsatisfiable.p
% Domain   : Propositional logic
% Problem  : An unsatisfiable set of axioms
% English  : Every assignment of p and q falsifies one of the axioms.
% Status   : Unsatisfiable
% SPC      : FOF_UNS_PRP
%------------------------------------------------------------------------------
fof(c1, axiom, p | q).
fof(c2, axiom, ~ p | q).
fof(c3, axiom, p | ~ q).
fof(c4, axiom, ~ p | ~ q).
%------------------------------------------------------------------------------
