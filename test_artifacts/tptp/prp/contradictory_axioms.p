%------------------------------------------------------------------------------
% File     : contradictory_axioms.p
% Domain   : Propositional logic
% Problem  : Axioms with no model
% Status   : ContradictoryAxioms
% SPC      : FOF_CAX_PRP
%------------------------------------------------------------------------------
fof(p, axiom, p).
fof(not_p, axiom, ~ p).
fof(anything, conjecture, q).
%------------------------------------------------------------------------------
