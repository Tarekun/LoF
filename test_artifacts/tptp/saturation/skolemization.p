%------------------------------------------------------------------------------
% Status   : Theorem
% Existential axioms and conjectures, clausified through skolemization
%------------------------------------------------------------------------------
fof(something_is_p, axiom, ?[X]: p(X)).
fof(p_maps_to_q, axiom, ![X]: (p(X) => q(f(X)))).
fof(something_is_q, conjecture, ?[Y]: q(Y)).
%------------------------------------------------------------------------------
