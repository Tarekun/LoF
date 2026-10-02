%------------------------------------------------------------------------------
% File     : modus_ponens.p
% Domain   : Propositional logic
% Problem  : Modus ponens
% English  : From p and p implies q, q follows.
% Status   : Theorem
% SPC      : FOF_THM_PRP
%------------------------------------------------------------------------------
fof(p, axiom, p).
fof(p_implies_q, axiom, p => q).
fof(q, conjecture, q).
%------------------------------------------------------------------------------
