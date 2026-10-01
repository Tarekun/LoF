%------------------------------------------------------------------------------
% File     : affirming_the_consequent.p
% Domain   : Propositional logic
% Problem  : Affirming the consequent is a fallacy
% English  : From q and p implies q, p doesn't follow: p false, q true is a
%            countermodel.
% Status   : CounterSatisfiable
% SPC      : FOF_CSA_PRP
%------------------------------------------------------------------------------
fof(q, axiom, q).
fof(p_implies_q, axiom, p => q).
fof(p, conjecture, p).
%------------------------------------------------------------------------------
