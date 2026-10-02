%------------------------------------------------------------------------------
% File     : connectives.p
% Domain   : Propositional logic
% Problem  : Laws relating the TPTP connectives
% English  : Every binary connective, the truth constants and quoted atoms.
%            The conjectures are proved jointly.
% Status   : Theorem
% SPC      : FOF_THM_PRP
%------------------------------------------------------------------------------
fof(iff_is_double_implication, conjecture,
    (p <=> q) <=> ((p => q) & (p <= q))).
fof(xor_is_not_iff, conjecture, (p <~> q) <=> ~ (p <=> q)).
fof(de_morgan_nor, conjecture, (p ~| q) <=> (~ p & ~ q)).
fof(de_morgan_nand, conjecture, (p ~& q) <=> (~ p | ~ q)).
fof(truth_constants, conjecture, $true & ~ $false).
fof(quoted_atoms, conjecture, 'It rains' => ('It rains' | 'it_snows')).
%------------------------------------------------------------------------------
