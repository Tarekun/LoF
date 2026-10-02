%------------------------------------------------------------------------------
% File     : pigeonhole.p
% Domain   : Combinatorics
% Problem  : Three pigeons don't fit in two holes
% English  : pij means pigeon i sits in hole j. Every pigeon sits in a hole,
%            no hole hosts two pigeons.
% Status   : Unsatisfiable
% SPC      : FOF_UNS_PRP
%------------------------------------------------------------------------------
fof(pigeon_1, axiom, p11 | p12).
fof(pigeon_2, axiom, p21 | p22).
fof(pigeon_3, axiom, p31 | p32).
fof(hole_1, axiom, ~ (p11 & p21) & ~ (p11 & p31) & ~ (p21 & p31)).
fof(hole_2, axiom, ~ (p12 & p22) & ~ (p12 & p32) & ~ (p22 & p32)).
%------------------------------------------------------------------------------
