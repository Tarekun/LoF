%------------------------------------------------------------------------------
% Status   : Theorem
% Greeks are human, humans are mortal, Socrates is greek
%------------------------------------------------------------------------------
fof(humans_are_mortal, axiom, ![X]: (human(X) => mortal(X))).
fof(greeks_are_human, axiom, ![X]: (greek(X) => human(X))).
fof(socrates_is_greek, axiom, greek(socrates)).
fof(socrates_is_mortal, conjecture, mortal(socrates)).
%------------------------------------------------------------------------------
