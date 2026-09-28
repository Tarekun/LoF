%------------------------------------------------------------------------------
% Status   : Theorem
% Typed Peano naturals: 2 is even
%------------------------------------------------------------------------------
tff(nat_type, type, nat: $tType).
tff(zero_decl, type, zero: nat).
tff(succ_decl, type, succ: nat > nat).
tff(even_decl, type, even: nat > $o).
tff(zero_is_even, axiom, even(zero)).
tff(even_step, axiom, ![X: nat]: (even(X) => even(succ(succ(X))))).
tff(two_is_even, conjecture, even(succ(succ(zero)))).
%------------------------------------------------------------------------------
