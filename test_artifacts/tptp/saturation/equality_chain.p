%------------------------------------------------------------------------------
% Status   : Unsatisfiable
% Rewriting along a chain of equalities: p(a) and a = b = c give p(c)
%------------------------------------------------------------------------------
cnf(a_is_b, axiom, a = b).
cnf(b_is_c, axiom, b = c).
cnf(p_of_a, axiom, p(a)).
cnf(not_p_of_c, negated_conjecture, ~ p(c)).
%------------------------------------------------------------------------------
