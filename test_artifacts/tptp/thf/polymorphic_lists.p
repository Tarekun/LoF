%------------------------------------------------------------------------------
% File     : polymorphic_lists.p
% Domain   : Higher order logic
% Problem  : Mapping a function over the empty list
% English  : A polymorphic type constructor with polymorphic constructors and
%            a polymorphic map function, instantiated at $i.
% Status   : Theorem
% SPC      : TH1_THM_EQU_NAR
%------------------------------------------------------------------------------
thf(list_type, type, list: $tType > $tType).
thf(nil_decl, type, nil: !>[A: $tType]: (list @ A)).
thf(cons_decl, type, cons: !>[A: $tType]: (A > (list @ A) > (list @ A))).
thf(map_decl, type,
    map: !>[A: $tType, B: $tType]: ((A > B) > (list @ A) > (list @ B))).

thf(map_nil, axiom,
    !>[A: $tType, B: $tType]: ![F: A > B]:
      ((map @ A @ B @ F @ (nil @ A)) = (nil @ B))).

thf(map_cons, axiom,
    !>[A: $tType, B: $tType]: ![F: A > B, X: A, L: (list @ A)]:
      ((map @ A @ B @ F @ (cons @ A @ X @ L))
      = (cons @ B @ (F @ X) @ (map @ A @ B @ F @ L)))).

thf(map_identity_nil, conjecture,
    ( map @ $i @ $i @ (^[X: $i]: X) @ (nil @ $i) ) = (nil @ $i)).
%------------------------------------------------------------------------------
