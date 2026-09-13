let candle_marchal3_xy = prove
 (`!u0 u1 u2 u3 x y z t:A.
     {x,y,z,t} = {u0,u1,u2,u3} /\ x = y
     ==> {u0,u1,u2,u3} = {x,z,t}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM (ASSUME `{x,y,z,t:A} = {u0,u1,u2,u3}`)] THEN
  SUBST1_TAC (ASSUME `x:A = y`) THEN REWRITE_TAC[INSERT_AC]);;

let candle_marchal3_xz = prove
 (`!u0 u1 u2 u3 x y z t:A.
     {x,y,z,t} = {u0,u1,u2,u3} /\ x = z
     ==> {u0,u1,u2,u3} = {x,y,t}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM (ASSUME `{x,y,z,t:A} = {u0,u1,u2,u3}`)] THEN
  SUBST1_TAC (ASSUME `x:A = z`) THEN REWRITE_TAC[INSERT_AC]);;

let candle_marchal3_xt = prove
 (`!u0 u1 u2 u3 x y z t:A.
     {x,y,z,t} = {u0,u1,u2,u3} /\ x = t
     ==> {u0,u1,u2,u3} = {x,y,z}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM (ASSUME `{x,y,z,t:A} = {u0,u1,u2,u3}`)] THEN
  SUBST1_TAC (ASSUME `x:A = t`) THEN REWRITE_TAC[INSERT_AC]);;

let candle_marchal3_yz = prove
 (`!u0 u1 u2 u3 x y z t:A.
     {x,y,z,t} = {u0,u1,u2,u3} /\ y = z
     ==> {u0,u1,u2,u3} = {x,z,t}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM (ASSUME `{x,y,z,t:A} = {u0,u1,u2,u3}`)] THEN
  SUBST1_TAC (ASSUME `y:A = z`) THEN REWRITE_TAC[INSERT_AC]);;

let candle_marchal3_yt = prove
 (`!u0 u1 u2 u3 x y z t:A.
     {x,y,z,t} = {u0,u1,u2,u3} /\ y = t
     ==> {u0,u1,u2,u3} = {x,z,t}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM (ASSUME `{x,y,z,t:A} = {u0,u1,u2,u3}`)] THEN
  SUBST1_TAC (ASSUME `y:A = t`) THEN REWRITE_TAC[INSERT_AC]);;

let candle_marchal3_zt = prove
 (`!u0 u1 u2 u3 x y z t:A.
     {x,y,z,t} = {u0,u1,u2,u3} /\ z = t
     ==> {u0,u1,u2,u3} = {x,y,t}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM (ASSUME `{x,y,z,t:A} = {u0,u1,u2,u3}`)] THEN
  SUBST1_TAC (ASSUME `z:A = t`) THEN REWRITE_TAC[INSERT_AC]);;

let candle_marchal3_card_permutation =
  SET_RULE `{w0,w1,w2,w3:real^3} = {w3,w0,w1,w2}`;;

let candle_marchal3_card_rewrite = prove
 (`!w0 w1 w2 w3:real^3.
     CARD {w0,w1,w2,w3} = CARD {w3,w0,w1,w2}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[candle_marchal3_card_permutation]);;

let candle_marchal3_inverse_rewrite = prove
 (`!p i1 i2 i3 i4.
     p permutes 0..3 /\
     p i1 = 0 /\ p i2 = 1 /\ p i3 = 2 /\ p i4 = 3
     ==> inverse (p:num->num) 0 = i1 /\
         inverse p 3 = i4 /\
         inverse p 1 = i2 /\
         inverse p 2 = i3`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATCH_MP PERMUTES_INVERSE_EQ
    (ASSUME `p permutes 0..3`)] THEN ASM_REWRITE_TAC[]);;

let candle_marchal3_four_selected_members_exhaust = prove
 (`!u v w m w0 w1 w2 w3:real^3.
     u IN {w0,w1,w2,w3} /\ v IN {w0,w1,w2,w3} /\ ~(u = v) /\
     w IN {w0,w1,w2,w3} DIFF {u,v} /\
     m IN {w0,w1,w2,w3} DIFF {u,v,w}
     ==> {u,v,w,m} = {w0,w1,w2,w3}`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF; IN_INSERT; NOT_IN_EMPTY]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[INSERT_AC] THEN ASM_MESON_TAC[]);;

let candle_marchal3_four_selected_application = prove
 (`!u v w m w0 w1 w2 w3:real^3.
     u IN {w0,w1,w2,w3} /\ v IN {w0,w1,w2,w3} /\ ~(u = v) /\
     w IN {w0,w1,w2,w3} DIFF {u,v} /\
     m IN {w0,w1,w2,w3} DIFF {u,v,w}
     ==> {u,v,w,m} = {w0,w1,w2,w3}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_marchal3_four_selected_members_exhaust THEN
  ASM_REWRITE_TAC[]);;

let candle_marchal3_three_swap = prove
 (`!u v a:real^3. {u,v,a} = {v,u,a}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `{u,v,a:real^3} = {v,u,a}`]);;

let candle_marchal3_four_swap = prove
 (`!u v a b:real^3. {u,v,a,b} = {v,u,a,b}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `{u,v,a,b:real^3} = {v,u,a,b}`]);;

print_endline "MARCHAL3_SET_SUBSTITUTION_OK";;
print_endline "MARCHAL3_CARD_PERMUTATION_OK";;
print_endline "MARCHAL3_INVERSE_REWRITE_OK";;
print_endline "MARCHAL3_FOUR_SELECTED_MEMBERS_OK";;
print_endline "MARCHAL3_CONTEXT_FREE_SET_SWAPS_OK";;
