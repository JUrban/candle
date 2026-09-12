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

print_endline "MARCHAL3_SET_SUBSTITUTION_OK";;
print_endline "MARCHAL3_INVERSE_REWRITE_OK";;
