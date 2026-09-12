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

print_endline "MARCHAL3_SET_SUBSTITUTION_OK";;
