(* ========================================================================== *)
(* Proof-producing multiplication for exact reflected intervals.             *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. The output bounds are the extrema of the four  *)
(* exact endpoint products. The generic real interval theorem is proved here  *)
(* and then transferred through the rational denotation theorems.             *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_core.ml";;
needs "candle/cv_compute_exact_rational_order_core.ml";;

module Candle_cv_exact_interval_mul_core = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_rational_order_core;;

let candle_q_min4_def = new_definition
 `candle_q_min4 a b c d =
    candle_q_min (candle_q_min a b) (candle_q_min c d)`;;

let candle_q_max4_def = new_definition
 `candle_q_max4 a b c d =
    candle_q_max (candle_q_max a b) (candle_q_max c d)`;;

let candle_q_interval_mul_def = new_definition
 `candle_q_interval_mul
    (i:((num#num)#num)#((num#num)#num)) j =
    (candle_q_min4
       (candle_q_mul (FST i) (FST j))
       (candle_q_mul (FST i) (SND j))
       (candle_q_mul (SND i) (FST j))
       (candle_q_mul (SND i) (SND j)),
     candle_q_max4
       (candle_q_mul (FST i) (FST j))
       (candle_q_mul (FST i) (SND j))
       (candle_q_mul (SND i) (FST j))
       (candle_q_mul (SND i) (SND j)))`;;

(* These four lemmas isolate the sign-sensitive monotonicity steps used by the
   endpoint-product theorem.  Keeping them separate makes the soundness bridge
   independent of the original Flyspeck proof script. *)
let candle_real_mul_upper_pp = prove
 (`!x y b d:real.
     &0 <= x /\ x <= b /\ &0 <= y /\ y <= d ==> x * y <= b * d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[]);;

let candle_real_mul_upper_nn = prove
 (`!x y a c:real.
     a <= x /\ x <= &0 /\ c <= y /\ y <= &0 ==> x * y <= a * c`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_NEG_GE0]);;

let candle_real_mul_upper_pn = prove
 (`!x y a c d:real.
     a <= x /\ &0 <= x /\ c <= y /\ y <= &0 /\ y <= d
     ==> x * y <= (if &0 <= a then a * d else a * c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * y:real` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_NEG_GE0];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC
        [REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_NEG_GE0];
      ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_NEG_GE0] THEN
      CONJ_TAC THEN ASM_REAL_ARITH_TAC]]);;

let candle_real_mul_upper_np = prove
 (`!x y a b c:real.
     a <= x /\ x <= &0 /\ x <= b /\ c <= y /\ &0 <= y
     ==> x * y <= (if &0 <= c then b * c else a * c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x * c:real` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_NEG_GE0];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC
        [REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_NEG_GE0];
      ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_NEG_GE0] THEN
      CONJ_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* Unlike POP_ASSUM, this keeps the assumption in the goal while ACCEPT_TAC
   builds its justification. The selected endpoint bound is always newest. *)
let candle_accept_latest_assum_tac =
  ASSUM_LIST (fun ths -> ACCEPT_TAC (hd ths));;

let candle_real_interval_mul_upper = prove
 (`!x y a b c d:real.
     a <= x /\ x <= b /\ c <= y /\ y <= d
     ==> x * y <=
         max (max (a * c) (a * d)) (max (b * c) (b * d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH `&0 <= x \/ x <= &0`) THENL
   [DISJ_CASES_TAC (REAL_ARITH `&0 <= y \/ y <= &0`) THENL
     [SUBGOAL_THEN `(x:real) * y <= b * d` ASSUME_TAC THENL
       [MP_TAC
         (SPECL [`x:real`; `y:real`; `b:real`; `d:real`]
           candle_real_mul_upper_pp) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN candle_accept_latest_assum_tac;
        REWRITE_TAC[REAL_LE_MAX] THEN
        DISJ2_TAC THEN DISJ2_TAC THEN candle_accept_latest_assum_tac];
      ASM_CASES_TAC `&0 <= a` THENL
       [SUBGOAL_THEN `(x:real) * y <= a * d` ASSUME_TAC THENL
         [MP_TAC
           (SPECL [`x:real`; `y:real`; `a:real`; `c:real`; `d:real`]
             candle_real_mul_upper_pn) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN candle_accept_latest_assum_tac;
          REWRITE_TAC[REAL_LE_MAX] THEN
          DISJ1_TAC THEN DISJ2_TAC THEN candle_accept_latest_assum_tac];
        SUBGOAL_THEN `(x:real) * y <= a * c` ASSUME_TAC THENL
         [MP_TAC
           (SPECL [`x:real`; `y:real`; `a:real`; `c:real`; `d:real`]
             candle_real_mul_upper_pn) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN candle_accept_latest_assum_tac;
          REWRITE_TAC[REAL_LE_MAX] THEN
          DISJ1_TAC THEN DISJ1_TAC THEN candle_accept_latest_assum_tac]]];
    DISJ_CASES_TAC (REAL_ARITH `&0 <= y \/ y <= &0`) THENL
     [ASM_CASES_TAC `&0 <= c` THENL
       [SUBGOAL_THEN `(x:real) * y <= b * c` ASSUME_TAC THENL
         [MP_TAC
           (SPECL [`x:real`; `y:real`; `a:real`; `b:real`; `c:real`]
             candle_real_mul_upper_np) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN candle_accept_latest_assum_tac;
          REWRITE_TAC[REAL_LE_MAX] THEN
          DISJ2_TAC THEN DISJ1_TAC THEN candle_accept_latest_assum_tac];
        SUBGOAL_THEN `(x:real) * y <= a * c` ASSUME_TAC THENL
         [MP_TAC
           (SPECL [`x:real`; `y:real`; `a:real`; `b:real`; `c:real`]
             candle_real_mul_upper_np) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN candle_accept_latest_assum_tac;
          REWRITE_TAC[REAL_LE_MAX] THEN
          DISJ1_TAC THEN DISJ1_TAC THEN candle_accept_latest_assum_tac]];
      SUBGOAL_THEN `(x:real) * y <= a * c` ASSUME_TAC THENL
       [MP_TAC
         (SPECL [`x:real`; `y:real`; `a:real`; `c:real`]
           candle_real_mul_upper_nn) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN candle_accept_latest_assum_tac;
        REWRITE_TAC[REAL_LE_MAX] THEN
        DISJ1_TAC THEN DISJ1_TAC THEN candle_accept_latest_assum_tac]]]);;

let candle_real_interval_mul = prove
 (`!x y a b c d:real.
     a <= x /\ x <= b /\ c <= y /\ y <= d
     ==> min (min (a * c) (a * d)) (min (b * c) (b * d)) <= x * y /\
         x * y <= max (max (a * c) (a * d)) (max (b * c) (b * d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC
    (SPECL [`--x:real`; `y:real`; `--b:real`; `--a:real`;
             `c:real`; `d:real`]
       candle_real_interval_mul_upper) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MAX_MIN; REAL_NEG_NEG;
                REAL_LE_NEG2; REAL_MIN_ACI];
    MP_TAC
     (SPECL [`x:real`; `y:real`; `a:real`; `b:real`; `c:real`; `d:real`]
       candle_real_interval_mul_upper) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN candle_accept_latest_assum_tac]);;

let candle_q_interval_mul_sound = prove
 (`!i j x y.
     candle_q_interval_contains i x /\
     candle_q_interval_contains j y
     ==> candle_q_interval_contains (candle_q_interval_mul i j) (x * y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_interval_mul_def; candle_q_min4_def;
              candle_q_max4_def; FST; SND; candle_q_min_real;
              candle_q_max_real; candle_q_real_mul] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`x:real`; `y:real`;
       `candle_q_real
          (FST (i:((num#num)#num)#((num#num)#num))):real`;
       `candle_q_real
          (SND (i:((num#num)#num)#((num#num)#num))):real`;
       `candle_q_real
          (FST (j:((num#num)#num)#((num#num)#num))):real`;
       `candle_q_real
          (SND (j:((num#num)#num)#((num#num)#num))):real`]
      candle_real_interval_mul) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;

let candle_cv_q_min4_def = new_definition
 `candle_cv_q_min4 a b c d =
    candle_cv_q_min (candle_cv_q_min a b) (candle_cv_q_min c d)`;;

let candle_cv_q_max4_def = new_definition
 `candle_cv_q_max4 a b c d =
    candle_cv_q_max (candle_cv_q_max a b) (candle_cv_q_max c d)`;;

let candle_cv_q_interval_mul_def = new_definition
 `candle_cv_q_interval_mul i j =
    Cexp_pair
      (candle_cv_q_min4
        (candle_cv_q_mul (Cexp_fst i) (Cexp_fst j))
        (candle_cv_q_mul (Cexp_fst i) (Cexp_snd j))
        (candle_cv_q_mul (Cexp_snd i) (Cexp_fst j))
        (candle_cv_q_mul (Cexp_snd i) (Cexp_snd j)))
      (candle_cv_q_max4
        (candle_cv_q_mul (Cexp_fst i) (Cexp_fst j))
        (candle_cv_q_mul (Cexp_fst i) (Cexp_snd j))
        (candle_cv_q_mul (Cexp_snd i) (Cexp_fst j))
        (candle_cv_q_mul (Cexp_snd i) (Cexp_snd j)))`;;

let candle_cv_q_interval_mul_compute_eqs =
  candle_cv_q_interval_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_le_def;
    candle_cv_q_min_def;
    candle_cv_q_max_def;
    candle_cv_q_min4_def;
    candle_cv_q_max4_def;
    candle_cv_q_interval_mul_def];;

let candle_cv_q_min4_correct = prove
 (`!a b c d.
     candle_cv_q_min4 (candle_cv_q a) (candle_cv_q b)
                      (candle_cv_q c) (candle_cv_q d) =
     candle_cv_q (candle_q_min4 a b c d)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_min4_def; candle_q_min4_def;
              candle_cv_q_min_correct]);;

let candle_cv_q_max4_correct = prove
 (`!a b c d.
     candle_cv_q_max4 (candle_cv_q a) (candle_cv_q b)
                      (candle_cv_q c) (candle_cv_q d) =
     candle_cv_q (candle_q_max4 a b c d)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_max4_def; candle_q_max4_def;
              candle_cv_q_max_correct]);;

let candle_cv_q_interval_mul_correct = prove
 (`!i j.
     candle_cv_q_interval_mul
       (candle_cv_q_interval i) (candle_cv_q_interval j) =
     candle_cv_q_interval (candle_q_interval_mul i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_mul_def; candle_cv_q_interval_def;
              candle_q_interval_mul_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_mul_correct; candle_cv_q_min4_correct;
              candle_cv_q_max4_correct]);;

end;;
