(* ========================================================================== *)
(* Proof-producing interval operations over exact reflected rationals.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. This is the first shared substrate for the     *)
(* nonlinear Taylor checker: interval results are computed as cvals, decoded *)
(* through a proved round trip, and related to real containment by theorems   *)
(* in cv_compute_exact_rational_core.ml.                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_rational_core.ml";;

module Candle_cv_exact_interval_core = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;

let candle_cv_q_interval_def = new_definition
 `candle_cv_q_interval
    (i:((num#num)#num)#((num#num)#num)) =
    Cexp_pair (candle_cv_q (FST i)) (candle_cv_q (SND i))`;;

let candle_cv_q_interval_decode_def = define
 `(candle_cv_q_interval_decode (Cexp_num n) =
     ((((0,0),0),((0,0),0)):
       ((num#num)#num)#((num#num)#num))) /\
  (candle_cv_q_interval_decode (Cexp_pair lo hi) =
     (candle_cv_q_decode lo,candle_cv_q_decode hi))`;;

let candle_cv_q_interval_roundtrip = prove
 (`!i:((num#num)#num)#((num#num)#num).
     candle_cv_q_interval_decode (candle_cv_q_interval i) = i`,
  REWRITE_TAC[candle_cv_q_interval_decode_def; candle_cv_q_interval_def;
              candle_cv_q_roundtrip]);;

let candle_cv_q_interval_add_def = new_definition
 `candle_cv_q_interval_add x y =
    Cexp_pair
      (candle_cv_q_add (Cexp_fst x) (Cexp_fst y))
      (candle_cv_q_add (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_q_interval_neg_def = new_definition
 `candle_cv_q_interval_neg x =
    Cexp_pair (candle_cv_q_neg (Cexp_snd x))
              (candle_cv_q_neg (Cexp_fst x))`;;

let candle_cv_q_interval_compute_eqs =
  candle_cv_q_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_interval_add_def;
    candle_cv_q_interval_neg_def];;

let candle_cv_q_interval_add_correct = prove
 (`!x y.
     candle_cv_q_interval_add
       (candle_cv_q_interval x) (candle_cv_q_interval y) =
     candle_cv_q_interval (candle_q_interval_add x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_add_def; candle_cv_q_interval_def;
              candle_q_interval_add_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_add_correct]);;

let candle_cv_q_interval_neg_correct = prove
 (`!x.
     candle_cv_q_interval_neg (candle_cv_q_interval x) =
     candle_cv_q_interval (candle_q_interval_neg x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_neg_def; candle_cv_q_interval_def;
              candle_q_interval_neg_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_neg_correct]);;

end;;
