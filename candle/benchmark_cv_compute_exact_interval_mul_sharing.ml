(* ========================================================================== *)
(* Reflected interval-multiplication endpoint sharing benchmark.             *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The production definition spells the four    *)
(* endpoint products once below the minimum and again below the maximum.     *)
(* The candidate passes the four products through a helper, so strict        *)
(* evaluation computes each once.  A compact structural checksum forces the  *)
(* complete interval result without accumulating a large output theorem.     *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_mul_core.ml";;
needs "candle/cv_compute_analytic_expr_jet_prove.ml";;

open Candle_cv_exact_interval_mul_core;;
open Candle_cv_analytic_expr_jet_prove;;

let candle_cv_q_interval_mul_shared_finish_def = new_definition
 `candle_cv_q_interval_mul_shared_finish p00 p01 p10 p11 =
    Cexp_pair
      (candle_cv_q_min4 p00 p01 p10 p11)
      (candle_cv_q_max4 p00 p01 p10 p11)`;;

let candle_cv_q_interval_mul_shared_def = new_definition
 `candle_cv_q_interval_mul_shared i j =
    candle_cv_q_interval_mul_shared_finish
      (candle_cv_q_mul (Cexp_fst i) (Cexp_fst j))
      (candle_cv_q_mul (Cexp_fst i) (Cexp_snd j))
      (candle_cv_q_mul (Cexp_snd i) (Cexp_fst j))
      (candle_cv_q_mul (Cexp_snd i) (Cexp_snd j))`;;

let candle_cv_interval_mul_sharing_size_def = define
 `(candle_cv_interval_mul_sharing_size (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_interval_mul_sharing_size (Cexp_pair h t) =
     Cexp_add (candle_cv_interval_mul_sharing_size h)
       (candle_cv_interval_mul_sharing_size t))`;;

let candle_cv_interval_mul_sharing_size_compute = prove
 (`!value.
     candle_cv_interval_mul_sharing_size value =
     Cexp_if (Cexp_ispair value)
       (Cexp_add
         (candle_cv_interval_mul_sharing_size (Cexp_fst value))
         (candle_cv_interval_mul_sharing_size (Cexp_snd value)))
       (Cexp_num 1)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `value:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_interval_mul_sharing_size_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_interval_mul_sharing_current_repeat_def = define
 `(candle_cv_interval_mul_sharing_current_repeat
      (Cexp_num n) i j = Cexp_num 0) /\
  (candle_cv_interval_mul_sharing_current_repeat
      (Cexp_pair h t) i j =
    Cexp_add
      (candle_cv_interval_mul_sharing_size
        (candle_cv_q_interval_mul i j))
      (candle_cv_interval_mul_sharing_current_repeat t i j))`;;

let candle_cv_interval_mul_sharing_current_repeat_compute = prove
 (`!count i j.
     candle_cv_interval_mul_sharing_current_repeat count i j =
     Cexp_if (Cexp_ispair count)
       (Cexp_add
         (candle_cv_interval_mul_sharing_size
           (candle_cv_q_interval_mul i j))
         (candle_cv_interval_mul_sharing_current_repeat
           (Cexp_snd count) i j))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `count:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_interval_mul_sharing_current_repeat_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_interval_mul_sharing_shared_repeat_def = define
 `(candle_cv_interval_mul_sharing_shared_repeat
      (Cexp_num n) i j = Cexp_num 0) /\
  (candle_cv_interval_mul_sharing_shared_repeat
      (Cexp_pair h t) i j =
    Cexp_add
      (candle_cv_interval_mul_sharing_size
        (candle_cv_q_interval_mul_shared i j))
      (candle_cv_interval_mul_sharing_shared_repeat t i j))`;;

let candle_cv_interval_mul_sharing_shared_repeat_compute = prove
 (`!count i j.
     candle_cv_interval_mul_sharing_shared_repeat count i j =
     Cexp_if (Cexp_ispair count)
       (Cexp_add
         (candle_cv_interval_mul_sharing_size
           (candle_cv_q_interval_mul_shared i j))
         (candle_cv_interval_mul_sharing_shared_repeat
           (Cexp_snd count) i j))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `count:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_interval_mul_sharing_shared_repeat_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_interval_mul_sharing_equations =
  candle_cv_q_interval_mul_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_interval_mul_shared_finish_def;
    candle_cv_q_interval_mul_shared_def;
    candle_cv_interval_mul_sharing_size_compute;
    candle_cv_interval_mul_sharing_current_repeat_compute;
    candle_cv_interval_mul_sharing_shared_repeat_compute];;

let candle_cv_interval_mul_sharing_q pp nn dd =
  let numc value = mk_comb (`Cexp_num`,value) in
  list_mk_comb
    (`Cexp_pair`,
     [list_mk_comb (`Cexp_pair`,[numc pp;numc nn]);numc dd]);;

let candle_cv_interval_mul_sharing_i =
  list_mk_comb
    (`Cexp_pair`,
     [candle_cv_interval_mul_sharing_q
        `0` `123456789` `1000002`;
      candle_cv_interval_mul_sharing_q
        `987654321` `0` `1000032`]);;

let candle_cv_interval_mul_sharing_j =
  list_mk_comb
    (`Cexp_pair`,
     [candle_cv_interval_mul_sharing_q
        `0` `246813579` `1000036`;
      candle_cv_interval_mul_sharing_q
        `192837465` `0` `1000038`]);;

let candle_cv_interval_mul_sharing_repetitions =
  itlist
    (fun _ tail -> list_mk_comb (`Cexp_pair`,[`Cexp_num 0`;tail]))
    (1--1024) `Cexp_num 0`;;

let candle_cv_interval_mul_sharing_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=interval-mul-sharing scope=repeat-1024" ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_cv_interval_mul_sharing_current_call =
  list_mk_comb
    (`candle_cv_interval_mul_sharing_current_repeat`,
     [candle_cv_interval_mul_sharing_repetitions;
      candle_cv_interval_mul_sharing_i;
      candle_cv_interval_mul_sharing_j]);;

let candle_cv_interval_mul_sharing_shared_call =
  list_mk_comb
    (`candle_cv_interval_mul_sharing_shared_repeat`,
     [candle_cv_interval_mul_sharing_repetitions;
      candle_cv_interval_mul_sharing_i;
      candle_cv_interval_mul_sharing_j]);;

let _ = candle_cv_interval_mul_sharing_marker "current" "begin";;
let candle_cv_interval_mul_sharing_current_result =
  candle_q_dim_analytic_jet_compute
    candle_cv_interval_mul_sharing_equations
    candle_cv_interval_mul_sharing_current_call;;
let _ = candle_cv_interval_mul_sharing_marker "current" "end";;

let _ = candle_cv_interval_mul_sharing_marker "shared" "begin";;
let candle_cv_interval_mul_sharing_shared_result =
  candle_q_dim_analytic_jet_compute
    candle_cv_interval_mul_sharing_equations
    candle_cv_interval_mul_sharing_shared_call;;
let _ = candle_cv_interval_mul_sharing_marker "shared" "end";;

let candle_cv_interval_mul_sharing_one_current =
  candle_q_dim_analytic_jet_compute
    candle_cv_interval_mul_sharing_equations
    (list_mk_comb
      (`candle_cv_q_interval_mul`,
       [candle_cv_interval_mul_sharing_i;
        candle_cv_interval_mul_sharing_j]));;
let candle_cv_interval_mul_sharing_one_shared =
  candle_q_dim_analytic_jet_compute
    candle_cv_interval_mul_sharing_equations
    (list_mk_comb
      (`candle_cv_q_interval_mul_shared`,
       [candle_cv_interval_mul_sharing_i;
        candle_cv_interval_mul_sharing_j]));;

if hyp candle_cv_interval_mul_sharing_current_result <> [] ||
   hyp candle_cv_interval_mul_sharing_shared_result <> [] ||
   not
     (aconv (rand (concl candle_cv_interval_mul_sharing_current_result))
            (rand (concl candle_cv_interval_mul_sharing_shared_result))) ||
   not
     (aconv (rand (concl candle_cv_interval_mul_sharing_one_current))
            (rand (concl candle_cv_interval_mul_sharing_one_shared))) then
  failwith "interval multiplication sharing: exact result mismatch";;

print_endline
  "CANDLE_CV_INTERVAL_MUL_SHARING_RESULT repeats=1024 exact_match=1";;
print_endline
  "CANDLE_CV_INTERVAL_MUL_SHARING_OK DEVELOPMENT_NON_RELEASE";;
