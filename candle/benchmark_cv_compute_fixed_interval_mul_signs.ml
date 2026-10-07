(* ========================================================================== *)
(* Reflected fixed-scale sign-classified interval-product discriminator.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This deliberately precedes the semantic proof *)
(* and production integration.  It compares the existing four-endpoint      *)
(* operation with the classical two-endpoint cases selected by interval     *)
(* signs.  The both-straddling case delegates to the existing definition.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;
needs "candle/cv_compute_analytic_expr_jet_prove.ml";;

open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_jet_prove;;

let candle_cv_fs_raw_interval_mul_sign_def = new_definition
 `candle_cv_fs_raw_interval_mul_sign x y =
    Cexp_if
      (candle_cv_fs_raw_le candle_cv_fs_zero (Cexp_fst x))
      (Cexp_if
        (candle_cv_fs_raw_le candle_cv_fs_zero (Cexp_fst y))
        (Cexp_pair
          (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_fst y))
          (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_snd y)))
        (Cexp_if
          (candle_cv_fs_raw_le (Cexp_snd y) candle_cv_fs_zero)
          (Cexp_pair
            (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_fst y))
            (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_snd y)))
          (Cexp_pair
            (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_fst y))
            (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_snd y)))))
      (Cexp_if
        (candle_cv_fs_raw_le (Cexp_snd x) candle_cv_fs_zero)
        (Cexp_if
          (candle_cv_fs_raw_le candle_cv_fs_zero (Cexp_fst y))
          (Cexp_pair
            (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_snd y))
            (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_fst y)))
          (Cexp_if
            (candle_cv_fs_raw_le (Cexp_snd y) candle_cv_fs_zero)
            (Cexp_pair
              (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_snd y))
              (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_fst y)))
            (Cexp_pair
              (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_snd y))
              (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_fst y)))))
        (Cexp_if
          (candle_cv_fs_raw_le candle_cv_fs_zero (Cexp_fst y))
          (Cexp_pair
            (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_snd y))
            (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_snd y)))
          (Cexp_if
            (candle_cv_fs_raw_le (Cexp_snd y) candle_cv_fs_zero)
            (Cexp_pair
              (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_fst y))
              (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_fst y)))
            (candle_cv_fs_raw_interval_mul x y))))`;;

let candle_cv_fs_interval_mul_sign_size_def = define
 `(candle_cv_fs_interval_mul_sign_size (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fs_interval_mul_sign_size (Cexp_pair h t) =
    Cexp_add
      (candle_cv_fs_interval_mul_sign_size h)
      (candle_cv_fs_interval_mul_sign_size t))`;;

let candle_cv_fs_interval_mul_sign_size_compute = prove
 (`!value.
     candle_cv_fs_interval_mul_sign_size value =
     Cexp_if (Cexp_ispair value)
       (Cexp_add
         (candle_cv_fs_interval_mul_sign_size (Cexp_fst value))
         (candle_cv_fs_interval_mul_sign_size (Cexp_snd value)))
       (Cexp_num 1)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `value:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_mul_sign_size_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_interval_mul_current_repeat_def = define
 `(candle_cv_fs_interval_mul_current_repeat (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_interval_mul_current_repeat (Cexp_pair h t) =
    Cexp_add
      (candle_cv_fs_interval_mul_sign_size
        (candle_cv_fs_raw_interval_mul (Cexp_fst h) (Cexp_snd h)))
      (candle_cv_fs_interval_mul_current_repeat t))`;;

let candle_cv_fs_interval_mul_current_repeat_compute = prove
 (`!items.
     candle_cv_fs_interval_mul_current_repeat items =
     Cexp_if (Cexp_ispair items)
       (Cexp_add
         (candle_cv_fs_interval_mul_sign_size
           (candle_cv_fs_raw_interval_mul
             (Cexp_fst (Cexp_fst items))
             (Cexp_snd (Cexp_fst items))))
         (candle_cv_fs_interval_mul_current_repeat (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_mul_current_repeat_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_interval_mul_sign_repeat_def = define
 `(candle_cv_fs_interval_mul_sign_repeat (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_interval_mul_sign_repeat (Cexp_pair h t) =
    Cexp_add
      (candle_cv_fs_interval_mul_sign_size
        (candle_cv_fs_raw_interval_mul_sign (Cexp_fst h) (Cexp_snd h)))
      (candle_cv_fs_interval_mul_sign_repeat t))`;;

let candle_cv_fs_interval_mul_sign_repeat_compute = prove
 (`!items.
     candle_cv_fs_interval_mul_sign_repeat items =
     Cexp_if (Cexp_ispair items)
       (Cexp_add
         (candle_cv_fs_interval_mul_sign_size
           (candle_cv_fs_raw_interval_mul_sign
             (Cexp_fst (Cexp_fst items))
             (Cexp_snd (Cexp_fst items))))
         (candle_cv_fs_interval_mul_sign_repeat (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_mul_sign_repeat_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_interval_mul_sign_equations =
  candle_cv_fs_compute_eqs @
  map SPEC_ALL
   [candle_cv_fs_raw_interval_mul_sign_def;
    candle_cv_fs_interval_mul_sign_size_compute;
    candle_cv_fs_interval_mul_current_repeat_compute;
    candle_cv_fs_interval_mul_sign_repeat_compute];;

let candle_cv_fs_interval_mul_sign_num n = mk_comb (`Cexp_num`,n);;

let candle_cv_fs_interval_mul_sign_z pp nn =
  list_mk_comb
    (`Cexp_pair`,
     [candle_cv_fs_interval_mul_sign_num pp;
      candle_cv_fs_interval_mul_sign_num nn]);;

let candle_cv_fs_interval_mul_sign_interval lo_pp lo_nn hi_pp hi_nn =
  list_mk_comb
    (`Cexp_pair`,
     [candle_cv_fs_interval_mul_sign_z lo_pp lo_nn;
      candle_cv_fs_interval_mul_sign_z hi_pp hi_nn]);;

let candle_cv_fs_interval_mul_sign_positive =
  candle_cv_fs_interval_mul_sign_interval
    `123456789` `0` `987654321` `0`;;

let candle_cv_fs_interval_mul_sign_negative =
  candle_cv_fs_interval_mul_sign_interval
    `0` `987654321` `0` `123456789`;;

let candle_cv_fs_interval_mul_sign_straddling =
  candle_cv_fs_interval_mul_sign_interval
    `0` `246813579` `192837465` `0`;;

let candle_cv_fs_interval_mul_sign_patterns =
  [(candle_cv_fs_interval_mul_sign_positive,
    candle_cv_fs_interval_mul_sign_positive);
   (candle_cv_fs_interval_mul_sign_positive,
    candle_cv_fs_interval_mul_sign_negative);
   (candle_cv_fs_interval_mul_sign_positive,
    candle_cv_fs_interval_mul_sign_straddling);
   (candle_cv_fs_interval_mul_sign_negative,
    candle_cv_fs_interval_mul_sign_positive);
   (candle_cv_fs_interval_mul_sign_negative,
    candle_cv_fs_interval_mul_sign_negative);
   (candle_cv_fs_interval_mul_sign_negative,
    candle_cv_fs_interval_mul_sign_straddling);
   (candle_cv_fs_interval_mul_sign_straddling,
    candle_cv_fs_interval_mul_sign_positive);
   (candle_cv_fs_interval_mul_sign_straddling,
    candle_cv_fs_interval_mul_sign_negative)];;

let candle_cv_fs_interval_mul_sign_items =
  itlist
    (fun index tail ->
      let (left,right) =
        el ((index - 1) mod (length candle_cv_fs_interval_mul_sign_patterns))
          candle_cv_fs_interval_mul_sign_patterns in
      list_mk_comb
        (`Cexp_pair`,
         [list_mk_comb (`Cexp_pair`,[left;right]);tail]))
    (1--4096) `Cexp_num 0`;;

let candle_cv_fs_interval_mul_current_call =
  mk_comb
    (`candle_cv_fs_interval_mul_current_repeat`,
     candle_cv_fs_interval_mul_sign_items);;

let candle_cv_fs_interval_mul_sign_call =
  mk_comb
    (`candle_cv_fs_interval_mul_sign_repeat`,
     candle_cv_fs_interval_mul_sign_items);;

let candle_cv_fs_interval_mul_sign_run lane repetition call =
  print_endline
    ("CANDLE_CERT_PROFILE lane=fixed-interval-mul-sign" ^
     " scope=repeat-4096 phase=" ^ lane ^
     " repetition=" ^ string_of_int repetition ^ " event=begin");
  let started = Unix.gettimeofday () in
  let result =
    candle_q_dim_analytic_jet_compute
      candle_cv_fs_interval_mul_sign_equations call in
  let elapsed = Unix.gettimeofday () -. started in
  print_endline
    ("CANDLE_CERT_PROFILE lane=fixed-interval-mul-sign" ^
     " scope=repeat-4096 phase=" ^ lane ^
     " repetition=" ^ string_of_int repetition ^ " event=end");
  print_endline
    ("CANDLE_CV_FS_INTERVAL_MUL_SIGN_TIMING lane=" ^ lane ^
     " repetition=" ^ string_of_int repetition ^
     " seconds=" ^ string_of_float elapsed);
  result;;

let candle_cv_fs_interval_mul_sign_current_1 =
  candle_cv_fs_interval_mul_sign_run
    "four-endpoint" 1 candle_cv_fs_interval_mul_current_call;;
let candle_cv_fs_interval_mul_sign_candidate_1 =
  candle_cv_fs_interval_mul_sign_run
    "sign-classified" 1 candle_cv_fs_interval_mul_sign_call;;
let candle_cv_fs_interval_mul_sign_candidate_2 =
  candle_cv_fs_interval_mul_sign_run
    "sign-classified" 2 candle_cv_fs_interval_mul_sign_call;;
let candle_cv_fs_interval_mul_sign_current_2 =
  candle_cv_fs_interval_mul_sign_run
    "four-endpoint" 2 candle_cv_fs_interval_mul_current_call;;
let candle_cv_fs_interval_mul_sign_current_3 =
  candle_cv_fs_interval_mul_sign_run
    "four-endpoint" 3 candle_cv_fs_interval_mul_current_call;;
let candle_cv_fs_interval_mul_sign_candidate_3 =
  candle_cv_fs_interval_mul_sign_run
    "sign-classified" 3 candle_cv_fs_interval_mul_sign_call;;
let candle_cv_fs_interval_mul_sign_candidate_4 =
  candle_cv_fs_interval_mul_sign_run
    "sign-classified" 4 candle_cv_fs_interval_mul_sign_call;;
let candle_cv_fs_interval_mul_sign_current_4 =
  candle_cv_fs_interval_mul_sign_run
    "four-endpoint" 4 candle_cv_fs_interval_mul_current_call;;
let candle_cv_fs_interval_mul_sign_current_5 =
  candle_cv_fs_interval_mul_sign_run
    "four-endpoint" 5 candle_cv_fs_interval_mul_current_call;;
let candle_cv_fs_interval_mul_sign_candidate_5 =
  candle_cv_fs_interval_mul_sign_run
    "sign-classified" 5 candle_cv_fs_interval_mul_sign_call;;
let candle_cv_fs_interval_mul_sign_candidate_6 =
  candle_cv_fs_interval_mul_sign_run
    "sign-classified" 6 candle_cv_fs_interval_mul_sign_call;;
let candle_cv_fs_interval_mul_sign_current_6 =
  candle_cv_fs_interval_mul_sign_run
    "four-endpoint" 6 candle_cv_fs_interval_mul_current_call;;
let candle_cv_fs_interval_mul_sign_current_7 =
  candle_cv_fs_interval_mul_sign_run
    "four-endpoint" 7 candle_cv_fs_interval_mul_current_call;;
let candle_cv_fs_interval_mul_sign_candidate_7 =
  candle_cv_fs_interval_mul_sign_run
    "sign-classified" 7 candle_cv_fs_interval_mul_sign_call;;
let candle_cv_fs_interval_mul_sign_candidate_8 =
  candle_cv_fs_interval_mul_sign_run
    "sign-classified" 8 candle_cv_fs_interval_mul_sign_call;;
let candle_cv_fs_interval_mul_sign_current_8 =
  candle_cv_fs_interval_mul_sign_run
    "four-endpoint" 8 candle_cv_fs_interval_mul_current_call;;

let candle_cv_fs_interval_mul_sign_results =
  [candle_cv_fs_interval_mul_sign_current_1;
   candle_cv_fs_interval_mul_sign_candidate_1;
   candle_cv_fs_interval_mul_sign_candidate_2;
   candle_cv_fs_interval_mul_sign_current_2;
   candle_cv_fs_interval_mul_sign_current_3;
   candle_cv_fs_interval_mul_sign_candidate_3;
   candle_cv_fs_interval_mul_sign_candidate_4;
   candle_cv_fs_interval_mul_sign_current_4;
   candle_cv_fs_interval_mul_sign_current_5;
   candle_cv_fs_interval_mul_sign_candidate_5;
   candle_cv_fs_interval_mul_sign_candidate_6;
   candle_cv_fs_interval_mul_sign_current_6;
   candle_cv_fs_interval_mul_sign_current_7;
   candle_cv_fs_interval_mul_sign_candidate_7;
   candle_cv_fs_interval_mul_sign_candidate_8;
   candle_cv_fs_interval_mul_sign_current_8];;

if exists (fun theorem -> hyp theorem <> [])
     candle_cv_fs_interval_mul_sign_results ||
   exists
     (fun theorem ->
       not
         (aconv
           (rand (concl candle_cv_fs_interval_mul_sign_current_1))
           (rand (concl theorem))))
     candle_cv_fs_interval_mul_sign_results then
  failwith "fixed interval multiplication sign discriminator mismatch";;

print_endline
  "CANDLE_CV_FS_INTERVAL_MUL_SIGN_RESULT calls=4096 repetitions=8 exact_match=1";;
print_endline
  "CANDLE_CV_FS_INTERVAL_MUL_SIGN_OK DEVELOPMENT_NON_RELEASE";;
