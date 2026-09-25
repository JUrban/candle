(* ========================================================================== *)
(* Focused reflected-GCD fuel benchmark.                                     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The production normalizer currently carries  *)
(* its bounded Euclidean fuel as a 128-cell cval list.  This experiment keeps *)
(* the same Euclidean recurrence and exact result, but carries the countdown  *)
(* as HOL num data.  Repeated Fibonacci inputs force a long, representative  *)
(* Euclidean path and make evaluator setup negligible.                       *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_rational_normalize_extended.ml";;
needs "candle/cv_compute_analytic_expr_jet_prove.ml";;

module Candle_cv_exact_rational_gcd_fuel_benchmark = struct

open Candle_cv_exact_rational_normalize;;
open Candle_cv_exact_rational_normalize_extended;;
open Candle_cv_analytic_expr_jet_prove;;

let candle_cv_num_gcd_state_fuel_numeric_aux_def = define
 `(candle_cv_num_gcd_state_fuel_numeric_aux 0 a b = Cexp_pair a b) /\
  (candle_cv_num_gcd_state_fuel_numeric_aux (SUC fuel) a b =
     Cexp_if (Cexp_eq b (Cexp_num 0)) (Cexp_pair a b)
       (candle_cv_num_gcd_state_fuel_numeric_aux fuel b (Cexp_mod a b)))`;;

let candle_cv_num_gcd_state_fuel_numeric_def = define
 `(candle_cv_num_gcd_state_fuel_numeric (Cexp_num fuel) a b =
     candle_cv_num_gcd_state_fuel_numeric_aux fuel a b) /\
  (candle_cv_num_gcd_state_fuel_numeric (Cexp_pair h t) a b =
     Cexp_pair a b)`;;

let candle_cv_num_gcd_state_fuel_numeric_compute = prove
 (`!fuel a b.
     candle_cv_num_gcd_state_fuel_numeric fuel a b =
     Cexp_if (Cexp_ispair fuel) (Cexp_pair a b)
       (Cexp_if (Cexp_eq fuel (Cexp_num 0)) (Cexp_pair a b)
         (Cexp_if (Cexp_eq b (Cexp_num 0)) (Cexp_pair a b)
           (candle_cv_num_gcd_state_fuel_numeric
             (Cexp_sub fuel (Cexp_num 1)) b (Cexp_mod a b))))`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `fuel:cval` (cases "cval")) THENL
   [MP_TAC (SPEC `a:num` num_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_num_gcd_state_fuel_numeric_def;
                candle_cv_num_gcd_state_fuel_numeric_aux_def;
                cexp_if_def; cexp_ispair_def; cexp_eq_def;
                cexp_sub_def; distinctness "cval"; injectivity "cval";
                NOT_SUC; ARITH_RULE `SUC n - 1 = n`];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_num_gcd_state_fuel_numeric_def;
                cexp_if_def; cexp_ispair_def]]);;

let candle_cv_num_gcd_state_fuel_numeric_correct = prove
 (`!fuel a b.
     candle_cv_num_gcd_state_fuel_numeric_aux fuel
       (Cexp_num a) (Cexp_num b) =
     Cexp_pair
       (Cexp_num (FST (candle_num_gcd_state_fuel fuel a b)))
       (Cexp_num (SND (candle_num_gcd_state_fuel fuel a b)))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_num_gcd_state_fuel_numeric_aux_def;
                candle_num_gcd_state_fuel_def; FST; SND];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_num_gcd_state_fuel_numeric_aux_def;
                candle_num_gcd_state_fuel_def;
                cexp_eq_def; injectivity "cval"; cexp_mod_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def; FST; SND]]);;

let candle_cv_num_gcd_state_chunk_numeric_def = new_definition
 `candle_cv_num_gcd_state_chunk_numeric a b =
    candle_cv_num_gcd_state_fuel_numeric (Cexp_num 128) a b`;;

let candle_cv_gcd_fuel_benchmark_pair_def = define
 `(candle_cv_gcd_fuel_benchmark_pair (Cexp_num n) a b = Cexp_num 0) /\
  (candle_cv_gcd_fuel_benchmark_pair (Cexp_pair h t) a b =
     Cexp_pair (candle_cv_num_gcd_state_chunk a b)
       (candle_cv_gcd_fuel_benchmark_pair t a b))`;;

let candle_cv_gcd_fuel_benchmark_numeric_def = define
 `(candle_cv_gcd_fuel_benchmark_numeric (Cexp_num n) a b = Cexp_num 0) /\
  (candle_cv_gcd_fuel_benchmark_numeric (Cexp_pair h t) a b =
     Cexp_pair (candle_cv_num_gcd_state_chunk_numeric a b)
       (candle_cv_gcd_fuel_benchmark_numeric t a b))`;;

let candle_cv_gcd_fuel_benchmark_pair_compute = prove
 (`!count a b.
     candle_cv_gcd_fuel_benchmark_pair count a b =
     Cexp_if (Cexp_ispair count)
       (Cexp_pair (candle_cv_num_gcd_state_chunk a b)
         (candle_cv_gcd_fuel_benchmark_pair (Cexp_snd count) a b))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `count:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_gcd_fuel_benchmark_pair_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_gcd_fuel_benchmark_numeric_compute = prove
 (`!count a b.
     candle_cv_gcd_fuel_benchmark_numeric count a b =
     Cexp_if (Cexp_ispair count)
       (Cexp_pair (candle_cv_num_gcd_state_chunk_numeric a b)
         (candle_cv_gcd_fuel_benchmark_numeric (Cexp_snd count) a b))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `count:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_gcd_fuel_benchmark_numeric_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_gcd_fuel_benchmark_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=gcd-fuel scope=repeat-512 phase=" ^ phase ^
     " event=" ^ event);;

let candle_cv_gcd_fuel_benchmark_equations =
  map SPEC_ALL
   [candle_cv_num_gcd_state_fuel_compute;
    candle_cv_num_gcd_state_chunk_def;
    candle_cv_num_gcd_state_fuel_numeric_compute;
    candle_cv_num_gcd_state_chunk_numeric_def;
    candle_cv_gcd_fuel_benchmark_pair_compute;
    candle_cv_gcd_fuel_benchmark_numeric_compute];;

(* Consecutive Fibonacci numbers take 92 Euclidean remainder steps. *)
let candle_cv_gcd_fuel_benchmark_a = `Cexp_num 12200160415121876738`;;
let candle_cv_gcd_fuel_benchmark_b = `Cexp_num 7540113804746346429`;;

let candle_cv_gcd_fuel_benchmark_repetitions =
  itlist
    (fun _ tail -> list_mk_comb (`Cexp_pair`,[`Cexp_num 0`;tail]))
    (1--512) `Cexp_num 0`;;

let candle_cv_gcd_fuel_benchmark_pair_call =
  list_mk_comb
    (`candle_cv_gcd_fuel_benchmark_pair`,
     [candle_cv_gcd_fuel_benchmark_repetitions;
      candle_cv_gcd_fuel_benchmark_a;
      candle_cv_gcd_fuel_benchmark_b]);;

let candle_cv_gcd_fuel_benchmark_numeric_call =
  list_mk_comb
    (`candle_cv_gcd_fuel_benchmark_numeric`,
     [candle_cv_gcd_fuel_benchmark_repetitions;
      candle_cv_gcd_fuel_benchmark_a;
      candle_cv_gcd_fuel_benchmark_b]);;

let _ = candle_cv_gcd_fuel_benchmark_marker "pair-fuel" "begin";;
let candle_cv_gcd_fuel_benchmark_pair_result =
  candle_q_dim_analytic_jet_compute
    candle_cv_gcd_fuel_benchmark_equations
    candle_cv_gcd_fuel_benchmark_pair_call;;
let _ = candle_cv_gcd_fuel_benchmark_marker "pair-fuel" "end";;

let _ = candle_cv_gcd_fuel_benchmark_marker "numeric-fuel" "begin";;
let candle_cv_gcd_fuel_benchmark_numeric_result =
  candle_q_dim_analytic_jet_compute
    candle_cv_gcd_fuel_benchmark_equations
    candle_cv_gcd_fuel_benchmark_numeric_call;;
let _ = candle_cv_gcd_fuel_benchmark_marker "numeric-fuel" "end";;

if hyp candle_cv_gcd_fuel_benchmark_pair_result <> [] ||
   hyp candle_cv_gcd_fuel_benchmark_numeric_result <> [] ||
   not
     (aconv (rand (concl candle_cv_gcd_fuel_benchmark_pair_result))
            (rand (concl candle_cv_gcd_fuel_benchmark_numeric_result))) then
  failwith "reflected GCD fuel benchmark: exact result mismatch";;

print_endline
  "CANDLE_CV_GCD_FUEL_BENCHMARK_RESULT repeats=512 euclid_steps=92 exact_match=1";;
print_endline "CANDLE_CV_GCD_FUEL_BENCHMARK_OK DEVELOPMENT_NON_RELEASE";;

end;;
