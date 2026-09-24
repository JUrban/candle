(* ========================================================================== *)
(* Behavioral regression for the universal analytic calculus bridge.         *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_calculus.ml";;

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;

let candle_analytic_calculus_axioms_before = axioms ();;

let candle_analytic_calculus_fixture =
 `Candle_analytic_sqrt 2 0 0 2 0 0
    (Candle_analytic_add
      (Candle_analytic_inv
        (Candle_analytic_poly
          (Candle_poly_add
            (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
      (Candle_analytic_poly (Candle_poly_const 3 0 0)))`;;

let candle_analytic_calculus_valid = prove
 (list_mk_comb
    (`candle_analytic_valid_dim`,
     [`1`;candle_analytic_calculus_fixture]),
  REWRITE_TAC[candle_analytic_valid_dim_def;
              candle_poly_valid_dim_def] THEN ARITH_TAC);;

let candle_analytic_calculus_regular = prove
 (list_mk_comb
    (`candle_analytic_regular_at`,
     [`[(&0)]`;candle_analytic_calculus_fixture]),
  REWRITE_TAC[candle_analytic_regular_at_def;
              candle_analytic_value_def; candle_poly_value_list_def;
              candle_q_real_def; candle_q_den_def; candle_lc_zreal_def;
              candle_q_real_lookup_def] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let candle_analytic_calculus_vec0_env = prove
 (`list_of_seq (\k. (vec 0:real^1)$(k + 1)) (dimindex (:1)) = [&0]`,
  REWRITE_TAC[DIMINDEX_1; num_CONV `1`; list_of_seq; APPEND;
              VEC_COMPONENT]);;

let candle_analytic_calculus_diff2c =
  MATCH_MP
    (REWRITE_RULE[DIMINDEX_1; candle_analytic_calculus_vec0_env]
      (ISPECL [candle_analytic_calculus_fixture; `vec 0:real^1`]
        candle_analytic_denote_dim_diff2c))
    (CONJ candle_analytic_calculus_valid candle_analytic_calculus_regular);;

if hyp candle_analytic_calculus_diff2c <> [] then
  failwith "analytic calculus bridge: theorem assumptions";;

let candle_analytic_calculus_axioms_after = axioms ();;
if length candle_analytic_calculus_axioms_after <>
     length candle_analytic_calculus_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_calculus_axioms_before)
       candle_analytic_calculus_axioms_after) then
  failwith "analytic calculus bridge: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_EXPR_CALCULUS_RESULT constructors=7 nested_depth=4 diff2c=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_EXPR_CALCULUS_OK";;
