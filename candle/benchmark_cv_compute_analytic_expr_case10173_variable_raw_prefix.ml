(* ========================================================================== *)
(* Bounded genuine-prefix check for the case-10173 raw-data plan.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This checks the first 128 final cells using   *)
(* one authenticated source program and canonical certificate data.          *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_variable_raw_prefix = struct

open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-variable-raw-prefix" ^
       " phase=" ^ event));;

let rec candle_case10173_variable_raw_take count items =
  if count = 0 then [] else
  match items with
  | [] -> failwith "case10173 variable raw prefix: short plan"
  | head :: tail ->
      head :: candle_case10173_variable_raw_take (count - 1) tail;;

let _ =
  let axioms_before = axioms () in
  let plan = candle_case10173_variable_raw_plan () in
  let cells =
    candle_case10173_variable_raw_take 128
      plan.case10173_variable_raw_plan_cells in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
      plan.case10173_variable_raw_plan_prepared cells in
  let axioms_after = axioms () in
  if hyp result.variable_raw_accept_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith "case10173 variable raw prefix: theorem validation failed";
  print_endline
    "CANDLE_CV_CASE10173_VARIABLE_RAW_PREFIX_OK DEVELOPMENT_NON_RELEASE cells=128 accepted=1 assumptions=0 axiom_growth=0";;

end;;
