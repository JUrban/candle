(* ========================================================================== *)
(* Exact current-checker upper bounds for 128 genuine case-10173 cells.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  Kernel.compute evaluates  *)
(* the production fixed-nonlinear equations, but this diagnostic deliberately *)
(* stops before the general soundness handoff and contributes no proof claim. *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_bound_tightness_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;

let candle_cv_fsn_variable_job_bound_def = new_definition
 `candle_cv_fsn_variable_job_bound source_program job =
    Cexp_if
      (candle_cv_analytic_program_sqrt_data_exact
        (Cexp_fst job) source_program)
      (let box_patched =
         candle_cv_analytic_program_patch_sqrt
           (Cexp_fst job) source_program in
       Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst (Cexp_snd job)) source_program)
         (let center_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_snd job)) source_program in
          candle_cv_fsn_certified_check
            (Cexp_snd center_patched) (Cexp_snd box_patched)
            (Cexp_snd (Cexp_snd job)))
         (Cexp_pair (Cexp_num 0) (Cexp_num 0)))
      (Cexp_pair (Cexp_num 0) (Cexp_num 0))`;;

let candle_cv_fsn_variable_jobs_bounds_def = define
 `(candle_cv_fsn_variable_jobs_bounds source_program (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fsn_variable_jobs_bounds source_program (Cexp_pair job jobs) =
     Cexp_pair
       (candle_cv_fsn_variable_job_bound source_program job)
       (candle_cv_fsn_variable_jobs_bounds source_program jobs))`;;

let candle_cv_fsn_variable_jobs_bounds_compute = prove
 (`!source_program jobs.
     candle_cv_fsn_variable_jobs_bounds source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (candle_cv_fsn_variable_job_bound source_program (Cexp_fst jobs))
         (candle_cv_fsn_variable_jobs_bounds source_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fsn_variable_jobs_bounds_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let rec candle_case10173_bound_prefix_take count items =
  if count = 0 then [] else
  match items with
  | [] -> failwith "case10173 bound tightness: short cell plan"
  | head :: tail -> head :: candle_case10173_bound_prefix_take (count - 1) tail;;

let rec candle_case10173_bound_dest_list term =
  if aconv term `Cexp_num 0` then [] else
  let head,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 bound result list" term in
  head :: candle_case10173_bound_dest_list tail;;

let candle_case10173_bound_dest_num term =
  let constructor,arguments = strip_comb term in
  if not (aconv constructor `Cexp_num`) then
    failwith "case10173 bound result: expected numeral";
  match arguments with
  | [value] -> dest_numeral value
  | _ -> failwith "case10173 bound result: malformed numeral";;

let candle_case10173_bound_rational term =
  let signed,denominator_predecessor =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 bound rational" term in
  let positive,negative =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 bound signed numerator" signed in
  let numerator =
    Num.sub_num
      (candle_case10173_bound_dest_num positive)
      (candle_case10173_bound_dest_num negative) in
  let denominator =
    Num.add_num
      (candle_case10173_bound_dest_num denominator_predecessor)
      (Num.num_of_int 1) in
  Num.div_num numerator denominator;;

let rec candle_case10173_bound_emit index = function
  | [] -> ()
  | item :: remaining ->
      let domain,upper =
        candle_q_dim_stable_program_dest_cval_pair
          "case10173 bound item" item in
      if not (aconv domain `Cexp_num 1`) then
        failwith "case10173 bound result: rejected domain";
      print_endline
        ("CANDLE_CV_NL_REFLECTED_BOUND\t10173\t" ^ string_of_int index ^
         "\t" ^ Num.string_of_num (candle_case10173_bound_rational upper));
      candle_case10173_bound_emit (index + 1) remaining;;

let candle_case10173_bound_prefix128_theorem : thm option ref = ref None;;

let _ =
  let axioms_before = axioms () in
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-bound-tightness-prefix128" ^
         " phase=" ^ event));
  candle_q_dim_analytic_jet_profile_event "plan-begin";
  let plan = candle_case10173_variable_raw_plan () in
  let cells =
    candle_case10173_bound_prefix_take 128
      plan.case10173_variable_raw_plan_cells in
  candle_q_dim_analytic_jet_profile_event "plan-end";
  candle_q_dim_analytic_jet_profile_event "encoding-begin";
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_q_dim_analytic_jet_profile_event "encoding-end";
  let call =
    list_mk_comb
      (`candle_cv_fsn_variable_jobs_bounds`,
       [plan.case10173_variable_raw_plan_prepared.program_representation_term;
        encoded_jobs]) in
  let equations =
    map (REWRITE_RULE [LET_END_DEF])
      (union candle_cv_fixed_nonlinear_compute_eqs
        (map SPEC_ALL
          [candle_cv_fsn_variable_job_bound_def;
           candle_cv_fsn_variable_jobs_bounds_compute])) in
  candle_q_dim_analytic_jet_profile_event "kernel-compute-begin";
  let theorem = candle_q_dim_analytic_jet_compute equations call in
  candle_q_dim_analytic_jet_profile_event "kernel-compute-end";
  candle_case10173_bound_prefix128_theorem := Some theorem;
  let results = candle_case10173_bound_dest_list (rand (concl theorem)) in
  if hyp theorem <> [] || length results <> 128 then
    failwith "case10173 bound tightness: result shape";
  candle_case10173_bound_emit 0 results;
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 bound tightness: axiom-set drift";
  print_endline
    "CANDLE_CV_CASE10173_BOUND_TIGHTNESS_PREFIX128_OK DEVELOPMENT_NON_RELEASE cells=128 assumptions=0 axiom_growth=0";;

end;;
