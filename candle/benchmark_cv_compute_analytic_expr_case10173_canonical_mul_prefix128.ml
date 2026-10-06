(* ========================================================================== *)
(* Matched canonical-signed-product discriminator on genuine case 10173.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The baseline and candidate use the same       *)
(* encoded 128 jobs.  A proved redirect uses one product for canonical signed*)
(* operands and the existing generic rule for every noncanonical operand.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_canonical_mul_compute.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_case10173_bound_tightness_prefix128.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_canonical_mul_prefix128 = struct

open Candle_cv_analytic_expr_fixed_scale_canonical_mul_compute;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Benchmark_cv_compute_analytic_expr_case10173_bound_tightness_prefix128;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;

let _ =
  let axioms_before = axioms () in
  let baseline =
    match !candle_case10173_bound_prefix128_theorem with
    | Some theorem -> theorem
    | None -> failwith "case10173 canonical mul: baseline unavailable" in
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-canonical-mul-prefix128" ^
         " phase=" ^ event));
  candle_q_dim_analytic_jet_profile_event "encoding-begin";
  let plan = candle_case10173_variable_raw_plan () in
  let cells =
    candle_case10173_bound_prefix_take 128
      plan.case10173_variable_raw_plan_cells in
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_q_dim_analytic_jet_profile_event "encoding-end";
  let call =
    list_mk_comb
      (`candle_cv_fsn_variable_jobs_bounds`,
       [plan.case10173_variable_raw_plan_prepared.program_representation_term;
        encoded_jobs]) in
  (* Kernel.compute requires one user equation per function name.  Replace
     exactly the generic raw-product equation by its proved redirect; the
     redirected function retains the original formula as its fallback. *)
  let base_equations =
    union candle_cv_fixed_nonlinear_compute_eqs
      (map SPEC_ALL
        [candle_cv_fsn_variable_job_bound_def;
         candle_cv_fsn_variable_jobs_bounds_compute]) in
  let raw_mul_conclusion = concl (SPEC_ALL candle_cv_fs_raw_mul_def) in
  let retained,removed =
    List.partition
      (fun theorem -> not (aconv (concl theorem) raw_mul_conclusion))
      base_equations in
  if length removed <> 1 then
    failwith "case10173 canonical mul: raw equation identity drift";
  let equations =
    map (REWRITE_RULE [LET_END_DEF])
      (retained @ candle_cv_fs_canonical_raw_mul_compute_eqs) in
  candle_q_dim_analytic_jet_profile_event "kernel-compute-begin";
  let candidate = candle_q_dim_analytic_jet_compute equations call in
  candle_q_dim_analytic_jet_profile_event "kernel-compute-end";
  if hyp candidate <> [] ||
     not (aconv (rand (concl baseline)) (rand (concl candidate))) then
    failwith "case10173 canonical mul: exact result mismatch";
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 canonical mul: axiom-set drift";
  print_endline
    "CANDLE_CV_CASE10173_CANONICAL_MUL_PREFIX128_OK DEVELOPMENT_NON_RELEASE cells=128 exact_match=1 assumptions=0 axiom_growth=0";;

end;;
