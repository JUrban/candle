(* ========================================================================== *)
(* Upper-bound discriminator for repeated exact-slot walks on case 10173.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The candidate deliberately *)
(* omits exact square-root-slot validation on already authenticated valid     *)
(* input.  It retains both program patches, the full certified Taylor check,  *)
(* and topology validation.  Its result may guide implementation work but     *)
(* must never contribute theorem evidence.                                    *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_skip_exact_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_topology;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_cv_fso_variable_jobs_check_skip_exact_def = define
 `(candle_cv_fso_variable_jobs_check_skip_exact
      source_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fso_variable_jobs_check_skip_exact source_program
      (Cexp_pair job jobs) =
     let box_patched =
       candle_cv_analytic_program_patch_sqrt
         (Cexp_fst job) source_program in
     let center_patched =
       candle_cv_analytic_program_patch_sqrt
         (Cexp_fst (Cexp_snd job)) source_program in
     Cexp_if
       (Cexp_fst
         (candle_cv_fso_certified_check
           (Cexp_snd center_patched) (Cexp_snd box_patched)
           (Cexp_snd (Cexp_snd job))))
       (candle_cv_fso_variable_jobs_check_skip_exact source_program jobs)
       (Cexp_num 0))`;;

let candle_cv_fso_variable_jobs_check_skip_exact_compute = prove
 (`!source_program jobs.
     candle_cv_fso_variable_jobs_check_skip_exact source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (let job = Cexp_fst jobs in
        let box_patched =
          candle_cv_analytic_program_patch_sqrt
            (Cexp_fst job) source_program in
        let center_patched =
          candle_cv_analytic_program_patch_sqrt
            (Cexp_fst (Cexp_snd job)) source_program in
        Cexp_if
          (Cexp_fst
            (candle_cv_fso_certified_check
              (Cexp_snd center_patched) (Cexp_snd box_patched)
              (Cexp_snd (Cexp_snd job))))
          (candle_cv_fso_variable_jobs_check_skip_exact
            source_program (Cexp_snd jobs))
          (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_variable_jobs_check_skip_exact_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
     LET_DEF;LET_END_DEF]);;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_skip_exact_def =
  new_definition
   `candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_skip_exact
        source_program tree_dim tokens encoded_jobs =
      Cexp_pair
        (candle_cv_fso_variable_jobs_check_skip_exact
          source_program encoded_jobs)
        (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
          tree_dim tokens encoded_jobs (Cexp_num 0))`;;

let candle_case10173_skip_exact_complete_compute_eqs () =
  union
    (union candle_cv_fso_compute_eqs
      [REWRITE_RULE [LET_END_DEF]
        (SPEC_ALL candle_cv_fso_variable_jobs_check_skip_exact_compute)])
    (union
      candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs
      [SPEC_ALL
        candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_skip_exact_def]);;

let rec candle_case10173_skip_exact_cval_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 skip-exact prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_skip_exact_cval_take (count - 1) tail);;

let rec candle_case10173_skip_exact_prefix_tokens leaves reversed items =
  if leaves = 0 then rev reversed else
  match items with
  | [] -> failwith "case10173 skip-exact prefix: short topology"
  | token :: remaining ->
      (match token with
       | Candle_case10173_complete_leaf ->
           candle_case10173_skip_exact_prefix_tokens
             (leaves - 1) (token :: reversed) remaining
       | Candle_case10173_complete_glue _ ->
           candle_case10173_skip_exact_prefix_tokens
             leaves (token :: reversed) remaining);;

let candle_case10173_skip_exact_validate call theorem =
  hyp theorem = [] && aconv (lhand (concl theorem)) call;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-skip-exact-prefix128" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let token_data =
    candle_case10173_skip_exact_prefix_tokens 128 []
      (candle_case10173_complete_token_data ()) in
  if length token_data <> 250 then
    failwith "case10173 skip-exact prefix: topology drift";
  let encoded_jobs =
    candle_case10173_skip_exact_cval_take 128
      captured.case10173_complete_encoded_jobs in
  let encoded_tokens =
    candle_case10173_skip_exact_cval_take (length token_data)
      captured.case10173_complete_encoded_tokens in
  let prepared = captured.case10173_complete_prepared in
  let arguments =
    [prepared.program_representation_term;
     `Cexp_num 6`;encoded_tokens;encoded_jobs] in
  let established_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
       arguments) in
  candle_q_dim_analytic_jet_profile_event
    "skip-exact-prefix128-established-compute-begin";
  let established =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
      established_call in
  candle_q_dim_analytic_jet_profile_event
    "skip-exact-prefix128-established-compute-end";
  let candidate_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_skip_exact`,
       arguments) in
  candle_q_dim_analytic_jet_profile_event
    "skip-exact-prefix128-candidate-compute-begin";
  let candidate =
    candle_q_dim_analytic_jet_compute
      (candle_case10173_skip_exact_complete_compute_eqs ()) candidate_call in
  candle_q_dim_analytic_jet_profile_event
    "skip-exact-prefix128-candidate-compute-end";
  let axioms_after = axioms () in
  if not (candle_case10173_skip_exact_validate established_call established) ||
     not (candle_case10173_skip_exact_validate candidate_call candidate) ||
     not (aconv (rand (concl established)) (rand (concl candidate))) ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 skip-exact prefix: result mismatch";
  print_endline
    "CANDLE_CV_CASE10173_SKIP_EXACT_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 token_items=250 matched=1 assumptions=0 axiom_growth=0";;

end;;
