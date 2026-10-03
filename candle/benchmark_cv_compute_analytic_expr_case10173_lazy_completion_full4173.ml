(* ========================================================================== *)
(* Lazy polynomial-completion integration on genuine case-10173 cells.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The candidate defers dead *)
(* polynomial completions while preserving every required force point.       *)
(* A separate reflected pass requires byte-exact final Taylor results against *)
(* the established evaluator for all 4,173 captured cells.                   *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_lazy.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_lazy_completion_full4173 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_lazy;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_cv_fso_lazy_completion_full4173_variable_jobs_check_def = define
 `(candle_cv_fso_lazy_completion_full4173_variable_jobs_check
      source_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fso_lazy_completion_full4173_variable_jobs_check
      source_program (Cexp_pair job jobs) =
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
           Cexp_if
             (Cexp_fst
               (candle_cv_fsol_certified_check
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job))))
             (candle_cv_fso_lazy_completion_full4173_variable_jobs_check
               source_program jobs)
             (Cexp_num 0))
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fso_lazy_completion_full4173_variable_jobs_check_compute = prove
 (`!source_program jobs.
     candle_cv_fso_lazy_completion_full4173_variable_jobs_check source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst (Cexp_fst jobs)) source_program)
         (let box_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_fst jobs)) source_program in
          Cexp_if
            (candle_cv_analytic_program_sqrt_data_exact
              (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program)
            (let center_patched =
               candle_cv_analytic_program_patch_sqrt
                 (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program in
             Cexp_if
               (Cexp_fst
                 (candle_cv_fsol_certified_check
                   (Cexp_snd center_patched) (Cexp_snd box_patched)
                   (Cexp_snd (Cexp_snd (Cexp_fst jobs)))))
               (candle_cv_fso_lazy_completion_full4173_variable_jobs_check
                 source_program (Cexp_snd jobs))
               (Cexp_num 0))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fso_lazy_completion_full4173_variable_jobs_check_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fso_lazy_completion_full4173_exact_jobs_check_def = define
 `(candle_cv_fso_lazy_completion_full4173_exact_jobs_check
      source_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fso_lazy_completion_full4173_exact_jobs_check
      source_program (Cexp_pair job jobs) =
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
           Cexp_if
             (Cexp_eq
               (candle_cv_fsol_program
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job)))
               (candle_cv_fso_program
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job))))
             (candle_cv_fso_lazy_completion_full4173_exact_jobs_check source_program jobs)
             (Cexp_num 0))
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fso_lazy_completion_full4173_exact_jobs_check_compute = prove
 (`!source_program jobs.
     candle_cv_fso_lazy_completion_full4173_exact_jobs_check source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst (Cexp_fst jobs)) source_program)
         (let box_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_fst jobs)) source_program in
          Cexp_if
            (candle_cv_analytic_program_sqrt_data_exact
              (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program)
            (let center_patched =
               candle_cv_analytic_program_patch_sqrt
                 (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program in
             Cexp_if
               (Cexp_eq
                 (candle_cv_fsol_program
                   (Cexp_snd center_patched) (Cexp_snd box_patched)
                   (Cexp_snd (Cexp_snd (Cexp_fst jobs))))
                 (candle_cv_fso_program
                   (Cexp_snd center_patched) (Cexp_snd box_patched)
                   (Cexp_snd (Cexp_snd (Cexp_fst jobs)))))
               (candle_cv_fso_lazy_completion_full4173_exact_jobs_check
                 source_program (Cexp_snd jobs))
               (Cexp_num 0))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fso_lazy_completion_full4173_exact_jobs_check_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fso_lazy_completion_full4173_raw_jobs_check_def = new_definition
 `candle_cv_fso_lazy_completion_full4173_raw_jobs_check source_program encoded_jobs =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_fso_lazy_completion_full4173_variable_jobs_check
        source_program encoded_jobs)`;;

let candle_cv_fso_lazy_completion_full4173_exact_raw_jobs_check_def = new_definition
 `candle_cv_fso_lazy_completion_full4173_exact_raw_jobs_check source_program encoded_jobs =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_fso_lazy_completion_full4173_exact_jobs_check
        source_program encoded_jobs)`;;

let candle_case10173_lazy_completion_full4173_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fso_variable_raw_compute_eqs
      (union candle_cv_fsol_compute_eqs
        (map SPEC_ALL
          [candle_cv_fso_lazy_completion_full4173_variable_jobs_check_compute;
           candle_cv_fso_lazy_completion_full4173_exact_jobs_check_compute;
           candle_cv_fso_lazy_completion_full4173_raw_jobs_check_def;
           candle_cv_fso_lazy_completion_full4173_exact_raw_jobs_check_def])));;

let rec candle_case10173_lazy_completion_full4173_cval_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 lazy-completion-full4173 prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_lazy_completion_full4173_cval_take (count - 1) tail);;

let candle_case10173_lazy_completion_full4173_validate call theorem =
  hyp theorem = [] && aconv (lhand (concl theorem)) call &&
  aconv (rand (concl theorem)) `Cexp_num 1`;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-lazy-completion-full4173" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let encoded_jobs =
    candle_case10173_lazy_completion_full4173_cval_take 4173
      captured.case10173_complete_encoded_jobs in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  let call name =
    list_mk_comb
      (name,[source_program;encoded_jobs]) in
  let run label name =
    let current_call = call name in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
    let theorem =
      candle_q_dim_analytic_jet_compute
        candle_case10173_lazy_completion_full4173_compute_eqs current_call in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-end");
    if not
         (candle_case10173_lazy_completion_full4173_validate current_call theorem)
    then failwith ("case10173 lazy-completion-full4173: " ^ label ^ " failed");
    theorem in
  let current_1 =
    run "lazy-completion-full4173-current-1"
      `candle_cv_fso_variable_raw_jobs_check` in
  let candidate_1 =
    run "lazy-completion-full4173-candidate-1"
      `candle_cv_fso_lazy_completion_full4173_raw_jobs_check` in
  let exact =
    run "lazy-completion-full4173-exact-results"
      `candle_cv_fso_lazy_completion_full4173_exact_raw_jobs_check` in
  let candidate_2 =
    run "lazy-completion-full4173-candidate-2"
      `candle_cv_fso_lazy_completion_full4173_raw_jobs_check` in
  let current_2 =
    run "lazy-completion-full4173-current-2"
      `candle_cv_fso_variable_raw_jobs_check` in
  let results = [current_1;candidate_1;exact;candidate_2;current_2] in
  let first_result = rand (concl current_1) in
  let axioms_after = axioms () in
  if not (List.for_all (fun th -> aconv (rand (concl th)) first_result)
            results) ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 lazy-completion-full4173: final mismatch";
  print_endline
    "CANDLE_CV_CASE10173_LAZY_COMPLETION_FULL4173_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=4173 current=2 candidate=2 exact_results=4173 accepted=1 assumptions=0 axiom_growth=0";;

end;;
