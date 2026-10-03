(* ========================================================================== *)
(* Lazy polynomial-completion benchmark on genuine case-10173 cells.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The benchmark evaluates   *)
(* all 22 authentic polynomial blocks on 128 authenticated boxes.  A separate *)
(* reflected pass requires exact equality with the established fixed evaluator *)
(* for all 2,816 block/box results.                                            *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_lazy_completion_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_lazy_completion_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_lazy_completion_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_cv_fs_poly_result_checksum_def = new_definition
 `candle_cv_fs_poly_result_checksum result =
    Cexp_add
      (Cexp_fst (Cexp_snd (candle_cv_fs_result_value_bound result)))
      (Cexp_snd (Cexp_snd (candle_cv_fs_result_value_bound result)))`;;

let candle_cv_fs_poly_source_checksum_current_def = define
 `(candle_cv_fs_poly_source_checksum_current
     center_boxes radii (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_poly_source_checksum_current
     center_boxes radii (Cexp_pair instruction instructions) =
     Cexp_if (Cexp_ispair instruction)
       (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
         (Cexp_add
           (candle_cv_fs_poly_result_checksum
             (candle_cv_fs_poly_program
               center_boxes radii (Cexp_snd instruction)))
           (candle_cv_fs_poly_source_checksum_current
             center_boxes radii instructions))
         (candle_cv_fs_poly_source_checksum_current
           center_boxes radii instructions))
       (candle_cv_fs_poly_source_checksum_current
         center_boxes radii instructions))`;;

let candle_cv_fs_poly_source_checksum_current_compute = prove
 (`!center_boxes radii program.
     candle_cv_fs_poly_source_checksum_current center_boxes radii program =
     Cexp_if (Cexp_ispair program)
       (Cexp_if (Cexp_ispair (Cexp_fst program))
         (Cexp_if
           (Cexp_eq (Cexp_fst (Cexp_fst program)) (Cexp_num 0))
           (Cexp_add
             (candle_cv_fs_poly_result_checksum
               (candle_cv_fs_poly_program center_boxes radii
                 (Cexp_snd (Cexp_fst program))))
             (candle_cv_fs_poly_source_checksum_current
               center_boxes radii (Cexp_snd program)))
           (candle_cv_fs_poly_source_checksum_current
             center_boxes radii (Cexp_snd program)))
         (candle_cv_fs_poly_source_checksum_current
           center_boxes radii (Cexp_snd program)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_source_checksum_current_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_poly_source_checksum_lazy_def = define
 `(candle_cv_fs_poly_source_checksum_lazy
     center_boxes radii (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_poly_source_checksum_lazy
     center_boxes radii (Cexp_pair instruction instructions) =
     Cexp_if (Cexp_ispair instruction)
       (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
         (Cexp_add
           (candle_cv_fs_poly_result_checksum
             (candle_cv_fs_poly_program_lazy
               center_boxes radii (Cexp_snd instruction)))
           (candle_cv_fs_poly_source_checksum_lazy
             center_boxes radii instructions))
         (candle_cv_fs_poly_source_checksum_lazy
           center_boxes radii instructions))
       (candle_cv_fs_poly_source_checksum_lazy
         center_boxes radii instructions))`;;

let candle_cv_fs_poly_source_checksum_lazy_compute = prove
 (`!center_boxes radii program.
     candle_cv_fs_poly_source_checksum_lazy center_boxes radii program =
     Cexp_if (Cexp_ispair program)
       (Cexp_if (Cexp_ispair (Cexp_fst program))
         (Cexp_if
           (Cexp_eq (Cexp_fst (Cexp_fst program)) (Cexp_num 0))
           (Cexp_add
             (candle_cv_fs_poly_result_checksum
               (candle_cv_fs_poly_program_lazy center_boxes radii
                 (Cexp_snd (Cexp_fst program))))
             (candle_cv_fs_poly_source_checksum_lazy
               center_boxes radii (Cexp_snd program)))
           (candle_cv_fs_poly_source_checksum_lazy
             center_boxes radii (Cexp_snd program)))
         (candle_cv_fs_poly_source_checksum_lazy
           center_boxes radii (Cexp_snd program)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_source_checksum_lazy_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_poly_source_exact_def = define
 `(candle_cv_fs_poly_source_exact
     center_boxes radii (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fs_poly_source_exact
     center_boxes radii (Cexp_pair instruction instructions) =
     Cexp_if (Cexp_ispair instruction)
       (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
         (Cexp_if
           (Cexp_eq
             (candle_cv_fs_poly_program
               center_boxes radii (Cexp_snd instruction))
             (candle_cv_fs_poly_program_lazy
               center_boxes radii (Cexp_snd instruction)))
           (candle_cv_fs_poly_source_exact
             center_boxes radii instructions)
           (Cexp_num 0))
         (candle_cv_fs_poly_source_exact
           center_boxes radii instructions))
       (candle_cv_fs_poly_source_exact
         center_boxes radii instructions))`;;

let candle_cv_fs_poly_source_exact_compute = prove
 (`!center_boxes radii program.
     candle_cv_fs_poly_source_exact center_boxes radii program =
     Cexp_if (Cexp_ispair program)
       (Cexp_if (Cexp_ispair (Cexp_fst program))
         (Cexp_if
           (Cexp_eq (Cexp_fst (Cexp_fst program)) (Cexp_num 0))
           (Cexp_if
             (Cexp_eq
               (candle_cv_fs_poly_program center_boxes radii
                 (Cexp_snd (Cexp_fst program)))
               (candle_cv_fs_poly_program_lazy center_boxes radii
                 (Cexp_snd (Cexp_fst program))))
             (candle_cv_fs_poly_source_exact
               center_boxes radii (Cexp_snd program))
             (Cexp_num 0))
           (candle_cv_fs_poly_source_exact
             center_boxes radii (Cexp_snd program)))
         (candle_cv_fs_poly_source_exact
           center_boxes radii (Cexp_snd program)))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_source_exact_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_poly_jobs_checksum_current_def = define
 `(candle_cv_fs_poly_jobs_checksum_current
     source_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_poly_jobs_checksum_current
     source_program (Cexp_pair job jobs) =
     let boxes = Cexp_snd (Cexp_snd job) in
     Cexp_add
       (candle_cv_fs_poly_source_checksum_current
         (candle_cv_q_center_environment_list boxes)
         (candle_cv_q_fixed_list_round_upper (candle_cv_q_radius_list boxes))
         source_program)
       (candle_cv_fs_poly_jobs_checksum_current source_program jobs))`;;

let candle_cv_fs_poly_jobs_checksum_current_compute = prove
 (`!source_program jobs.
     candle_cv_fs_poly_jobs_checksum_current source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (let boxes = Cexp_snd (Cexp_snd (Cexp_fst jobs)) in
        Cexp_add
          (candle_cv_fs_poly_source_checksum_current
            (candle_cv_q_center_environment_list boxes)
            (candle_cv_q_fixed_list_round_upper
              (candle_cv_q_radius_list boxes)) source_program)
          (candle_cv_fs_poly_jobs_checksum_current
            source_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_jobs_checksum_current_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fs_poly_jobs_checksum_lazy_def = define
 `(candle_cv_fs_poly_jobs_checksum_lazy
     source_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_poly_jobs_checksum_lazy
     source_program (Cexp_pair job jobs) =
     let boxes = Cexp_snd (Cexp_snd job) in
     Cexp_add
       (candle_cv_fs_poly_source_checksum_lazy
         (candle_cv_q_center_environment_list boxes)
         (candle_cv_q_fixed_list_round_upper (candle_cv_q_radius_list boxes))
         source_program)
       (candle_cv_fs_poly_jobs_checksum_lazy source_program jobs))`;;

let candle_cv_fs_poly_jobs_checksum_lazy_compute = prove
 (`!source_program jobs.
     candle_cv_fs_poly_jobs_checksum_lazy source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (let boxes = Cexp_snd (Cexp_snd (Cexp_fst jobs)) in
        Cexp_add
          (candle_cv_fs_poly_source_checksum_lazy
            (candle_cv_q_center_environment_list boxes)
            (candle_cv_q_fixed_list_round_upper
              (candle_cv_q_radius_list boxes)) source_program)
          (candle_cv_fs_poly_jobs_checksum_lazy
            source_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_jobs_checksum_lazy_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fs_poly_jobs_exact_def = define
 `(candle_cv_fs_poly_jobs_exact source_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fs_poly_jobs_exact source_program (Cexp_pair job jobs) =
     let boxes = Cexp_snd (Cexp_snd job) in
     Cexp_if
       (candle_cv_fs_poly_source_exact
         (candle_cv_q_center_environment_list boxes)
         (candle_cv_q_fixed_list_round_upper (candle_cv_q_radius_list boxes))
         source_program)
       (candle_cv_fs_poly_jobs_exact source_program jobs)
       (Cexp_num 0))`;;

let candle_cv_fs_poly_jobs_exact_compute = prove
 (`!source_program jobs.
     candle_cv_fs_poly_jobs_exact source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (let boxes = Cexp_snd (Cexp_snd (Cexp_fst jobs)) in
        Cexp_if
          (candle_cv_fs_poly_source_exact
            (candle_cv_q_center_environment_list boxes)
            (candle_cv_q_fixed_list_round_upper
              (candle_cv_q_radius_list boxes)) source_program)
          (candle_cv_fs_poly_jobs_exact source_program (Cexp_snd jobs))
          (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_jobs_exact_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fs_poly_raw_checksum_current_def = new_definition
 `candle_cv_fs_poly_raw_checksum_current source_program encoded_jobs =
    Cexp_if
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_fs_poly_jobs_checksum_current source_program encoded_jobs)
      (Cexp_num 0)`;;

let candle_cv_fs_poly_raw_checksum_lazy_def = new_definition
 `candle_cv_fs_poly_raw_checksum_lazy source_program encoded_jobs =
    Cexp_if
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_fs_poly_jobs_checksum_lazy source_program encoded_jobs)
      (Cexp_num 0)`;;

let candle_cv_fs_poly_raw_exact_def = new_definition
 `candle_cv_fs_poly_raw_exact source_program encoded_jobs =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_fs_poly_jobs_exact source_program encoded_jobs)`;;

let candle_case10173_lazy_completion_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fso_variable_raw_compute_eqs
      (union candle_cv_fs_lazy_completion_compute_eqs
        (map SPEC_ALL
          [candle_cv_fs_poly_result_checksum_def;
           candle_cv_fs_poly_source_checksum_current_compute;
           candle_cv_fs_poly_source_checksum_lazy_compute;
           candle_cv_fs_poly_source_exact_compute;
           candle_cv_fs_poly_jobs_checksum_current_compute;
           candle_cv_fs_poly_jobs_checksum_lazy_compute;
           candle_cv_fs_poly_jobs_exact_compute;
           candle_cv_fs_poly_raw_checksum_current_def;
           candle_cv_fs_poly_raw_checksum_lazy_def;
           candle_cv_fs_poly_raw_exact_def])));;

let rec candle_case10173_lazy_completion_cval_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 lazy-completion prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_lazy_completion_cval_take (count - 1) tail);;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-lazy-completion-prefix128" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let encoded_jobs =
    candle_case10173_lazy_completion_cval_take 128
      captured.case10173_complete_encoded_jobs in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  let call name = list_mk_comb (name,[source_program;encoded_jobs]) in
  let run label name =
    let current_call = call name in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
    let theorem =
      candle_q_dim_analytic_jet_compute
        candle_case10173_lazy_completion_compute_eqs current_call in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-end");
    if hyp theorem <> [] || not (aconv (lhand (concl theorem)) current_call)
    then failwith ("case10173 lazy-completion: " ^ label ^ " malformed");
    theorem in
  let current_1 =
    run "lazy-completion-current-1" `candle_cv_fs_poly_raw_checksum_current` in
  let candidate_1 =
    run "lazy-completion-candidate-1" `candle_cv_fs_poly_raw_checksum_lazy` in
  let exact = run "lazy-completion-exact-results" `candle_cv_fs_poly_raw_exact` in
  let candidate_2 =
    run "lazy-completion-candidate-2" `candle_cv_fs_poly_raw_checksum_lazy` in
  let current_2 =
    run "lazy-completion-current-2" `candle_cv_fs_poly_raw_checksum_current` in
  let baseline = rand (concl current_1) in
  let axioms_after = axioms () in
  if not (aconv (rand (concl candidate_1)) baseline) ||
     not (aconv (rand (concl candidate_2)) baseline) ||
     not (aconv (rand (concl current_2)) baseline) ||
     not (aconv (rand (concl exact)) `Cexp_num 1`) ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 lazy-completion: final mismatch";
  print_endline
    "CANDLE_CV_CASE10173_LAZY_COMPLETION_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 blocks_per_cell=22 current=2 candidate=2 exact_results=2816 assumptions=0 axiom_growth=0";;

end;;
