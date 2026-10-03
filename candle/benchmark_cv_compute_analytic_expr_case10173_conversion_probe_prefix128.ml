(* ========================================================================== *)
(* Fixed/rational transition-cost probe for genuine case-10173 cells.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The conversion mode       *)
(* deliberately repeats the representation conversion already performed by  *)
(* each authentic fixed-outer step.  The matched control follows the same    *)
(* instruction/stack branches but checks only the input item constructor.     *)
(* Their timing difference is a bounded discriminator, never theorem evidence. *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_conversion_probe_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_cv_fso_transition_probe_to_q_def = new_definition
 `candle_cv_fso_transition_probe_to_q mode item =
    Cexp_if mode
      (Cexp_ispair (candle_cv_fsa_item_to_q item))
      (Cexp_ispair item)`;;

let candle_cv_fso_transition_probe_to_fixed_def = new_definition
 `candle_cv_fso_transition_probe_to_fixed mode item =
    Cexp_if mode
      (Cexp_ispair (candle_cv_fsa_item_to_fixed item))
      (Cexp_ispair item)`;;

let candle_cv_fso_transition_probe_def = new_definition
 `candle_cv_fso_transition_probe
      mode center_boxes boxes center_instruction stack =
    Cexp_if (Cexp_ispair center_instruction)
      (Cexp_if (Cexp_eq (Cexp_fst center_instruction) (Cexp_num 1))
        (candle_cv_fso_transition_probe_to_q mode
          (candle_cv_fsa_item_head center_boxes boxes stack))
        (Cexp_num 1))
      (Cexp_if (Cexp_eq center_instruction (Cexp_num 2))
        (candle_cv_fso_transition_probe_to_fixed mode
          (candle_cv_fsa_item_head center_boxes boxes stack))
        (Cexp_if (Cexp_eq center_instruction (Cexp_num 3))
          (candle_cv_bool_and
            (candle_cv_fso_transition_probe_to_fixed mode
              (candle_cv_fsa_item_head center_boxes boxes
                (candle_cv_fsa_item_tail stack)))
            (candle_cv_fso_transition_probe_to_fixed mode
              (candle_cv_fsa_item_head center_boxes boxes stack)))
          (Cexp_if (Cexp_eq center_instruction (Cexp_num 4))
            (candle_cv_bool_and
              (candle_cv_fso_transition_probe_to_fixed mode
                (candle_cv_fsa_item_head center_boxes boxes
                  (candle_cv_fsa_item_tail stack)))
              (candle_cv_fso_transition_probe_to_fixed mode
                (candle_cv_fsa_item_head center_boxes boxes stack)))
            (Cexp_if (Cexp_eq center_instruction (Cexp_num 5))
              (candle_cv_fso_transition_probe_to_fixed mode
                (candle_cv_fsa_item_head center_boxes boxes stack))
              (Cexp_if (Cexp_eq center_instruction (Cexp_num 6))
                (candle_cv_fso_transition_probe_to_q mode
                  (candle_cv_fsa_item_head center_boxes boxes stack))
                (Cexp_if (Cexp_eq center_instruction (Cexp_num 7))
                  (candle_cv_fso_transition_probe_to_q mode
                    (candle_cv_fsa_item_head center_boxes boxes stack))
                  (Cexp_num 1)))))))`;;

let candle_cv_fso_program_run_transition_probe_def = define
 `(candle_cv_fso_program_run_transition_probe
     mode center_boxes boxes radii (Cexp_num n) box_program stack = stack) /\
  (candle_cv_fso_program_run_transition_probe
     mode center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) stack =
     stack) /\
  (candle_cv_fso_program_run_transition_probe
     mode center_boxes boxes radii (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     Cexp_if
       (candle_cv_fso_transition_probe mode center_boxes boxes ch stack)
       (candle_cv_fso_program_run_transition_probe
         mode center_boxes boxes radii ct bt
         (candle_cv_fso_program_step
           center_boxes boxes radii ch bh stack))
       stack)`;;

let candle_cv_fso_program_run_transition_probe_compute = prove
 (`!mode center_boxes boxes radii center_program box_program stack.
     candle_cv_fso_program_run_transition_probe
       mode center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (Cexp_if
           (candle_cv_fso_transition_probe mode center_boxes boxes
             (Cexp_fst center_program) stack)
           (candle_cv_fso_program_run_transition_probe
             mode center_boxes boxes radii
             (Cexp_snd center_program) (Cexp_snd box_program)
             (candle_cv_fso_program_step center_boxes boxes radii
               (Cexp_fst center_program) (Cexp_fst box_program) stack))
           stack)
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_program_run_transition_probe_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_fso_program_transition_probe_def = new_definition
 `candle_cv_fso_program_transition_probe
      mode center_program box_program boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fso_program_run_transition_probe
          mode (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program (Cexp_num 0)))`;;

let candle_cv_fso_certified_check_transition_probe_def = new_definition
 `candle_cv_fso_certified_check_transition_probe
      mode center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fso_program_transition_probe
        mode center_program box_program boxes)`;;

let candle_cv_fso_variable_jobs_check_transition_probe_def = define
 `(candle_cv_fso_variable_jobs_check_transition_probe
      mode source_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fso_variable_jobs_check_transition_probe
      mode source_program (Cexp_pair job jobs) =
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
               (candle_cv_fso_certified_check_transition_probe mode
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job))))
             (candle_cv_fso_variable_jobs_check_transition_probe
               mode source_program jobs)
             (Cexp_num 0))
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fso_variable_jobs_check_transition_probe_compute = prove
 (`!mode source_program jobs.
     candle_cv_fso_variable_jobs_check_transition_probe
       mode source_program jobs =
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
                 (candle_cv_fso_certified_check_transition_probe mode
                   (Cexp_snd center_patched) (Cexp_snd box_patched)
                   (Cexp_snd (Cexp_snd (Cexp_fst jobs)))))
               (candle_cv_fso_variable_jobs_check_transition_probe
                 mode source_program (Cexp_snd jobs))
               (Cexp_num 0))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_variable_jobs_check_transition_probe_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
     LET_DEF;LET_END_DEF]);;

let candle_cv_fso_variable_raw_jobs_check_transition_probe_def =
  new_definition
   `candle_cv_fso_variable_raw_jobs_check_transition_probe
        mode source_program encoded_jobs =
      candle_cv_bool_and
        (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
          encoded_jobs)
        (candle_cv_fso_variable_jobs_check_transition_probe
          mode source_program encoded_jobs)`;;

let candle_case10173_transition_probe_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fso_variable_raw_compute_eqs
      (map SPEC_ALL
        [candle_cv_fso_transition_probe_to_q_def;
         candle_cv_fso_transition_probe_to_fixed_def;
         candle_cv_fso_transition_probe_def;
         candle_cv_fso_program_run_transition_probe_compute;
         candle_cv_fso_program_transition_probe_def;
         candle_cv_fso_certified_check_transition_probe_def;
         candle_cv_fso_variable_jobs_check_transition_probe_compute;
         candle_cv_fso_variable_raw_jobs_check_transition_probe_def]));;

let rec candle_case10173_transition_probe_cval_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 transition-probe prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_transition_probe_cval_take (count - 1) tail);;

let candle_case10173_transition_probe_validate call theorem =
  hyp theorem = [] && aconv (lhand (concl theorem)) call &&
  aconv (rand (concl theorem)) `Cexp_num 1`;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-transition-probe-prefix128" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let encoded_jobs =
    candle_case10173_transition_probe_cval_take 128
      captured.case10173_complete_encoded_jobs in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  let established_call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [source_program;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "transition-probe-established-compute-begin";
  let established =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_raw_compute_eqs established_call in
  candle_q_dim_analytic_jet_profile_event
    "transition-probe-established-compute-end";
  let probe_call mode =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check_transition_probe`,
       [mode;source_program;encoded_jobs]) in
  let run_probe label mode =
    let call = probe_call mode in
    candle_q_dim_analytic_jet_profile_event
      (label ^ "-compute-begin");
    let theorem =
      candle_q_dim_analytic_jet_compute
        candle_case10173_transition_probe_compute_eqs call in
    candle_q_dim_analytic_jet_profile_event
      (label ^ "-compute-end");
    if not (candle_case10173_transition_probe_validate call theorem) then
      failwith ("case10173 transition probe: " ^ label ^ " failed");
    theorem in
  let control_1 = run_probe "transition-probe-control-1" `Cexp_num 0` in
  let conversion_1 =
    run_probe "transition-probe-conversion-1" `Cexp_num 1` in
  let conversion_2 =
    run_probe "transition-probe-conversion-2" `Cexp_num 1` in
  let control_2 = run_probe "transition-probe-control-2" `Cexp_num 0` in
  let axioms_after = axioms () in
  if not
       (candle_case10173_transition_probe_validate
         established_call established) ||
     not (aconv (rand (concl control_1)) (rand (concl conversion_1))) ||
     not (aconv (rand (concl conversion_1)) (rand (concl conversion_2))) ||
     not (aconv (rand (concl conversion_2)) (rand (concl control_2))) ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 transition probe: final mismatch";
  print_endline
    "CANDLE_CV_CASE10173_TRANSITION_PROBE_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 controls=2 conversions=2 accepted=1 assumptions=0 axiom_growth=0";;

end;;
