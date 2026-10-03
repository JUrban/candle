(* ========================================================================== *)
(* Numerical discriminator for a wider fixed-scale algebraic suffix.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The established checker keeps multiplication  *)
(* and square in the rational representation.  This experiment instead keeps *)
(* those operations fixed-scale when no nonlinear instruction remains.  It   *)
(* compares acceptance and execution time on 128 genuine case-16594 cells.   *)
(* No soundness or source-theorem claim is made for the experimental result.  *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_fixed_mul_square_discriminator = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let candle_cv_fsm_item_mul_def = new_definition
 `candle_cv_fsm_item_mul use_fixed radii left right =
    Cexp_if use_fixed
      (candle_cv_fsa_item_fixed
        (candle_cv_fs_result_mul (candle_cv_fs_list_of_q radii)
          (candle_cv_fsa_item_to_fixed left)
          (candle_cv_fsa_item_to_fixed right)))
      (candle_cv_fsa_item_q
        (candle_cv_q_dim_taylor_model_result_mul radii
          (candle_cv_fsa_item_to_q left)
          (candle_cv_fsa_item_to_q right)))`;;

let candle_cv_fsm_item_square_def = new_definition
 `candle_cv_fsm_item_square use_fixed radii item =
    Cexp_if use_fixed
      (candle_cv_fsa_item_fixed
        (candle_cv_fs_result_square (candle_cv_fs_list_of_q radii)
          (candle_cv_fsa_item_to_fixed item)))
      (candle_cv_fsa_item_q
        (candle_cv_q_dim_taylor_model_result_square radii
          (candle_cv_fsa_item_to_q item)))`;;

let candle_cv_fsm_program_step_def = new_definition
 `candle_cv_fsm_program_step
      center_boxes boxes radii use_fixed
      center_instruction box_instruction stack =
    Cexp_if (Cexp_ispair center_instruction)
      (Cexp_if (Cexp_ispair box_instruction)
        (Cexp_if (Cexp_eq (Cexp_fst center_instruction) (Cexp_num 0))
          (Cexp_if (Cexp_eq (Cexp_fst box_instruction) (Cexp_num 0))
            (Cexp_pair
              (candle_cv_fsa_item_fixed
                (candle_cv_fs_poly_program center_boxes radii
                  (Cexp_snd center_instruction)))
              stack)
            (Cexp_pair
              (candle_cv_fsa_item_default center_boxes boxes) stack))
          (Cexp_if (Cexp_eq (Cexp_fst center_instruction) (Cexp_num 1))
            (Cexp_if (Cexp_eq (Cexp_fst box_instruction) (Cexp_num 1))
              (Cexp_pair
                (candle_cv_fsa_item_sqrt radii
                  (Cexp_snd center_instruction)
                  (Cexp_snd box_instruction)
                  (candle_cv_fsa_item_head center_boxes boxes stack))
                (candle_cv_fsa_item_tail stack))
              (Cexp_pair
                (candle_cv_fsa_item_default center_boxes boxes) stack))
            (Cexp_pair
              (candle_cv_fsa_item_default center_boxes boxes) stack)))
        (Cexp_pair
          (candle_cv_fsa_item_default center_boxes boxes) stack))
      (Cexp_if (Cexp_ispair box_instruction)
        (Cexp_pair
          (candle_cv_fsa_item_default center_boxes boxes) stack)
        (Cexp_if (Cexp_eq center_instruction box_instruction)
          (Cexp_if (Cexp_eq center_instruction (Cexp_num 2))
            (Cexp_pair
              (candle_cv_fsa_item_neg use_fixed radii
                (candle_cv_fsa_item_head center_boxes boxes stack))
              (candle_cv_fsa_item_tail stack))
            (Cexp_if (Cexp_eq center_instruction (Cexp_num 3))
              (Cexp_pair
                (candle_cv_fsa_item_add use_fixed radii
                  (candle_cv_fsa_item_head center_boxes boxes
                    (candle_cv_fsa_item_tail stack))
                  (candle_cv_fsa_item_head center_boxes boxes stack))
                (candle_cv_fsa_item_tail
                  (candle_cv_fsa_item_tail stack)))
              (Cexp_if (Cexp_eq center_instruction (Cexp_num 4))
                (Cexp_pair
                  (candle_cv_fsm_item_mul use_fixed radii
                    (candle_cv_fsa_item_head center_boxes boxes
                      (candle_cv_fsa_item_tail stack))
                    (candle_cv_fsa_item_head center_boxes boxes stack))
                  (candle_cv_fsa_item_tail
                    (candle_cv_fsa_item_tail stack)))
                (Cexp_if (Cexp_eq center_instruction (Cexp_num 5))
                  (Cexp_pair
                    (candle_cv_fsm_item_square use_fixed radii
                      (candle_cv_fsa_item_head center_boxes boxes stack))
                    (candle_cv_fsa_item_tail stack))
                  (Cexp_if (Cexp_eq center_instruction (Cexp_num 6))
                    (Cexp_pair
                      (candle_cv_fsa_item_inv radii
                        (candle_cv_fsa_item_head center_boxes boxes stack))
                      (candle_cv_fsa_item_tail stack))
                    (Cexp_if (Cexp_eq center_instruction (Cexp_num 7))
                      (Cexp_pair
                        (candle_cv_fsa_item_atn radii
                          (candle_cv_fsa_item_head center_boxes boxes stack))
                        (candle_cv_fsa_item_tail stack))
                      (Cexp_if (Cexp_eq center_instruction (Cexp_num 8))
                        (Cexp_pair
                          (candle_cv_fsa_item_pi_half
                            radii center_boxes boxes) stack)
                        (Cexp_pair
                          (candle_cv_fsa_item_default center_boxes boxes)
                          stack))))))))
          (Cexp_pair
            (candle_cv_fsa_item_default center_boxes boxes) stack)))`;;

let candle_cv_fsm_program_run_def = define
 `(candle_cv_fsm_program_run
     center_boxes boxes radii (Cexp_num n) box_program stack = stack) /\
  (candle_cv_fsm_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_fsm_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_fsm_program_run center_boxes boxes radii ct bt
       (candle_cv_fsm_program_step
         center_boxes boxes radii
         (Cexp_if (candle_cv_fsa_program_has_nonlinear ct)
           (Cexp_num 0) (Cexp_num 1))
         ch bh stack))`;;

let candle_cv_fsm_program_run_compute = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_cv_fsm_program_run
       center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_fsm_program_run center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_fsm_program_step center_boxes boxes radii
             (Cexp_if
               (candle_cv_fsa_program_has_nonlinear
                 (Cexp_snd center_program))
               (Cexp_num 0) (Cexp_num 1))
             (Cexp_fst center_program) (Cexp_fst box_program) stack))
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsm_program_run_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsm_program_def = new_definition
 `candle_cv_fsm_program center_program box_program boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fsm_program_run
          (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program (Cexp_num 0)))`;;

let candle_cv_fsm_certified_check_def = new_definition
 `candle_cv_fsm_certified_check center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fsm_program center_program box_program boxes)`;;

let candle_cv_fsm_variable_jobs_check_def = define
 `(candle_cv_fsm_variable_jobs_check source_program (Cexp_num n) =
     Cexp_num 1) /\
  (candle_cv_fsm_variable_jobs_check source_program
      (Cexp_pair job jobs) =
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
               (candle_cv_fsm_certified_check
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job))))
             (candle_cv_fsm_variable_jobs_check source_program jobs)
             (Cexp_num 0))
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fsm_variable_jobs_check_compute = prove
 (`!source_program jobs.
     candle_cv_fsm_variable_jobs_check source_program jobs =
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
                 (candle_cv_fsm_certified_check
                   (Cexp_snd center_patched) (Cexp_snd box_patched)
                   (Cexp_snd (Cexp_snd (Cexp_fst jobs)))))
               (candle_cv_fsm_variable_jobs_check
                 source_program (Cexp_snd jobs))
               (Cexp_num 0))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsm_variable_jobs_check_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsm_variable_raw_jobs_check_def = new_definition
 `candle_cv_fsm_variable_raw_jobs_check source_program encoded_jobs =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_fsm_variable_jobs_check source_program encoded_jobs)`;;

let candle_cv_fsm_compute_eqs =
  map (REWRITE_RULE[LET_END_DEF])
    (union candle_cv_fso_variable_raw_compute_eqs
      [SPEC_ALL candle_cv_fsm_item_mul_def;
       SPEC_ALL candle_cv_fsm_item_square_def;
       SPEC_ALL candle_cv_fsm_program_step_def;
       SPEC_ALL candle_cv_fsm_program_run_compute;
       SPEC_ALL candle_cv_fsm_program_def;
       SPEC_ALL candle_cv_fsm_certified_check_def;
       SPEC_ALL candle_cv_fsm_variable_jobs_check_compute;
       SPEC_ALL candle_cv_fsm_variable_raw_jobs_check_def]);;

let rec candle_disjunctive_case16594_fixed_mul_square_take count = function
  | _ when count = 0 -> []
  | [] -> failwith "case16594 fixed mul/square: short plan"
  | head :: tail ->
      head ::
      candle_disjunctive_case16594_fixed_mul_square_take (count - 1) tail;;

let candle_disjunctive_case16594_fixed_mul_square_marker phase =
  candle_q_dim_analytic_jet_profile_event phase;;

let candle_disjunctive_case16594_fixed_mul_square_compute
    label equations operator prepared encoded_jobs =
  let call =
    list_mk_comb
      (operator,[prepared.program_representation_term;encoded_jobs]) in
  candle_disjunctive_case16594_fixed_mul_square_marker
    (label ^ "-kernel-compute-begin");
  let theorem = candle_q_dim_analytic_jet_compute equations call in
  candle_disjunctive_case16594_fixed_mul_square_marker
    (label ^ "-kernel-compute-end");
  let result = rand (concl theorem) in
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) call) ||
     (not (aconv result `Cexp_num 0`) &&
      not (aconv result `Cexp_num 1`)) then
    failwith "case16594 fixed mul/square: malformed verdict";
  let accepted = aconv result `Cexp_num 1` in
  print_endline
    ("CANDLE_CV_CASE16594_FIXED_MUL_SQUARE_RESULT" ^
     " checker=" ^ label ^
     " cells=128 accepted=" ^ (if accepted then "1" else "0"));
  accepted;;

let candle_disjunctive_case16594_fixed_mul_square_run () =
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  candle_disjunctive_case16594_fixed_mul_square_marker "encoding-begin";
  let cells =
    candle_disjunctive_case16594_fixed_mul_square_take 128
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_disjunctive_case16594_fixed_mul_square_marker "encoding-end";
  let established =
    candle_disjunctive_case16594_fixed_mul_square_compute
      "established"
      candle_cv_fso_variable_raw_compute_eqs
      `candle_cv_fso_variable_raw_jobs_check` prepared encoded_jobs in
  if not established then
    failwith "case16594 fixed mul/square: established checker rejected";
  let experimental =
    candle_disjunctive_case16594_fixed_mul_square_compute
      "fixed-mul-square"
      candle_cv_fsm_compute_eqs
      `candle_cv_fsm_variable_raw_jobs_check` prepared encoded_jobs in
  established,experimental;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-fixed-mul-square" ^
         " phase=" ^ event));;

let candle_disjunctive_case16594_fixed_mul_square_established,
    candle_disjunctive_case16594_fixed_mul_square_experimental =
  candle_disjunctive_case16594_fixed_mul_square_run ();;

let _ =
  print_endline
    ("CANDLE_CV_CASE16594_FIXED_MUL_SQUARE_OK DEVELOPMENT_NON_RELEASE" ^
     " cells=128 established=1 experimental=" ^
     (if candle_disjunctive_case16594_fixed_mul_square_experimental
      then "1" else "0"));;

end;;
