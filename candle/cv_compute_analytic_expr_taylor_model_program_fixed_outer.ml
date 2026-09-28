(* ========================================================================== *)
(* Fixed-scale outer-algebra discriminator for the tagged Taylor evaluator.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Unlike the proved production evaluator, this  *)
(* prototype retains fixed-scale results across every algebraic operation,   *)
(* including multiplication and square, and converts back to rationals only  *)
(* at nonlinear instructions and the final interface.  It has no theorem     *)
(* authority until a general analytic multiplication invariant is proved.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_batch.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer = struct

open Candle_cv_analytic_expr_certificate_patch_compute;;
open Candle_cv_analytic_expr_certificate_patch_exact;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;
open Candle_cv_analytic_expr_stable_batch;;

let candle_cv_fso_item_mul_def = new_definition
 `candle_cv_fso_item_mul radii left right =
    candle_cv_fsa_item_fixed
      (candle_cv_fs_result_mul (candle_cv_fs_list_of_q radii)
        (candle_cv_fsa_item_to_fixed left)
        (candle_cv_fsa_item_to_fixed right))`;;

let candle_cv_fso_item_square_def = new_definition
 `candle_cv_fso_item_square radii item =
    candle_cv_fsa_item_fixed
      (candle_cv_fs_result_square (candle_cv_fs_list_of_q radii)
        (candle_cv_fsa_item_to_fixed item))`;;

(* This is the established step relation with fixed mode selected for neg/add *)
(* and fixed-scale implementations selected for mul/square.  Invalid opcode  *)
(* and program-shape cases retain the same fail-closed default result.         *)

let candle_cv_fso_program_step_def = new_definition
 `candle_cv_fso_program_step
      center_boxes boxes radii center_instruction box_instruction stack =
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
              (candle_cv_fsa_item_neg (Cexp_num 1) radii
                (candle_cv_fsa_item_head center_boxes boxes stack))
              (candle_cv_fsa_item_tail stack))
            (Cexp_if (Cexp_eq center_instruction (Cexp_num 3))
              (Cexp_pair
                (candle_cv_fsa_item_add (Cexp_num 1) radii
                  (candle_cv_fsa_item_head center_boxes boxes
                    (candle_cv_fsa_item_tail stack))
                  (candle_cv_fsa_item_head center_boxes boxes stack))
                (candle_cv_fsa_item_tail
                  (candle_cv_fsa_item_tail stack)))
              (Cexp_if (Cexp_eq center_instruction (Cexp_num 4))
                (Cexp_pair
                  (candle_cv_fso_item_mul radii
                    (candle_cv_fsa_item_head center_boxes boxes
                      (candle_cv_fsa_item_tail stack))
                    (candle_cv_fsa_item_head center_boxes boxes stack))
                  (candle_cv_fsa_item_tail
                    (candle_cv_fsa_item_tail stack)))
                (Cexp_if (Cexp_eq center_instruction (Cexp_num 5))
                  (Cexp_pair
                    (candle_cv_fso_item_square radii
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

let candle_cv_fso_program_run_def = define
 `(candle_cv_fso_program_run
     center_boxes boxes radii (Cexp_num n) box_program stack = stack) /\
  (candle_cv_fso_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_fso_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_fso_program_run center_boxes boxes radii ct bt
       (candle_cv_fso_program_step
         center_boxes boxes radii ch bh stack))`;;

let candle_cv_fso_program_run_compute = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_cv_fso_program_run
       center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_fso_program_run center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_fso_program_step center_boxes boxes radii
             (Cexp_fst center_program) (Cexp_fst box_program) stack))
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fso_program_run_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fso_program_def = new_definition
 `candle_cv_fso_program center_program box_program boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fso_program_run
          (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program (Cexp_num 0)))`;;

let candle_cv_fso_certified_check_def = new_definition
 `candle_cv_fso_certified_check center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fso_program center_program box_program boxes)`;;

let candle_cv_fso_stable_jobs_check_def = define
 `(candle_cv_fso_stable_jobs_check
      source_program box_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fso_stable_jobs_check
      source_program box_program (Cexp_pair job jobs) =
     Cexp_if
       (candle_cv_analytic_program_sqrt_data_exact
         (Cexp_fst job) source_program)
       (let center_patched =
          candle_cv_analytic_program_patch_sqrt
            (Cexp_fst job) source_program in
        Cexp_if
          (Cexp_fst
            (candle_cv_fso_certified_check
              (Cexp_snd center_patched) box_program (Cexp_snd job)))
          (candle_cv_fso_stable_jobs_check
            source_program box_program jobs)
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fso_stable_jobs_check_compute = prove
 (`!source_program box_program jobs.
     candle_cv_fso_stable_jobs_check source_program box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst (Cexp_fst jobs)) source_program)
         (let center_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_fst jobs)) source_program in
          Cexp_if
            (Cexp_fst
              (candle_cv_fso_certified_check
                (Cexp_snd center_patched) box_program
                (Cexp_snd (Cexp_fst jobs))))
            (candle_cv_fso_stable_jobs_check
              source_program box_program (Cexp_snd jobs))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fso_stable_jobs_check_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fso_stable_batch_check_def = new_definition
 `candle_cv_fso_stable_batch_check source_program box_intervals jobs =
    Cexp_if
      (candle_cv_analytic_program_sqrt_data_exact
        box_intervals source_program)
      (let box_patched =
         candle_cv_analytic_program_patch_sqrt
           box_intervals source_program in
       candle_cv_fso_stable_jobs_check
         source_program (Cexp_snd box_patched) jobs)
      (Cexp_num 0)`;;

let candle_cv_fso_compute_eqs =
  map (REWRITE_RULE[LET_END_DEF])
    (union candle_cv_fsa_stable_batch_compute_eqs
      [SPEC_ALL candle_cv_fso_item_mul_def;
       SPEC_ALL candle_cv_fso_item_square_def;
       SPEC_ALL candle_cv_fso_program_step_def;
       SPEC_ALL candle_cv_fso_program_run_compute;
       SPEC_ALL candle_cv_fso_program_def;
       SPEC_ALL candle_cv_fso_certified_check_def;
       SPEC_ALL candle_cv_fso_stable_jobs_check_compute;
       SPEC_ALL candle_cv_fso_stable_batch_check_def]);;

end;;

