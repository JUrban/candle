(* ========================================================================== *)
(* Fixed-outer evaluator with proved lazy completion inside polynomial blocks. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Every non-polynomial instruction delegates to  *)
(* the established fixed-outer evaluator.  A polynomial pair uses the lazy    *)
(* fixed-scale evaluator, whose compiler-produced programs are proved exactly  *)
(* equal to the established fixed-scale result.                               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_lazy_completion_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_lazy = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_fixed_scale_lazy_completion_compute;;

let candle_cv_fsol_program_step_def = new_definition
 `candle_cv_fsol_program_step
      center_boxes boxes radii center_instruction box_instruction stack =
    Cexp_if
      (candle_cv_fs_q_dim_taylor_model_is_poly_pair
        center_instruction box_instruction)
      (Cexp_pair
        (candle_cv_fsa_item_fixed
          (candle_cv_fs_poly_program_lazy center_boxes radii
            (Cexp_snd center_instruction)))
        stack)
      (candle_cv_fso_program_step center_boxes boxes radii
        center_instruction box_instruction stack)`;;

let candle_cv_fsol_program_run_def = define
 `(candle_cv_fsol_program_run
     center_boxes boxes radii (Cexp_num n) box_program stack = stack) /\
  (candle_cv_fsol_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_fsol_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_fsol_program_run center_boxes boxes radii ct bt
       (candle_cv_fsol_program_step
         center_boxes boxes radii ch bh stack))`;;

let candle_cv_fsol_program_run_compute = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_cv_fsol_program_run
       center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_fsol_program_run center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_fsol_program_step center_boxes boxes radii
             (Cexp_fst center_program) (Cexp_fst box_program) stack))
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsol_program_run_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsol_program_def = new_definition
 `candle_cv_fsol_program center_program box_program boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fsol_program_run
          (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program (Cexp_num 0)))`;;

let candle_cv_fsol_certified_check_def = new_definition
 `candle_cv_fsol_certified_check center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fsol_program center_program box_program boxes)`;;

let candle_cv_fsol_compute_eqs =
  map (REWRITE_RULE[LET_END_DEF])
    (union candle_cv_fso_compute_eqs
      (union candle_cv_fs_lazy_completion_compute_eqs
        (map SPEC_ALL
          [candle_cv_fsol_program_step_def;
           candle_cv_fsol_program_run_compute;
           candle_cv_fsol_program_def;
           candle_cv_fsol_certified_check_def])));;

end;;
