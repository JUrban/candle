(* ========================================================================== *)
(* Fixed-scale addition tail after the final nonlinear instruction.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A tagged stack retains fixed-scale Taylor      *)
(* results across polynomial blocks and, once no later nonlinear instruction  *)
(* remains, negation and addition.  Multiplication, square, and every          *)
(* nonlinear instruction retain the established rational path.  This file is  *)
(* a numerical/acceptance discriminator; it must not authorize a theorem      *)
(* until the corresponding conversion and mixed-stack invariants are proved.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute = struct

open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;

(* Outwardly round an established rational result into the fixed-scale       *)
(* representation only when an outer algebraic operation consumes it.        *)

let candle_cv_fsa_interval_matrix_of_q_def = define
 `(candle_cv_fsa_interval_matrix_of_q (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fsa_interval_matrix_of_q (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_interval_list_of_q h)
       (candle_cv_fsa_interval_matrix_of_q t))`;;

let candle_cv_fsa_interval_matrix_of_q_compute = prove
 (`!items.
     candle_cv_fsa_interval_matrix_of_q items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair
         (candle_cv_fs_interval_list_of_q (Cexp_fst items))
         (candle_cv_fsa_interval_matrix_of_q (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsa_interval_matrix_of_q_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsa_result_of_q_def = new_definition
 `candle_cv_fsa_result_of_q result =
    candle_cv_fs_result_make
      (candle_cv_q_dim_taylor_model_result_domain result)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_of_q
          (candle_cv_q_dim_first_jet_f
            (candle_cv_q_dim_taylor_model_result_center result)))
        (candle_cv_fs_interval_list_of_q
          (candle_cv_q_dim_first_jet_gradient
            (candle_cv_q_dim_taylor_model_result_center result))))
      (candle_cv_fs_interval_of_q
        (candle_cv_q_dim_taylor_model_result_value_bound result))
      (candle_cv_fs_interval_list_of_q
        (candle_cv_q_dim_taylor_model_result_gradient_bounds result))
      (candle_cv_fsa_interval_matrix_of_q
        (candle_cv_q_dim_taylor_model_result_hessian result))`;;

(* A mixed item is [tag,result], where tag 1 denotes a fixed-scale result and *)
(* tag 0 denotes an established rational Taylor-model result.                 *)

let candle_cv_fsa_item_fixed_def = new_definition
 `candle_cv_fsa_item_fixed result =
    Cexp_pair (Cexp_num 1) result`;;

let candle_cv_fsa_item_q_def = new_definition
 `candle_cv_fsa_item_q result =
    Cexp_pair (Cexp_num 0) result`;;

let candle_cv_fsa_item_is_fixed_def = new_definition
 `candle_cv_fsa_item_is_fixed item =
    Cexp_eq (Cexp_fst item) (Cexp_num 1)`;;

let candle_cv_fsa_item_payload_def = new_definition
 `candle_cv_fsa_item_payload item = Cexp_snd item`;;

let candle_cv_fsa_item_to_q_def = new_definition
 `candle_cv_fsa_item_to_q item =
    Cexp_if (candle_cv_fsa_item_is_fixed item)
      (candle_cv_fs_result_to_q (candle_cv_fsa_item_payload item))
      (candle_cv_fsa_item_payload item)`;;

let candle_cv_fsa_item_to_fixed_def = new_definition
 `candle_cv_fsa_item_to_fixed item =
    Cexp_if (candle_cv_fsa_item_is_fixed item)
      (candle_cv_fsa_item_payload item)
      (candle_cv_fsa_result_of_q (candle_cv_fsa_item_payload item))`;;

let candle_cv_fsa_item_default_def = new_definition
 `candle_cv_fsa_item_default center_boxes boxes =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_default center_boxes boxes)`;;

let candle_cv_fsa_item_head_def = new_definition
 `candle_cv_fsa_item_head center_boxes boxes stack =
    Cexp_if (Cexp_ispair stack) (Cexp_fst stack)
      (candle_cv_fsa_item_default center_boxes boxes)`;;

let candle_cv_fsa_item_tail_def = new_definition
 `candle_cv_fsa_item_tail stack =
    Cexp_if (Cexp_ispair stack) (Cexp_snd stack) (Cexp_num 0)`;;

let candle_cv_fsa_item_neg_def = new_definition
 `candle_cv_fsa_item_neg use_fixed radii item =
    Cexp_if use_fixed
      (candle_cv_fsa_item_fixed
        (candle_cv_fs_result_neg (candle_cv_fs_list_of_q radii)
          (candle_cv_fsa_item_to_fixed item)))
      (candle_cv_fsa_item_q
        (candle_cv_q_dim_taylor_model_result_neg radii
          (candle_cv_fsa_item_to_q item)))`;;

let candle_cv_fsa_item_add_def = new_definition
 `candle_cv_fsa_item_add use_fixed radii left right =
    Cexp_if use_fixed
      (candle_cv_fsa_item_fixed
        (candle_cv_fs_result_add (candle_cv_fs_list_of_q radii)
          (candle_cv_fsa_item_to_fixed left)
          (candle_cv_fsa_item_to_fixed right)))
      (candle_cv_fsa_item_q
        (candle_cv_q_dim_taylor_model_result_add radii
          (candle_cv_fsa_item_to_q left)
          (candle_cv_fsa_item_to_q right)))`;;

let candle_cv_fsa_item_mul_def = new_definition
 `candle_cv_fsa_item_mul radii left right =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_mul radii
        (candle_cv_fsa_item_to_q left)
        (candle_cv_fsa_item_to_q right))`;;

let candle_cv_fsa_item_square_def = new_definition
 `candle_cv_fsa_item_square radii item =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_square radii
        (candle_cv_fsa_item_to_q item))`;;

let candle_cv_fsa_item_sqrt_def = new_definition
 `candle_cv_fsa_item_sqrt radii center_certificate box_certificate item =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_sqrt radii
        center_certificate box_certificate
        (candle_cv_fsa_item_to_q item))`;;

let candle_cv_fsa_item_inv_def = new_definition
 `candle_cv_fsa_item_inv radii item =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_inv radii
        (candle_cv_fsa_item_to_q item))`;;

let candle_cv_fsa_item_atn_def = new_definition
 `candle_cv_fsa_item_atn radii item =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_atn radii
        (candle_cv_fsa_item_to_q item))`;;

let candle_cv_fsa_item_pi_half_def = new_definition
 `candle_cv_fsa_item_pi_half radii center_boxes boxes =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_pi_half
        radii center_boxes boxes)`;;

let candle_cv_fsa_instruction_is_nonlinear_def = new_definition
 `candle_cv_fsa_instruction_is_nonlinear instruction =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_eq (Cexp_fst instruction) (Cexp_num 1))
      (Cexp_if (Cexp_eq instruction (Cexp_num 6)) (Cexp_num 1)
        (Cexp_if (Cexp_eq instruction (Cexp_num 7)) (Cexp_num 1)
          (Cexp_eq instruction (Cexp_num 8))))`;;

let candle_cv_fsa_program_has_nonlinear_def = define
 `(candle_cv_fsa_program_has_nonlinear (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fsa_program_has_nonlinear (Cexp_pair h t) =
     Cexp_if (candle_cv_fsa_instruction_is_nonlinear h) (Cexp_num 1)
       (candle_cv_fsa_program_has_nonlinear t))`;;

let candle_cv_fsa_program_has_nonlinear_compute = prove
 (`!program.
     candle_cv_fsa_program_has_nonlinear program =
     Cexp_if (Cexp_ispair program)
       (Cexp_if
         (candle_cv_fsa_instruction_is_nonlinear (Cexp_fst program))
         (Cexp_num 1)
         (candle_cv_fsa_program_has_nonlinear (Cexp_snd program)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsa_program_has_nonlinear_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsa_program_step_def = new_definition
 `candle_cv_fsa_program_step
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
                  (candle_cv_fsa_item_mul radii
                    (candle_cv_fsa_item_head center_boxes boxes
                      (candle_cv_fsa_item_tail stack))
                    (candle_cv_fsa_item_head center_boxes boxes stack))
                  (candle_cv_fsa_item_tail
                    (candle_cv_fsa_item_tail stack)))
                (Cexp_if (Cexp_eq center_instruction (Cexp_num 5))
                  (Cexp_pair
                    (candle_cv_fsa_item_square radii
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

let candle_cv_fsa_program_run_def = define
 `(candle_cv_fsa_program_run
     center_boxes boxes radii (Cexp_num n) box_program stack = stack) /\
  (candle_cv_fsa_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_fsa_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_fsa_program_run center_boxes boxes radii ct bt
       (candle_cv_fsa_program_step
         center_boxes boxes radii
         (Cexp_if (candle_cv_fsa_program_has_nonlinear ct)
           (Cexp_num 0) (Cexp_num 1))
         ch bh stack))`;;

let candle_cv_fsa_program_run_compute = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_cv_fsa_program_run
       center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_fsa_program_run center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_fsa_program_step center_boxes boxes radii
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
  REWRITE_TAC[candle_cv_fsa_program_run_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsa_program_def = new_definition
 `candle_cv_fsa_program center_program box_program boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fsa_program_run
          (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program (Cexp_num 0)))`;;

let candle_cv_fsa_certified_check_def = new_definition
 `candle_cv_fsa_certified_check center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fsa_program center_program box_program boxes)`;;

let candle_cv_fsa_compute_eqs =
  union candle_cv_fs_q_dim_taylor_model_compute_eqs
    (map SPEC_ALL
      [candle_cv_fsa_interval_matrix_of_q_compute;
       candle_cv_fsa_result_of_q_def;
       candle_cv_fsa_item_fixed_def;
       candle_cv_fsa_item_q_def;
       candle_cv_fsa_item_is_fixed_def;
       candle_cv_fsa_item_payload_def;
       candle_cv_fsa_item_to_q_def;
       candle_cv_fsa_item_to_fixed_def;
       candle_cv_fsa_item_default_def;
       candle_cv_fsa_item_head_def;
       candle_cv_fsa_item_tail_def;
       candle_cv_fsa_item_neg_def;
       candle_cv_fsa_item_add_def;
       candle_cv_fsa_item_mul_def;
       candle_cv_fsa_item_square_def;
       candle_cv_fsa_item_sqrt_def;
       candle_cv_fsa_item_inv_def;
       candle_cv_fsa_item_atn_def;
       candle_cv_fsa_item_pi_half_def;
       candle_cv_fsa_instruction_is_nonlinear_def;
       candle_cv_fsa_program_has_nonlinear_compute;
       candle_cv_fsa_program_step_def;
       candle_cv_fsa_program_run_compute;
       candle_cv_fsa_program_def;
       candle_cv_fsa_certified_check_def]);;

end;;
