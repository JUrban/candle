(* ========================================================================== *)
(* Centered Taylor-model execution for reflected analytic expressions.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The earlier reflected analytic interpreter    *)
(* propagated a complete interval jet through the whole box.  That loses     *)
(* substantially more dependency information than Flyspeck's legacy Taylor  *)
(* arithmetic.  This executable prototype instead carries:                   *)
(*                                                                            *)
(*   - a value and gradient evaluated at the box center; and                 *)
(*   - a Hessian enclosure over the whole box.                               *)
(*                                                                            *)
(* Before a composite instruction is evaluated, whole-box value and gradient *)
(* bounds for each child are reconstructed from that centered Taylor model.  *)
(* This mirrors the numerical boundary used by [eval_m_taylor_bound] and      *)
(* [eval_m_taylor_partial_bound], while retaining a single compact postfix    *)
(* source program.  A separate semantic proof is required before this        *)
(* prototype may support a release claim.                                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_split_certificate_check.ml";;

module Candle_cv_analytic_expr_taylor_model_program_compute = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_rational_normalize_extended;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_first_jet_program_compute;;
open Candle_cv_analytic_expr_extended_taylor;;
open Candle_cv_analytic_expr_split_certificate_check;;

(* Extended normalization is important here: authentic action-296 rows need *)
(* more Euclidean steps than the original bounded normalizer supplies.       *)

let candle_cv_q_interval_add_extended_def = new_definition
 `candle_cv_q_interval_add_extended x y =
    Cexp_pair
      (candle_cv_q_add_normalized_extended (Cexp_fst x) (Cexp_fst y))
      (candle_cv_q_add_normalized_extended (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_q_symmetric_interval_def = new_definition
 `candle_cv_q_symmetric_interval radius =
    Cexp_pair (candle_cv_q_neg radius) radius`;;

(* Bound rational growth after each analytic instruction.  This fixed scale *)
(* has twelve decimal digits, comparable to the precision used by the live  *)
(* action-296 legacy pass.  The numerical prototype uses it directly; the   *)
(* proof layer below this interface must establish the two directed-rounding *)
(* inequalities before release use.                                         *)

let candle_cv_q_taylor_model_scale_def = new_definition
 `candle_cv_q_taylor_model_scale = Cexp_num 1000000000000`;;

let candle_cv_q_ceil_div_def = new_definition
 `candle_cv_q_ceil_div numerator denominator =
    Cexp_add (Cexp_div numerator denominator)
      (Cexp_if (Cexp_eq (Cexp_mod numerator denominator) (Cexp_num 0))
        (Cexp_num 0) (Cexp_num 1))`;;

let candle_cv_q_fixed_make_def = new_definition
 `candle_cv_q_fixed_make positive negative =
    Cexp_pair (Cexp_pair positive negative)
      (Cexp_sub candle_cv_q_taylor_model_scale (Cexp_num 1))`;;

let candle_cv_q_fixed_round_lower_def = new_definition
 `candle_cv_q_fixed_round_lower q =
    Cexp_if (Cexp_less (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
      (candle_cv_q_fixed_make (Cexp_num 0)
        (candle_cv_q_ceil_div
          (Cexp_mul
            (Cexp_sub (Cexp_snd (Cexp_fst q)) (Cexp_fst (Cexp_fst q)))
            candle_cv_q_taylor_model_scale)
          (candle_cv_q_den q)))
      (candle_cv_q_fixed_make
        (Cexp_div
          (Cexp_mul
            (Cexp_sub (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
            candle_cv_q_taylor_model_scale)
          (candle_cv_q_den q))
        (Cexp_num 0))`;;

let candle_cv_q_fixed_round_upper_def = new_definition
 `candle_cv_q_fixed_round_upper q =
    Cexp_if (Cexp_less (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
      (candle_cv_q_fixed_make (Cexp_num 0)
        (Cexp_div
          (Cexp_mul
            (Cexp_sub (Cexp_snd (Cexp_fst q)) (Cexp_fst (Cexp_fst q)))
            candle_cv_q_taylor_model_scale)
          (candle_cv_q_den q)))
      (candle_cv_q_fixed_make
        (candle_cv_q_ceil_div
          (Cexp_mul
            (Cexp_sub (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
            candle_cv_q_taylor_model_scale)
          (candle_cv_q_den q))
        (Cexp_num 0))`;;

let candle_cv_q_fixed_interval_round_def = new_definition
 `candle_cv_q_fixed_interval_round x =
    Cexp_pair
      (candle_cv_q_fixed_round_lower (Cexp_fst x))
      (candle_cv_q_fixed_round_upper (Cexp_snd x))`;;

let candle_cv_q_fixed_interval_list_round_def = define
 `(candle_cv_q_fixed_interval_list_round (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_fixed_interval_list_round (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_fixed_interval_round h)
       (candle_cv_q_fixed_interval_list_round t))`;;

let candle_cv_q_fixed_interval_matrix_round_def = define
 `(candle_cv_q_fixed_interval_matrix_round (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_fixed_interval_matrix_round (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_fixed_interval_list_round h)
       (candle_cv_q_fixed_interval_matrix_round t))`;;

let candle_cv_q_fixed_list_round_upper_def = define
 `(candle_cv_q_fixed_list_round_upper (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_fixed_list_round_upper (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_fixed_round_upper h)
       (candle_cv_q_fixed_list_round_upper t))`;;

let candle_cv_q_fixed_interval_list_round_compute = prove
 (`!items.
     candle_cv_q_fixed_interval_list_round items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair
         (candle_cv_q_fixed_interval_round (Cexp_fst items))
         (candle_cv_q_fixed_interval_list_round (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_fixed_interval_list_round_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_fixed_interval_matrix_round_compute = prove
 (`!row_lists.
     candle_cv_q_fixed_interval_matrix_round row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_pair
         (candle_cv_q_fixed_interval_list_round (Cexp_fst row_lists))
         (candle_cv_q_fixed_interval_matrix_round (Cexp_snd row_lists)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_fixed_interval_matrix_round_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_fixed_list_round_upper_compute = prove
 (`!items.
     candle_cv_q_fixed_list_round_upper items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair (candle_cv_q_fixed_round_upper (Cexp_fst items))
         (candle_cv_q_fixed_list_round_upper (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_fixed_list_round_upper_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_first_jet_fixed_round_def = new_definition
 `candle_cv_q_dim_first_jet_fixed_round jet =
    candle_cv_q_dim_first_jet_make
      (candle_cv_q_fixed_interval_round
        (candle_cv_q_dim_first_jet_f jet))
      (candle_cv_q_fixed_interval_list_round
        (candle_cv_q_dim_first_jet_gradient jet))`;;

(* A Taylor-model result is                                                 *)
(*   (domain,(center-first-jet,(box-value,(box-gradient,box-Hessian)))).    *)
(* The three whole-box components are cached when a stack node is built.    *)
(* This is semantically redundant but prevents repeated Taylor reconstruction *)
(* in the pure computation term.                                            *)

let candle_cv_q_dim_taylor_model_result_make_def = new_definition
 `candle_cv_q_dim_taylor_model_result_make
      domain center_first value_bound gradient_bounds hessian =
    Cexp_pair domain
      (Cexp_pair center_first
        (Cexp_pair value_bound (Cexp_pair gradient_bounds hessian)))`;;

let candle_cv_q_dim_taylor_model_result_domain_def = new_definition
 `candle_cv_q_dim_taylor_model_result_domain result = Cexp_fst result`;;

let candle_cv_q_dim_taylor_model_result_center_def = new_definition
 `candle_cv_q_dim_taylor_model_result_center result =
    Cexp_fst (Cexp_snd result)`;;

let candle_cv_q_dim_taylor_model_result_hessian_def = new_definition
 `candle_cv_q_dim_taylor_model_result_hessian result =
    Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd result)))`;;

let candle_cv_q_dim_taylor_model_result_value_bound_def = new_definition
 `candle_cv_q_dim_taylor_model_result_value_bound result =
    Cexp_fst (Cexp_snd (Cexp_snd result))`;;

let candle_cv_q_dim_taylor_model_result_gradient_bounds_def = new_definition
 `candle_cv_q_dim_taylor_model_result_gradient_bounds result =
    Cexp_fst (Cexp_snd (Cexp_snd (Cexp_snd result)))`;;

let candle_cv_q_dim_taylor_model_result_default_def = new_definition
 `candle_cv_q_dim_taylor_model_result_default center_boxes boxes =
    candle_cv_q_dim_taylor_model_result_make (Cexp_num 0)
      (candle_cv_q_dim_first_jet_zero center_boxes)
      candle_cv_q_zero_interval
      (candle_cv_q_dim_interval_zeros boxes)
      (candle_cv_q_dim_interval_zero_matrix boxes boxes)`;;

let candle_cv_q_dim_taylor_model_result_head_def = new_definition
 `candle_cv_q_dim_taylor_model_result_head center_boxes boxes stack =
    Cexp_if (Cexp_ispair stack) (Cexp_fst stack)
      (candle_cv_q_dim_taylor_model_result_default center_boxes boxes)`;;

let candle_cv_q_dim_taylor_model_result_tail_def = new_definition
 `candle_cv_q_dim_taylor_model_result_tail stack =
    Cexp_if (Cexp_ispair stack) (Cexp_snd stack) (Cexp_num 0)`;;

(* Reconstruct the whole-box range of a child from its center value, center  *)
(* gradient, and whole-box Hessian.                                           *)

let candle_cv_q_dim_taylor_model_error_def = new_definition
 `candle_cv_q_dim_taylor_model_error radii center_first hessian =
    candle_cv_q_add_normalized_extended
      (candle_cv_q_dot_abs_upper_extended radii
        (candle_cv_q_dim_first_jet_gradient
          center_first))
      (candle_cv_q_mul_normalized_extended candle_cv_q_half
        (candle_cv_q_weighted_rows_abs_upper_extended radii radii
          hessian))`;;

let candle_cv_q_dim_taylor_model_value_bound_def = new_definition
 `candle_cv_q_dim_taylor_model_value_bound radii center_first hessian =
    candle_cv_q_interval_add_extended
      (candle_cv_q_dim_first_jet_f
        center_first)
      (candle_cv_q_symmetric_interval
        (candle_cv_q_dim_taylor_model_error
          radii center_first hessian))`;;

(* Each partial derivative is bounded by its center enclosure plus the       *)
(* radius-weighted absolute Hessian row.                                      *)

let candle_cv_q_dim_taylor_model_gradient_bounds_def = define
 `(candle_cv_q_dim_taylor_model_gradient_bounds
     radii (Cexp_num n) row_lists = Cexp_num 0) /\
  (candle_cv_q_dim_taylor_model_gradient_bounds
     radii (Cexp_pair gradient_interval gradient_tail) (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_q_dim_taylor_model_gradient_bounds
     radii (Cexp_pair gradient_interval gradient_tail)
       (Cexp_pair interval_row row_tail) =
     Cexp_pair
       (candle_cv_q_interval_add_extended gradient_interval
         (candle_cv_q_symmetric_interval
           (candle_cv_q_dot_abs_upper_extended radii interval_row)))
       (candle_cv_q_dim_taylor_model_gradient_bounds
         radii gradient_tail row_tail))`;;

let candle_cv_q_dim_taylor_model_gradient_bounds_compute = prove
 (`!radii gradient_intervals row_lists.
     candle_cv_q_dim_taylor_model_gradient_bounds
       radii gradient_intervals row_lists =
     Cexp_if (Cexp_ispair gradient_intervals)
       (Cexp_if (Cexp_ispair row_lists)
         (Cexp_pair
           (candle_cv_q_interval_add_extended
             (Cexp_fst gradient_intervals)
             (candle_cv_q_symmetric_interval
               (candle_cv_q_dot_abs_upper_extended
                 radii (Cexp_fst row_lists))))
           (candle_cv_q_dim_taylor_model_gradient_bounds radii
             (Cexp_snd gradient_intervals) (Cexp_snd row_lists)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `gradient_intervals:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_model_gradient_bounds_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_model_result_complete_rounded_def = new_definition
 `candle_cv_q_dim_taylor_model_result_complete_rounded
      radii domain center_first hessian =
    candle_cv_q_dim_taylor_model_result_make domain center_first
      (candle_cv_q_fixed_interval_round
        (candle_cv_q_dim_taylor_model_value_bound
          radii center_first hessian))
      (candle_cv_q_fixed_interval_list_round
        (candle_cv_q_dim_taylor_model_gradient_bounds radii
          (candle_cv_q_dim_first_jet_gradient center_first) hessian))
      hessian`;;

let candle_cv_q_dim_taylor_model_result_complete_def = new_definition
 `candle_cv_q_dim_taylor_model_result_complete
      radii domain center_first hessian =
    candle_cv_q_dim_taylor_model_result_complete_rounded radii domain
      (candle_cv_q_dim_first_jet_fixed_round center_first)
      (candle_cv_q_fixed_interval_matrix_round hessian)`;;

let candle_cv_q_dim_taylor_model_proxy_def = new_definition
 `candle_cv_q_dim_taylor_model_proxy result =
    candle_cv_q_dim_jet_make
      (candle_cv_q_dim_taylor_model_result_value_bound result)
      (candle_cv_q_dim_taylor_model_result_gradient_bounds result)
      (candle_cv_q_dim_taylor_model_result_hessian result)`;;

let candle_cv_q_dim_taylor_model_result_neg_def = new_definition
 `candle_cv_q_dim_taylor_model_result_neg radii result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_q_dim_taylor_model_result_domain result)
      (candle_cv_q_dim_first_jet_neg
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_interval_matrix_neg
        (candle_cv_q_dim_taylor_model_result_hessian result))`;;

let candle_cv_q_dim_taylor_model_result_add_def = new_definition
 `candle_cv_q_dim_taylor_model_result_add radii left right =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_bool_and
        (candle_cv_q_dim_taylor_model_result_domain left)
        (candle_cv_q_dim_taylor_model_result_domain right))
      (candle_cv_q_dim_first_jet_add
        (candle_cv_q_dim_taylor_model_result_center left)
        (candle_cv_q_dim_taylor_model_result_center right))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_taylor_model_result_hessian left)
        (candle_cv_q_dim_taylor_model_result_hessian right))`;;

let candle_cv_q_dim_taylor_model_result_mul_def = new_definition
 `candle_cv_q_dim_taylor_model_result_mul radii left right =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_bool_and
        (candle_cv_q_dim_taylor_model_result_domain left)
        (candle_cv_q_dim_taylor_model_result_domain right))
      (candle_cv_q_dim_first_jet_mul
        (candle_cv_q_dim_taylor_model_result_center left)
        (candle_cv_q_dim_taylor_model_result_center right))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_mul
          (candle_cv_q_dim_taylor_model_proxy left)
          (candle_cv_q_dim_taylor_model_proxy right)))`;;

let candle_cv_q_dim_taylor_model_result_square_def = new_definition
 `candle_cv_q_dim_taylor_model_result_square radii result =
    candle_cv_q_dim_taylor_model_result_mul radii result result`;;

let candle_cv_q_dim_taylor_model_result_inv_def = new_definition
 `candle_cv_q_dim_taylor_model_result_inv radii result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_bool_and
        (candle_cv_q_dim_taylor_model_result_domain result)
        (candle_cv_bool_and
          (candle_cv_q_dim_analytic_first_jet_inv_domain
            (candle_cv_q_dim_taylor_model_result_center result))
          (candle_cv_q_dim_jet_inv_domain
            (candle_cv_q_dim_taylor_model_proxy result))))
      (candle_cv_q_dim_analytic_first_jet_inv
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_inv
          (candle_cv_q_dim_taylor_model_proxy result)))`;;

let candle_cv_q_dim_taylor_model_result_sqrt_def = new_definition
 `candle_cv_q_dim_taylor_model_result_sqrt
      radii center_s box_s result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_bool_and
        (candle_cv_q_dim_taylor_model_result_domain result)
        (candle_cv_bool_and
          (candle_cv_q_dim_analytic_first_jet_sqrt_domain center_s
            (candle_cv_q_dim_taylor_model_result_center result))
          (candle_cv_q_dim_jet_sqrt_domain box_s
            (candle_cv_q_dim_taylor_model_proxy result))))
      (candle_cv_q_dim_analytic_first_jet_sqrt_with center_s
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_sqrt_with box_s
          (candle_cv_q_dim_taylor_model_proxy result)))`;;

let candle_cv_q_dim_taylor_model_result_atn_def = new_definition
 `candle_cv_q_dim_taylor_model_result_atn radii result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_bool_and
        (candle_cv_q_dim_taylor_model_result_domain result)
        (candle_cv_bool_and
          (candle_cv_q_dim_analytic_first_jet_atn_domain
            (candle_cv_q_dim_taylor_model_result_center result))
          (candle_cv_q_dim_jet_atn_domain
            (candle_cv_q_dim_taylor_model_proxy result))))
      (candle_cv_q_dim_analytic_first_jet_atn
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_atn
          (candle_cv_q_dim_taylor_model_proxy result)))`;;

let candle_cv_q_dim_taylor_model_result_pi_half_def = new_definition
 `candle_cv_q_dim_taylor_model_result_pi_half radii center_boxes boxes =
    candle_cv_q_dim_taylor_model_result_complete radii (Cexp_num 1)
      (candle_cv_q_dim_analytic_first_jet_pi_half center_boxes)
      (candle_cv_q_dim_interval_zero_matrix boxes boxes)`;;

(* Polynomial leaves must use the same centered composition boundary.  A    *)
(* whole-box forward polynomial jet would reintroduce the dependency loss   *)
(* that this interpreter is intended to avoid.                               *)

let candle_cv_q_dim_taylor_model_poly_constant_def = new_definition
 `candle_cv_q_dim_taylor_model_poly_constant
      center_boxes boxes radii q =
    candle_cv_q_dim_taylor_model_result_complete radii (Cexp_num 1)
      (candle_cv_q_dim_first_jet_constant center_boxes q)
      (candle_cv_q_dim_interval_zero_matrix boxes boxes)`;;

let candle_cv_q_dim_taylor_model_poly_variable_def = new_definition
 `candle_cv_q_dim_taylor_model_poly_variable
      center_boxes boxes radii variable =
    candle_cv_q_dim_taylor_model_result_complete radii (Cexp_num 1)
      (candle_cv_q_dim_first_jet_variable center_boxes variable)
      (candle_cv_q_dim_interval_zero_matrix boxes boxes)`;;

let candle_cv_q_dim_taylor_model_poly_step_def = new_definition
 `candle_cv_q_dim_taylor_model_poly_step
      center_boxes boxes radii instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (Cexp_pair
          (candle_cv_q_dim_taylor_model_poly_constant
            center_boxes boxes radii (Cexp_snd instruction)) stack)
        (Cexp_pair
          (candle_cv_q_dim_taylor_model_poly_variable
            center_boxes boxes radii (Cexp_snd instruction)) stack))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_pair
          (candle_cv_q_dim_taylor_model_result_neg radii
            (candle_cv_q_dim_taylor_model_result_head
              center_boxes boxes stack))
          (candle_cv_q_dim_taylor_model_result_tail stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_pair
            (candle_cv_q_dim_taylor_model_result_add radii
              (candle_cv_q_dim_taylor_model_result_head
                center_boxes boxes
                (candle_cv_q_dim_taylor_model_result_tail stack))
              (candle_cv_q_dim_taylor_model_result_head
                center_boxes boxes stack))
            (candle_cv_q_dim_taylor_model_result_tail
              (candle_cv_q_dim_taylor_model_result_tail stack)))
          (Cexp_if (Cexp_eq instruction (Cexp_num 4))
            (Cexp_pair
              (candle_cv_q_dim_taylor_model_result_mul radii
                (candle_cv_q_dim_taylor_model_result_head
                  center_boxes boxes
                  (candle_cv_q_dim_taylor_model_result_tail stack))
                (candle_cv_q_dim_taylor_model_result_head
                  center_boxes boxes stack))
              (candle_cv_q_dim_taylor_model_result_tail
                (candle_cv_q_dim_taylor_model_result_tail stack)))
            (Cexp_pair
              (candle_cv_q_dim_taylor_model_result_square radii
                (candle_cv_q_dim_taylor_model_result_head
                  center_boxes boxes stack))
              (candle_cv_q_dim_taylor_model_result_tail stack)))))`;;

let candle_cv_q_dim_taylor_model_poly_run_def = define
 `(candle_cv_q_dim_taylor_model_poly_run
     center_boxes boxes radii (Cexp_num n) stack = stack) /\
  (candle_cv_q_dim_taylor_model_poly_run
     center_boxes boxes radii (Cexp_pair h t) stack =
     candle_cv_q_dim_taylor_model_poly_run center_boxes boxes radii t
       (candle_cv_q_dim_taylor_model_poly_step
         center_boxes boxes radii h stack))`;;

let candle_cv_q_dim_taylor_model_poly_run_compute = prove
 (`!center_boxes boxes radii program stack.
     candle_cv_q_dim_taylor_model_poly_run
       center_boxes boxes radii program stack =
     Cexp_if (Cexp_ispair program)
       (candle_cv_q_dim_taylor_model_poly_run
         center_boxes boxes radii (Cexp_snd program)
         (candle_cv_q_dim_taylor_model_poly_step
           center_boxes boxes radii (Cexp_fst program) stack))
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_model_poly_run_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_model_poly_program_def = new_definition
 `candle_cv_q_dim_taylor_model_poly_program
      center_boxes boxes radii program =
    candle_cv_q_dim_taylor_model_result_head center_boxes boxes
      (candle_cv_q_dim_taylor_model_poly_run
        center_boxes boxes radii program (Cexp_num 0))`;;

let candle_cv_q_dim_taylor_model_program_step_def = new_definition
 `candle_cv_q_dim_taylor_model_program_step
      center_boxes boxes radii center_instruction box_instruction stack =
    Cexp_if (Cexp_ispair center_instruction)
      (Cexp_if (Cexp_ispair box_instruction)
          (Cexp_if (Cexp_eq (Cexp_fst center_instruction) (Cexp_num 0))
          (Cexp_if (Cexp_eq (Cexp_fst box_instruction) (Cexp_num 0))
            (Cexp_pair
              (candle_cv_q_dim_taylor_model_poly_program
                center_boxes boxes radii
                (Cexp_snd center_instruction))
              stack)
            (Cexp_pair
              (candle_cv_q_dim_taylor_model_result_default
                center_boxes boxes) stack))
          (Cexp_if
            (Cexp_eq (Cexp_fst center_instruction) (Cexp_num 1))
            (Cexp_if (Cexp_eq (Cexp_fst box_instruction) (Cexp_num 1))
              (Cexp_pair
                (candle_cv_q_dim_taylor_model_result_sqrt radii
                  (Cexp_snd center_instruction) (Cexp_snd box_instruction)
                  (candle_cv_q_dim_taylor_model_result_head
                    center_boxes boxes stack))
                (candle_cv_q_dim_taylor_model_result_tail stack))
              (Cexp_pair
                (candle_cv_q_dim_taylor_model_result_default
                  center_boxes boxes) stack))
            (Cexp_pair
              (candle_cv_q_dim_taylor_model_result_default
                center_boxes boxes) stack)))
        (Cexp_pair
          (candle_cv_q_dim_taylor_model_result_default center_boxes boxes)
          stack))
      (Cexp_if (Cexp_ispair box_instruction)
        (Cexp_pair
          (candle_cv_q_dim_taylor_model_result_default center_boxes boxes)
          stack)
        (Cexp_if (Cexp_eq center_instruction box_instruction)
          (Cexp_if (Cexp_eq center_instruction (Cexp_num 2))
            (Cexp_pair
              (candle_cv_q_dim_taylor_model_result_neg radii
                (candle_cv_q_dim_taylor_model_result_head
                  center_boxes boxes stack))
              (candle_cv_q_dim_taylor_model_result_tail stack))
            (Cexp_if (Cexp_eq center_instruction (Cexp_num 3))
              (Cexp_pair
                (candle_cv_q_dim_taylor_model_result_add radii
                  (candle_cv_q_dim_taylor_model_result_head
                    center_boxes boxes
                    (candle_cv_q_dim_taylor_model_result_tail stack))
                  (candle_cv_q_dim_taylor_model_result_head
                    center_boxes boxes stack))
                (candle_cv_q_dim_taylor_model_result_tail
                  (candle_cv_q_dim_taylor_model_result_tail stack)))
              (Cexp_if (Cexp_eq center_instruction (Cexp_num 4))
                (Cexp_pair
                  (candle_cv_q_dim_taylor_model_result_mul radii
                    (candle_cv_q_dim_taylor_model_result_head
                      center_boxes boxes
                      (candle_cv_q_dim_taylor_model_result_tail stack))
                    (candle_cv_q_dim_taylor_model_result_head
                      center_boxes boxes stack))
                  (candle_cv_q_dim_taylor_model_result_tail
                    (candle_cv_q_dim_taylor_model_result_tail stack)))
                (Cexp_if (Cexp_eq center_instruction (Cexp_num 5))
                  (Cexp_pair
                    (candle_cv_q_dim_taylor_model_result_square radii
                      (candle_cv_q_dim_taylor_model_result_head
                        center_boxes boxes stack))
                    (candle_cv_q_dim_taylor_model_result_tail stack))
                  (Cexp_if (Cexp_eq center_instruction (Cexp_num 6))
                    (Cexp_pair
                      (candle_cv_q_dim_taylor_model_result_inv radii
                        (candle_cv_q_dim_taylor_model_result_head
                          center_boxes boxes stack))
                      (candle_cv_q_dim_taylor_model_result_tail stack))
                    (Cexp_if (Cexp_eq center_instruction (Cexp_num 7))
                      (Cexp_pair
                        (candle_cv_q_dim_taylor_model_result_atn radii
                          (candle_cv_q_dim_taylor_model_result_head
                            center_boxes boxes stack))
                        (candle_cv_q_dim_taylor_model_result_tail stack))
                      (Cexp_if (Cexp_eq center_instruction (Cexp_num 8))
                        (Cexp_pair
                          (candle_cv_q_dim_taylor_model_result_pi_half
                            radii center_boxes boxes) stack)
                        (Cexp_pair
                          (candle_cv_q_dim_taylor_model_result_default
                            center_boxes boxes) stack))))))))
          (Cexp_pair
            (candle_cv_q_dim_taylor_model_result_default center_boxes boxes)
            stack)))`;;

let candle_cv_q_dim_taylor_model_program_run_def = define
 `(candle_cv_q_dim_taylor_model_program_run
     center_boxes boxes radii (Cexp_num n) box_program stack = stack) /\
  (candle_cv_q_dim_taylor_model_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_q_dim_taylor_model_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_q_dim_taylor_model_program_run
       center_boxes boxes radii ct bt
       (candle_cv_q_dim_taylor_model_program_step
         center_boxes boxes radii ch bh stack))`;;

let candle_cv_q_dim_taylor_model_program_run_compute = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_cv_q_dim_taylor_model_program_run
       center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_q_dim_taylor_model_program_run
           center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_q_dim_taylor_model_program_step
             center_boxes boxes radii
             (Cexp_fst center_program) (Cexp_fst box_program) stack))
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_model_program_run_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

(* A single-pass development trace records the accumulated domain bit after *)
(* each analytic instruction.  Keeping it beside the numerical result makes *)
(* guard localization cost one execution rather than one execution/prefix.   *)

let candle_cv_q_dim_taylor_model_trace_guards_def = new_definition
 `candle_cv_q_dim_taylor_model_trace_guards
      center_boxes boxes center_instruction box_instruction stack =
    Cexp_if (Cexp_ispair center_instruction)
      (Cexp_if (Cexp_ispair box_instruction)
        (Cexp_if
          (candle_cv_bool_and
            (Cexp_eq (Cexp_fst center_instruction) (Cexp_num 1))
            (Cexp_eq (Cexp_fst box_instruction) (Cexp_num 1)))
          (Cexp_pair
            (candle_cv_q_dim_analytic_first_jet_sqrt_domain
              (Cexp_snd center_instruction)
              (candle_cv_q_dim_taylor_model_result_center
                (candle_cv_q_dim_taylor_model_result_head
                  center_boxes boxes stack)))
            (Cexp_pair
              (candle_cv_q_dim_jet_sqrt_domain
                (Cexp_snd box_instruction)
                (candle_cv_q_dim_taylor_model_proxy
                  (candle_cv_q_dim_taylor_model_result_head
                    center_boxes boxes stack)))
              (candle_cv_q_dim_taylor_model_result_value_bound
                (candle_cv_q_dim_taylor_model_result_head
                  center_boxes boxes stack))))
          (Cexp_pair (Cexp_num 1)
            (Cexp_pair (Cexp_num 1) candle_cv_q_zero_interval)))
        (Cexp_pair (Cexp_num 1)
          (Cexp_pair (Cexp_num 1) candle_cv_q_zero_interval)))
      (Cexp_pair (Cexp_num 1)
        (Cexp_pair (Cexp_num 1) candle_cv_q_zero_interval))`;;

let candle_cv_q_dim_taylor_model_trace_record_def = new_definition
 `candle_cv_q_dim_taylor_model_trace_record
      center_boxes boxes center_instruction box_instruction
        previous_stack stepped domain_log =
    Cexp_pair stepped
      (Cexp_pair
        (Cexp_pair
          (candle_cv_q_dim_taylor_model_result_domain
            (candle_cv_q_dim_taylor_model_result_head
              center_boxes boxes stepped))
          (candle_cv_q_dim_taylor_model_trace_guards
            center_boxes boxes center_instruction box_instruction
            previous_stack))
        domain_log)`;;

let candle_cv_q_dim_taylor_model_trace_run_def = define
 `(candle_cv_q_dim_taylor_model_trace_run
     center_boxes boxes radii (Cexp_num n) box_program state = state) /\
  (candle_cv_q_dim_taylor_model_trace_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) state = state) /\
  (candle_cv_q_dim_taylor_model_trace_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_pair bh bt)
       state =
     candle_cv_q_dim_taylor_model_trace_run
       center_boxes boxes radii ct bt
       (candle_cv_q_dim_taylor_model_trace_record center_boxes boxes
         ch bh (Cexp_fst state)
         (candle_cv_q_dim_taylor_model_program_step
           center_boxes boxes radii ch bh (Cexp_fst state))
         (Cexp_snd state)))`;;

let candle_cv_q_dim_taylor_model_trace_run_compute = prove
 (`!center_boxes boxes radii center_program box_program state.
     candle_cv_q_dim_taylor_model_trace_run
       center_boxes boxes radii center_program box_program state =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_q_dim_taylor_model_trace_run
           center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_q_dim_taylor_model_trace_record center_boxes boxes
             (Cexp_fst center_program) (Cexp_fst box_program)
             (Cexp_fst state)
             (candle_cv_q_dim_taylor_model_program_step
               center_boxes boxes radii
               (Cexp_fst center_program) (Cexp_fst box_program)
               (Cexp_fst state))
             (Cexp_snd state)))
         state)
       state`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_model_trace_run_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_model_trace_finish_def = new_definition
 `candle_cv_q_dim_taylor_model_trace_finish center_boxes boxes state =
    Cexp_pair
      (candle_cv_q_dim_taylor_model_result_head
        center_boxes boxes (Cexp_fst state))
      (Cexp_snd state)`;;

let candle_cv_q_dim_taylor_model_program_trace_def = new_definition
 `candle_cv_q_dim_taylor_model_program_trace
      center_program box_program boxes =
    candle_cv_q_dim_taylor_model_trace_finish
      (candle_cv_q_center_environment_list boxes) boxes
      (candle_cv_q_dim_taylor_model_trace_run
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_q_fixed_list_round_upper
          (candle_cv_q_radius_list boxes))
        center_program box_program
        (Cexp_pair (Cexp_num 0) (Cexp_num 0)))`;;

let candle_cv_q_dim_taylor_model_program_def = new_definition
 `candle_cv_q_dim_taylor_model_program center_program box_program boxes =
    candle_cv_q_dim_taylor_model_result_head
      (candle_cv_q_center_environment_list boxes) boxes
      (candle_cv_q_dim_taylor_model_program_run
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_q_fixed_list_round_upper
          (candle_cv_q_radius_list boxes))
        center_program box_program (Cexp_num 0))`;;

let candle_cv_q_dim_taylor_model_upper_def = new_definition
 `candle_cv_q_dim_taylor_model_upper boxes result =
    candle_cv_q_dim_taylor_upper_extended
      (candle_cv_q_fixed_list_round_upper
        (candle_cv_q_radius_list boxes))
      (candle_cv_q_dim_first_jet_f
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_first_jet_gradient
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_taylor_model_result_hessian result)`;;

let candle_cv_q_dim_taylor_model_finish_def = new_definition
 `candle_cv_q_dim_taylor_model_finish boxes result =
    candle_cv_q_dim_whole_box_finish
      (candle_cv_q_dim_taylor_model_result_domain result)
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_q_dim_taylor_model_upper boxes result)`;;

let candle_cv_q_dim_taylor_model_check_def = new_definition
 `candle_cv_q_dim_taylor_model_check center_program box_program boxes =
    candle_cv_q_dim_taylor_model_finish boxes
      (candle_cv_q_dim_taylor_model_program
        center_program box_program boxes)`;;

let candle_cv_q_dim_taylor_model_compute_eqs =
  union candle_cv_q_dim_analytic_split_certificate_compute_eqs
    (map SPEC_ALL
      [candle_cv_q_interval_add_extended_def;
       candle_cv_q_symmetric_interval_def;
       candle_cv_q_taylor_model_scale_def;
       candle_cv_q_ceil_div_def;
       candle_cv_q_fixed_make_def;
       candle_cv_q_fixed_round_lower_def;
       candle_cv_q_fixed_round_upper_def;
       candle_cv_q_fixed_interval_round_def;
       candle_cv_q_fixed_interval_list_round_compute;
       candle_cv_q_fixed_interval_matrix_round_compute;
       candle_cv_q_fixed_list_round_upper_compute;
       candle_cv_q_dim_first_jet_fixed_round_def;
       candle_cv_q_dim_taylor_model_result_make_def;
       candle_cv_q_dim_taylor_model_result_domain_def;
       candle_cv_q_dim_taylor_model_result_center_def;
       candle_cv_q_dim_taylor_model_result_hessian_def;
       candle_cv_q_dim_taylor_model_result_value_bound_def;
       candle_cv_q_dim_taylor_model_result_gradient_bounds_def;
       candle_cv_q_dim_taylor_model_result_default_def;
       candle_cv_q_dim_taylor_model_result_head_def;
       candle_cv_q_dim_taylor_model_result_tail_def;
       candle_cv_q_dim_taylor_model_error_def;
       candle_cv_q_dim_taylor_model_value_bound_def;
       candle_cv_q_dim_taylor_model_gradient_bounds_compute;
       candle_cv_q_dim_taylor_model_result_complete_rounded_def;
       candle_cv_q_dim_taylor_model_result_complete_def;
       candle_cv_q_dim_taylor_model_proxy_def;
       candle_cv_q_dim_taylor_model_result_neg_def;
       candle_cv_q_dim_taylor_model_result_add_def;
       candle_cv_q_dim_taylor_model_result_mul_def;
       candle_cv_q_dim_taylor_model_result_square_def;
       candle_cv_q_dim_taylor_model_result_inv_def;
       candle_cv_q_dim_taylor_model_result_sqrt_def;
       candle_cv_q_dim_taylor_model_result_atn_def;
       candle_cv_q_dim_taylor_model_result_pi_half_def;
       candle_cv_q_dim_taylor_model_poly_constant_def;
       candle_cv_q_dim_taylor_model_poly_variable_def;
       candle_cv_q_dim_taylor_model_poly_step_def;
       candle_cv_q_dim_taylor_model_poly_run_compute;
       candle_cv_q_dim_taylor_model_poly_program_def;
       candle_cv_q_dim_taylor_model_program_step_def;
       candle_cv_q_dim_taylor_model_program_run_compute;
       candle_cv_q_dim_taylor_model_trace_guards_def;
       candle_cv_q_dim_taylor_model_trace_record_def;
       candle_cv_q_dim_taylor_model_trace_run_compute;
       candle_cv_q_dim_taylor_model_trace_finish_def;
       candle_cv_q_dim_taylor_model_program_trace_def;
       candle_cv_q_dim_taylor_model_program_def;
       candle_cv_q_dim_taylor_model_upper_def;
       candle_cv_q_dim_taylor_model_finish_def;
       candle_cv_q_dim_taylor_model_check_def]);;

end;;
