(* ========================================================================== *)
(* Executable representation of exact packed analytic object-q states.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fast word checker refines to an exact     *)
(* six-field object state.  This file fixes the ordinary Candle cval layout  *)
(* for that state and proves every projection and the final packed acceptance *)
(* wrapper against the ordinary-HOL object.                                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_object_compute.ml";;

module Candle_cv_analytic_expr_packed_source_object_representation = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_compute;;

(* Layout:                                                               *)
(*   (domain,(center-value,(center-gradient,                            *)
(*     (whole-value,(whole-gradient,packed-Hessian)))))                 *)

let candle_cv_q_packed_object_state_make_def = new_definition
 `candle_cv_q_packed_object_state_make domain center_value center_gradient
      value_bound gradient_bounds packed_hessian =
    Cexp_pair domain
      (Cexp_pair center_value
        (Cexp_pair center_gradient
          (Cexp_pair value_bound
            (Cexp_pair gradient_bounds packed_hessian))))`;;

let candle_cv_q_packed_object_state_domain_def = new_definition
 `candle_cv_q_packed_object_state_domain state = Cexp_fst state`;;

let candle_cv_q_packed_object_state_center_value_def = new_definition
 `candle_cv_q_packed_object_state_center_value state =
    Cexp_fst (Cexp_snd state)`;;

let candle_cv_q_packed_object_state_center_gradient_def = new_definition
 `candle_cv_q_packed_object_state_center_gradient state =
    Cexp_fst (Cexp_snd (Cexp_snd state))`;;

let candle_cv_q_packed_object_state_value_bound_def = new_definition
 `candle_cv_q_packed_object_state_value_bound state =
    Cexp_fst (Cexp_snd (Cexp_snd (Cexp_snd state)))`;;

let candle_cv_q_packed_object_state_gradient_bounds_def = new_definition
 `candle_cv_q_packed_object_state_gradient_bounds state =
    Cexp_fst (Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd state))))`;;

let candle_cv_q_packed_object_state_packed_hessian_def = new_definition
 `candle_cv_q_packed_object_state_packed_hessian state =
    Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd state))))`;;

let candle_cv_q_packed_object_state_encode_def = define
 `candle_cv_q_packed_object_state_encode
    (Candle_q_packed_object_state domain center_value center_gradient
      value_bound gradient_bounds packed_hessian) =
    candle_cv_q_packed_object_state_make
      (candle_cv_bool domain)
      (candle_cv_q_interval center_value)
      (candle_cv_q_interval_list center_gradient)
      (candle_cv_q_interval value_bound)
      (candle_cv_q_interval_list gradient_bounds)
      (candle_cv_q_interval_list packed_hessian)`;;

let candle_cv_q_packed_object_item_state_encode_def = define
 `candle_cv_q_packed_object_item_state_encode
    (Candle_q_packed_object_item state center_e box_e) =
    candle_cv_q_packed_object_state_encode state`;;

let candle_cv_q_packed_object_stack_encode_def = define
 `(candle_cv_q_packed_object_stack_encode [] = Cexp_num 0) /\
  (candle_cv_q_packed_object_stack_encode (CONS item rest) =
    Cexp_pair (candle_cv_q_packed_object_item_state_encode item)
      (candle_cv_q_packed_object_stack_encode rest))`;;

let candle_cv_q_packed_object_state_make_correct = prove
 (`!domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     candle_cv_q_packed_object_state_make
       (candle_cv_bool domain)
       (candle_cv_q_interval center_value)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval value_bound)
       (candle_cv_q_interval_list gradient_bounds)
       (candle_cv_q_interval_list packed_hessian) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state domain center_value center_gradient
         value_bound gradient_bounds packed_hessian)`,
  REWRITE_TAC[candle_cv_q_packed_object_state_encode_def]);;

let candle_cv_q_packed_object_state_domain_correct = prove
 (`!domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     candle_cv_q_packed_object_state_domain
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_bool domain`,
  REWRITE_TAC[candle_cv_q_packed_object_state_domain_def;
              candle_cv_q_packed_object_state_encode_def;
              candle_cv_q_packed_object_state_make_def;
              cexp_fst_def]);;

let candle_cv_q_packed_object_state_center_value_correct = prove
 (`!domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     candle_cv_q_packed_object_state_center_value
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_interval center_value`,
  REWRITE_TAC[candle_cv_q_packed_object_state_center_value_def;
              candle_cv_q_packed_object_state_encode_def;
              candle_cv_q_packed_object_state_make_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_packed_object_state_center_gradient_correct = prove
 (`!domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     candle_cv_q_packed_object_state_center_gradient
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_interval_list center_gradient`,
  REWRITE_TAC[candle_cv_q_packed_object_state_center_gradient_def;
              candle_cv_q_packed_object_state_encode_def;
              candle_cv_q_packed_object_state_make_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_packed_object_state_value_bound_correct = prove
 (`!domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     candle_cv_q_packed_object_state_value_bound
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_interval value_bound`,
  REWRITE_TAC[candle_cv_q_packed_object_state_value_bound_def;
              candle_cv_q_packed_object_state_encode_def;
              candle_cv_q_packed_object_state_make_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_packed_object_state_gradient_bounds_correct = prove
 (`!domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     candle_cv_q_packed_object_state_gradient_bounds
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_interval_list gradient_bounds`,
  REWRITE_TAC[candle_cv_q_packed_object_state_gradient_bounds_def;
              candle_cv_q_packed_object_state_encode_def;
              candle_cv_q_packed_object_state_make_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_packed_object_state_packed_hessian_correct = prove
 (`!domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     candle_cv_q_packed_object_state_packed_hessian
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_interval_list packed_hessian`,
  REWRITE_TAC[candle_cv_q_packed_object_state_packed_hessian_def;
              candle_cv_q_packed_object_state_encode_def;
              candle_cv_q_packed_object_state_make_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_packed_object_state_accept6_def = new_definition
 `candle_cv_q_packed_object_state_accept6 radii state =
    candle_cv_q_packed_object_accept6
      (candle_cv_q_packed_object_state_domain state)
      radii
      (candle_cv_q_packed_object_state_center_value state)
      (candle_cv_q_packed_object_state_center_gradient state)
      (candle_cv_q_packed_object_state_packed_hessian state)`;;

let candle_cv_q_packed_object_state_accept6_correct = prove
 (`!radii domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     candle_cv_q_packed_object_state_accept6
       (candle_cv_q_list radii)
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_packed_object_accept6
       (candle_cv_bool domain)
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_value)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed_hessian)`,
  REWRITE_TAC[candle_cv_q_packed_object_state_accept6_def;
              candle_cv_q_packed_object_state_domain_correct;
              candle_cv_q_packed_object_state_center_value_correct;
              candle_cv_q_packed_object_state_center_gradient_correct;
              candle_cv_q_packed_object_state_packed_hessian_correct]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_state_make_correct;
     candle_cv_q_packed_object_state_domain_correct;
     candle_cv_q_packed_object_state_center_value_correct;
     candle_cv_q_packed_object_state_center_gradient_correct;
     candle_cv_q_packed_object_state_value_bound_correct;
     candle_cv_q_packed_object_state_gradient_bounds_correct;
     candle_cv_q_packed_object_state_packed_hessian_correct;
     candle_cv_q_packed_object_state_accept6_correct] then
  failwith "packed object representation: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_REPRESENTATION_OK DEVELOPMENT_NON_RELEASE";;

end;;
