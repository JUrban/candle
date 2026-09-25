(* ========================================================================== *)
(* Executable certified boundary for centered analytic Taylor-model results. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Unlike the earlier experimental finish, this  *)
(* boundary consumes the value interval cached and outward-rounded by every  *)
(* high-level program instruction.                                            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_certified_compute = struct

open Candle_cv_analytic_expr_taylor_model_program_compute;;

let candle_cv_q_dim_taylor_model_certified_upper_def = new_definition
 `candle_cv_q_dim_taylor_model_certified_upper result =
    Cexp_snd (candle_cv_q_dim_taylor_model_result_value_bound result)`;;

let candle_cv_q_dim_taylor_model_certified_finish_def = new_definition
 `candle_cv_q_dim_taylor_model_certified_finish boxes result =
    candle_cv_q_dim_whole_box_finish
      (candle_cv_q_dim_taylor_model_result_domain result)
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_q_dim_taylor_model_certified_upper result)`;;

let candle_cv_q_dim_taylor_model_certified_check_def = new_definition
 `candle_cv_q_dim_taylor_model_certified_check
      center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_q_dim_taylor_model_program
        center_program box_program boxes)`;;

let candle_cv_q_dim_taylor_model_certified_compute_eqs =
  union candle_cv_q_dim_taylor_model_compute_eqs
    (map SPEC_ALL
      [candle_cv_q_dim_taylor_model_certified_upper_def;
       candle_cv_q_dim_taylor_model_certified_finish_def;
       candle_cv_q_dim_taylor_model_certified_check_def]);;

end;;
