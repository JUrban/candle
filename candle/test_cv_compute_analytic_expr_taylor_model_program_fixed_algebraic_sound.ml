needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_item_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound;;

let candle_fixed_algebraic_sound_axioms_before = axioms ();;

if hyp candle_cv_fsa_interval_matrix_of_q_correct <> [] ||
   hyp candle_cv_fsa_result_of_q_correct <> [] ||
   hyp candle_cv_fsa_item_is_fixed_correct <> [] ||
   hyp candle_cv_fsa_item_to_q_correct <> [] ||
   hyp candle_cv_fsa_item_to_fixed_correct <> [] ||
   hyp candle_cv_fsa_item_neg_correct <> [] ||
   hyp candle_cv_fsa_item_add_correct <> [] ||
   hyp candle_cv_fsa_item_mul_correct <> [] ||
   hyp candle_cv_fsa_item_square_correct <> [] ||
   hyp candle_cv_fsa_item_sqrt_correct <> [] ||
   hyp candle_cv_fsa_item_inv_correct <> [] ||
   hyp candle_cv_fsa_item_atn_correct <> [] ||
   hyp candle_cv_fsa_item_pi_half_correct <> [] ||
   hyp candle_cv_fsa_poly_item_correct <> [] ||
   hyp candle_fsa_item_fixed_view_analytic_invariant <> [] ||
   hyp candle_fsa_item_neg_analytic_invariant <> [] ||
   hyp candle_fsa_item_add_analytic_invariant <> [] ||
   hyp candle_fsa_item_mul_analytic_invariant <> [] ||
   hyp candle_fsa_item_square_analytic_invariant <> [] ||
   hyp candle_fsa_item_inv_analytic_invariant <> [] ||
   hyp candle_fsa_item_sqrt_analytic_invariant <> [] ||
   hyp candle_fsa_item_atn_analytic_invariant <> [] ||
   hyp candle_fsa_item_pi_half_analytic_invariant <> [] ||
   hyp candle_fsa_poly_item_analytic_invariant <> [] ||
   hyp candle_cv_fsa_logical_item_default_correct <> [] ||
   hyp candle_cv_fsa_logical_item_head_correct <> [] ||
   hyp candle_cv_fsa_logical_item_tail_correct <> [] ||
   hyp candle_cv_fsa_instruction_is_nonlinear_correct <> [] ||
   hyp candle_cv_fsa_program_has_nonlinear_correct <> [] ||
   hyp candle_cv_bool_not <> [] ||
   hyp candle_cv_fsa_logical_program_step_correct <> [] ||
   hyp candle_cv_fsa_logical_program_run_correct <> [] ||
   hyp candle_fsa_program_has_nonlinear_append <> [] ||
   hyp candle_fsa_logical_program_run_with_future_false <> [] ||
   hyp candle_fsa_logical_program_run_with_future_append <> [] ||
   hyp candle_fsa_interval_matrix_of_q_length <> [] ||
   hyp candle_fsa_interval_matrix_of_q_rows_width <> [] ||
   hyp candle_fsa_interval_matrix_of_q_map <> [] ||
   hyp candle_fsa_interval_matrix_of_q_contains <> [] ||
   hyp candle_fsa_interval_roundtrip_contains <> [] ||
   hyp candle_fsa_interval_list_roundtrip_length <> [] ||
   hyp candle_fsa_interval_list_roundtrip_contains <> [] ||
   hyp candle_fsa_interval_matrix_roundtrip_shape <> [] ||
   hyp candle_fsa_interval_matrix_roundtrip_contains <> [] ||
   hyp candle_fsa_jet_of_q_shape <> [] ||
   hyp candle_fsa_jet_of_q_f_contains <> [] ||
   hyp candle_fsa_jet_of_q_gradient_contains <> [] ||
   hyp candle_fsa_jet_of_q_hessian_contains <> [] ||
   hyp candle_fsa_jet_of_q_contains_components <> [] ||
   hyp candle_fsa_result_of_q_domain <> [] ||
   hyp candle_fsa_result_of_q_domain_roundtrip <> [] ||
   hyp candle_q_dim_taylor_model_proxy_hessian <> [] ||
   hyp candle_fsa_result_of_q_center <> [] ||
   hyp candle_fsa_result_of_q_proxy <> [] ||
   hyp candle_fsa_result_of_q_analytic_invariant <> [] ||
   hyp candle_q_dim_flyspeck_components_analytic_contains <> [] ||
   hyp candle_analytic_dd_matrix_flyspeck <> [] ||
   hyp candle_fs_result_complete_proxy_contains_box <> [] ||
   hyp candle_fs_result_complete_proxy_analytic_contains_box <> [] ||
   hyp candle_fs_result_complete_analytic_invariant <> [] ||
   hyp candle_fs_result_analytic_center_shape <> [] ||
   hyp candle_fs_result_analytic_center_contains <> [] ||
   hyp candle_fs_result_analytic_center_value_contains <> [] ||
   hyp candle_fs_result_analytic_center_gradient_contains <> [] ||
   hyp candle_fs_result_analytic_center_hessian_contains <> [] ||
   hyp candle_fs_result_analytic_proxy_shape <> [] ||
   hyp candle_fs_result_analytic_proxy_data_shape <> [] ||
   hyp candle_fs_result_analytic_box_regular <> [] ||
   hyp candle_fs_result_analytic_box_hessian_contains <> [] ||
   hyp candle_fs_result_neg_analytic_invariant <> [] ||
   hyp candle_fs_result_add_center_analytic_contains <> [] ||
   hyp candle_fs_result_add_box_hessian_contains <> [] ||
   hyp candle_fs_result_add_analytic_invariant <> [] then
  failwith "fixed-algebraic soundness substrate has assumptions";;

let candle_fixed_algebraic_sound_axioms_after = axioms ();;

if length candle_fixed_algebraic_sound_axioms_after <>
     length candle_fixed_algebraic_sound_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_fixed_algebraic_sound_axioms_before)
       candle_fixed_algebraic_sound_axioms_after) then
  failwith "fixed-algebraic soundness substrate changed axioms";;

print_endline
  "CANDLE_CV_FIXED_ALGEBRAIC_SOUND_OK DEVELOPMENT_NON_RELEASE";;
