needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_stable_batch_sound;;

let candle_fixed_outer_invariant_axioms_before = axioms ();;

if hyp candle_fs_result_analytic_proxy_target_components <> [] ||
   hyp candle_fs_result_mul_analytic_hessian_contains <> [] ||
   hyp candle_fs_analytic_hessian_flyspeck_contains <> [] ||
   hyp candle_fs_result_mul_analytic_box_hessian_contains <> [] ||
   hyp candle_fs_result_mul_analytic_center_contains <> [] ||
   hyp candle_fs_result_mul_analytic_center_shape <> [] ||
   hyp candle_fs_result_mul_analytic_invariant <> [] ||
   hyp candle_fs_result_square_analytic_invariant <> [] ||
   hyp candle_cv_fso_item_mul_correct <> [] ||
   hyp candle_cv_fso_item_square_correct <> [] ||
   hyp candle_fso_item_mul_analytic_invariant <> [] ||
   hyp candle_fso_item_square_analytic_invariant <> [] ||
   hyp candle_cv_fso_item_neg_correct <> [] ||
   hyp candle_cv_fso_item_add_correct <> [] ||
   hyp candle_cv_fso_logical_item_mul_correct <> [] ||
   hyp candle_cv_fso_logical_item_square_correct <> [] ||
   hyp candle_cv_fso_logical_program_step_correct <> [] ||
   hyp candle_cv_fso_logical_program_run_correct <> [] ||
   hyp candle_fso_logical_item_mul_analytic_invariant <> [] ||
   hyp candle_fso_logical_item_square_analytic_invariant <> [] ||
   hyp candle_fso_logical_program_step_poly <> [] ||
   hyp candle_fso_logical_program_step_sqrt <> [] ||
   hyp candle_fso_logical_program_step_neg <> [] ||
   hyp candle_fso_logical_program_step_add <> [] ||
   hyp candle_fso_logical_program_step_mul <> [] ||
   hyp candle_fso_logical_program_step_square <> [] ||
   hyp candle_fso_logical_program_step_inv <> [] ||
   hyp candle_fso_logical_program_step_atn <> [] ||
   hyp candle_fso_logical_program_step_pi_half <> [] ||
   hyp candle_fso_logical_program_run_append <> [] ||
   hyp candle_fso_logical_program_run_append_single <> [] ||
   hyp candle_fso_logical_program_run_append_binary <> [] ||
   hyp candle_fso_logical_compile_run_analytic_invariant <> [] ||
   hyp candle_cv_fso_program_correct <> [] ||
   hyp candle_q_dim_taylor_model_fixed_outer_compile_analytic_invariant <> [] ||
   hyp candle_cv_fso_certified_check_correct <> [] ||
   hyp candle_q_dim_taylor_model_fixed_outer_certified_upper_sound <> [] ||
   hyp candle_q_dim_taylor_model_fixed_outer_certified_accept_sound <> [] ||
   hyp candle_q_dim_taylor_model_fixed_outer_batch_accept_iff <> [] ||
   hyp candle_q_dim_taylor_model_fixed_outer_batch_accept_mem <> [] ||
   hyp candle_q_dim_taylor_model_fixed_outer_batch_sound <> [] ||
   hyp candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept <> [] ||
   hyp candle_q_dim_taylor_model_fixed_outer_stable_jobs_accept <> [] ||
   hyp candle_q_dim_taylor_model_fixed_outer_stable_batch_accept <> [] ||
   hyp candle_cv_fso_stable_jobs_check_correct <> [] ||
   hyp candle_cv_fso_stable_batch_check_correct <> [] then
  failwith "fixed outer invariant: unexpected theorem hypotheses";;

let candle_fixed_outer_invariant_axioms_after = axioms ();;

if length candle_fixed_outer_invariant_axioms_after <>
     length candle_fixed_outer_invariant_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_fixed_outer_invariant_axioms_before)
       candle_fixed_outer_invariant_axioms_after) then
  failwith "fixed outer invariant: axiom set changed";;

print_endline
  "CANDLE_CV_FIXED_OUTER_INVARIANT_OK DEVELOPMENT_NON_RELEASE";;
