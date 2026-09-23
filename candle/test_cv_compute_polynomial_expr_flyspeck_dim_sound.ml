load_path :=
  ["/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6/formal_ineqs"] @
  !load_path;;

needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_dim_sound.ml";;

open Candle_cv_polynomial_expr_flyspeck_dim_sound;;

if hyp candle_q_box_lower_vector_component <> [] ||
   hyp candle_q_box_upper_vector_component <> [] ||
   hyp candle_q_box_center_vector_component <> [] ||
   hyp candle_q_box_radius_vector_component <> [] ||
   hyp candle_q_box_center_vector_list <> [] ||
   hyp candle_q_box_radius_vector_list <> [] ||
   hyp candle_q_radius_list_map <> [] ||
   hyp candle_q_radius_list_vector_component <> [] ||
   hyp candle_q_center_environment_vector_contains <> [] ||
   hyp candle_q_box_m_cell_domain <> [] ||
   hyp candle_q_box_stack_contains_vector <> [] ||
   hyp candle_poly_center_interval_contains <> [] ||
   hyp candle_itlist2_eq_sum <> [] ||
   hyp candle_q_dot_list_of_seq_sum <> [] ||
   hyp candle_q_weighted_rows_list_of_seq_sum <> [] ||
   hyp candle_poly_gradient_taylor_sum_bound <> [] ||
   hyp candle_poly_hessian_taylor_sum_bound <> [] ||
   hyp candle_poly_m_taylor_error_sound <> [] ||
   hyp candle_q_dim_whole_box_upper_real <> [] ||
   hyp candle_poly_dim_whole_box_accept_sound <> [] then
  failwith "dimension-generic Flyspeck box bridge assumptions mismatch";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_FLYSPECK_DIM_SOUND_OK";;
