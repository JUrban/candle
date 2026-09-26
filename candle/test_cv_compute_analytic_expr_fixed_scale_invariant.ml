needs "candle/cv_compute_analytic_expr_fixed_scale_invariant.ml";;

open Candle_cv_analytic_expr_fixed_scale_invariant;;

if hyp candle_fs_dot_list_real_vector_sum <> [] ||
   hyp candle_fs_list_of_q_length <> [] ||
   hyp candle_fs_list_of_q_map <> [] ||
   hyp candle_fs_fixed_round_upper_real <> [] ||
   hyp candle_fs_rounded_list_map_real <> [] ||
   hyp candle_fs_rounded_list_real_vector <> [] ||
   hyp candle_fs_rounded_list_nonnegative <> [] ||
   hyp candle_fs_rounded_radii_m_cell_domain <> [] ||
   hyp candle_fs_interval_list_of_q_contains <> [] ||
   hyp candle_fs_center_environment_contains <> [] ||
   hyp candle_fs_dot_list_real_vector_sum_shifted <> [] ||
   hyp candle_fs_weighted_rows_list_real_vector_sum <> [] ||
   hyp candle_fs_complete_m_taylor_error_sound <> [] ||
   hyp candle_fs_complete_m_taylor_partial_error_sound <> [] ||
   hyp candle_fs_complete_gradient_error_sound <> [] ||
   hyp candle_m_bounded_on_int_contains <> [] ||
   hyp candle_fs_complete_value_bound_contains <> [] ||
   hyp candle_fs_complete_gradient_bound_contains <> [] ||
   hyp candle_fs_complete_gradient_bounds_contains <> [] ||
   hyp candle_fs_result_complete_proxy_contains <> [] ||
   hyp candle_q_dim_jet_components_gradient_contains <> [] ||
   hyp candle_q_dim_jet_components_hessian_contains <> [] ||
   hyp candle_fs_result_complete_poly_invariant <> [] ||
   hyp candle_fs_interval_zeros_length <> [] ||
   hyp candle_fs_interval_unit_length <> [] ||
   hyp candle_fs_interval_list_of_q_length <> [] ||
   hyp candle_fs_interval_lookup_contains <> [] ||
   hyp candle_fs_interval_zero_matrix_shape <> [] ||
   hyp candle_fs_interval_zero_matrix_rows_width <> [] ||
   hyp candle_fs_interval_zero_contains <> [] ||
   hyp candle_fs_interval_one_contains <> [] ||
   hyp candle_fs_interval_zeros_contains <> [] ||
   hyp candle_fs_interval_unit_contains <> [] ||
   hyp candle_fs_interval_zero_matrix_contains <> [] ||
   hyp candle_fs_result_constant_poly_invariant <> [] ||
   hyp candle_fs_result_variable_poly_invariant <> [] ||
   hyp candle_fs_center_dimensions_length <> [] ||
   hyp candle_fs_result_constant_center_poly_invariant <> [] ||
   hyp candle_fs_result_variable_center_poly_invariant <> [] ||
   hyp candle_fs_result_poly_center_shape <> [] ||
   hyp candle_fs_result_poly_center_components <> [] ||
   hyp candle_fs_result_poly_center_value_contains <> [] ||
   hyp candle_fs_result_poly_center_gradient_contains <> [] ||
   hyp candle_fs_result_poly_center_hessian_contains <> [] ||
   hyp candle_fs_result_poly_proxy_shape <> [] ||
   hyp candle_fs_result_poly_proxy_components <> [] ||
   hyp candle_fs_result_poly_box_hessian_contains <> [] ||
   hyp candle_fs_interval_to_q_neg <> [] ||
   hyp candle_fs_interval_list_to_q_neg <> [] ||
   hyp candle_fs_interval_matrix_to_q_neg <> [] ||
   hyp candle_fs_first_to_q_neg <> [] ||
   hyp candle_fs_interval_list_neg_contains <> [] ||
   hyp candle_fs_interval_matrix_neg_contains <> [] ||
   hyp candle_poly_denote_dim_neg_partial <> [] ||
   hyp candle_poly_denote_dim_neg_partial2 <> [] ||
   hyp candle_q_dim_jet_components_neg_sound <> [] ||
   hyp candle_map_neg_matrix_list_of_seq <> [] ||
   hyp candle_fs_result_neg_poly_invariant <> [] ||
   hyp candle_fs_first_components_from_data <> [] ||
   hyp candle_fs_interval_list_add_length <> [] ||
   hyp candle_fs_interval_matrix_add_length <> [] ||
   hyp candle_fs_interval_matrix_add_rows_width <> [] ||
   hyp candle_fs_interval_list_add_contains <> [] ||
   hyp candle_fs_interval_matrix_add_contains <> [] ||
   hyp candle_map2_list_of_seq <> [] ||
   hyp candle_map2_matrix_list_of_seq <> [] ||
   hyp candle_fs_first_add_shape <> [] ||
   hyp candle_fs_first_add_components <> [] ||
   hyp candle_poly_denote_dim_add_partial <> [] ||
   hyp candle_poly_denote_dim_add_partial2 <> [] ||
   hyp candle_fs_gradient_bounds_el <> [] ||
   hyp candle_fs_result_complete_domain <> [] ||
   hyp candle_fs_result_complete_proxy <> [] then
  failwith "fixed-scale invariant structural test has assumptions";;

print_endline "CANDLE_CV_FIXED_SCALE_INVARIANT_OK";;
