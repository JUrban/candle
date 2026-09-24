needs "candle/cv_compute_polynomial_expr_dim_jet_check.ml";;

open Candle_cv_polynomial_expr_dim_jet_check;;

let candle_dim_jet_whole_box_compute_probe = prove
 (`!e boxes.
     candle_cv_q_dim_poly_jet_whole_box_upper
       (candle_cv_q_instruction_list (candle_poly_compile e))
       (candle_cv_q_interval_list boxes) =
     candle_cv_q (candle_q_dim_poly_jet_whole_box_upper e boxes)`,
  REWRITE_TAC[candle_cv_q_dim_poly_jet_whole_box_upper_correct]);;

let candle_dim_jet_whole_box_sound_data_probe = prove
 (`!e boxes.
     ?jet.
       candle_cv_q_dim_poly_jet_whole_box_upper
         (candle_cv_q_instruction_list (candle_poly_compile e))
         (candle_cv_q_interval_list boxes) =
       candle_cv_q (candle_q_dim_jet_taylor_upper boxes jet) /\
       candle_q_dim_poly_jet_contains (LENGTH boxes) jet
         (MAP (\i. candle_q_real (candle_q_midpoint i)) boxes) e`,
  REWRITE_TAC[candle_cv_q_dim_poly_jet_whole_box_upper_sound_data]);;

if hyp candle_dim_jet_whole_box_compute_probe = [] &&
   hyp candle_dim_jet_whole_box_sound_data_probe = [] then
  print_endline "CANDLE_CV_DIM_JET_WHOLE_BOX_CHECK_OK"
else
  failwith "dimension-jet whole-box theorem has assumptions";;
