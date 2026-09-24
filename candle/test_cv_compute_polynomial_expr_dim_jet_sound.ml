needs "candle/cv_compute_polynomial_expr_dim_jet_sound.ml";;

open Candle_cv_polynomial_expr_dim_jet_sound;;

let candle_dim_jet_analytic_sound_probe = prove
 (`!e boxes.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     !p. p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_poly_denote_dim e (p:real^N) <=
       candle_q_real (candle_q_dim_poly_jet_whole_box_upper e boxes)`,
  REWRITE_TAC[candle_q_dim_poly_jet_whole_box_upper_sound]);;

if hyp candle_dim_jet_analytic_sound_probe = [] then
  print_endline "CANDLE_CV_DIM_JET_ANALYTIC_SOUND_OK"
else
  failwith "dimension-jet analytic theorem has assumptions";;
