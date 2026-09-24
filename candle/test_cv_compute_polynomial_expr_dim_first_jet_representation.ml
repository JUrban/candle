needs "candle/cv_compute_polynomial_expr_dim_first_jet_representation.ml";;

open Candle_cv_polynomial_expr_dim_first_jet_representation;;

let candle_dim_first_jet_representation_probe = prove
 (`!program boxes.
     candle_cv_q_dim_first_jet_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program) =
     candle_cv_q_dim_jet_first_projection
       (candle_cv_q_dim_jet_program
         (candle_cv_q_interval_list boxes)
         (candle_cv_q_instruction_list program))`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_program_projection]);;

if hyp candle_dim_first_jet_representation_probe = [] then
  print_endline "CANDLE_CV_DIM_FIRST_JET_REPRESENTATION_OK"
else
  failwith "dimension first-jet representation theorem has assumptions";;
