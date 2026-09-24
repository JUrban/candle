needs "candle/cv_compute_polynomial_expr_dim_jet_semantics.ml";;

open Candle_cv_polynomial_expr_dim_jet_semantics;;

let candle_dim_jet_normalized_interval_probe = prove
 (`!i x.
     candle_q_interval_contains (candle_q_interval_normalize i) x <=>
     candle_q_interval_contains i x`,
  REWRITE_TAC[candle_q_interval_normalize_contains]);;

let candle_dim_jet_source_program_probe = prove
 (`!e boxes.
     candle_cv_q_dim_jet_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list (candle_poly_compile e)) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_poly_jet_normalized boxes e)`,
  REWRITE_TAC[candle_cv_q_dim_poly_compile_program_correct]);;

if hyp candle_dim_jet_normalized_interval_probe = [] &&
   hyp candle_dim_jet_source_program_probe = [] then
  print_endline "CANDLE_CV_DIM_JET_SEMANTICS_OK"
else
  failwith "dimension-jet semantic bridge theorem has assumptions";;
