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

let candle_dim_jet_source_shape_probe = prove
 (`!e boxes.
     candle_q_dim_jet_shape (LENGTH boxes)
       (candle_q_dim_poly_jet_normalized boxes e)`,
  REWRITE_TAC[candle_q_dim_poly_jet_normalized_shape]);;

let candle_dim_jet_source_soundness_probe = prove
 (`!e boxes env.
     candle_q_stack_contains boxes env
     ==> candle_q_dim_poly_jet_contains (LENGTH boxes)
           (candle_q_dim_poly_jet_normalized boxes e) env e`,
  REWRITE_TAC[candle_q_dim_poly_jet_normalized_sound]);;

let candle_dim_jet_computed_soundness_probe = prove
 (`!e boxes env.
     candle_q_stack_contains boxes env
     ==> ?jet.
           candle_cv_q_dim_jet_program
             (candle_cv_q_interval_list boxes)
             (candle_cv_q_instruction_list (candle_poly_compile e)) =
           candle_cv_q_dim_jet_encode jet /\
           candle_q_dim_poly_jet_contains (LENGTH boxes) jet env e`,
  REWRITE_TAC[candle_cv_q_dim_poly_compile_program_sound]);;

if hyp candle_dim_jet_normalized_interval_probe = [] &&
   hyp candle_dim_jet_source_program_probe = [] &&
   hyp candle_dim_jet_source_shape_probe = [] &&
   hyp candle_dim_jet_source_soundness_probe = [] &&
   hyp candle_dim_jet_computed_soundness_probe = [] then
  print_endline "CANDLE_CV_DIM_JET_SEMANTICS_OK"
else
  failwith "dimension-jet semantic bridge theorem has assumptions";;
