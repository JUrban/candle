needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_compute.ml";;

open Candle_cv_polynomial_expr_dim_jet_compute;;

let candle_dim_jet_compute_program =
  `Cexp_pair
     (Cexp_pair (Cexp_num 1) (Cexp_num 0))
     (Cexp_pair
       (Cexp_pair (Cexp_num 1) (Cexp_num 1))
       (Cexp_pair (Cexp_num 4) (Cexp_num 0)))`;;

let candle_dim_jet_compute_qzero =
  `Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0)`;;

let candle_dim_jet_compute_qone =
  `Cexp_pair (Cexp_pair (Cexp_num 1) (Cexp_num 0)) (Cexp_num 0)`;;

let candle_dim_jet_compute_interval =
  list_mk_comb
    (`Cexp_pair`,[candle_dim_jet_compute_qzero;candle_dim_jet_compute_qone]);;

let candle_dim_jet_compute_boxes =
  list_mk_comb
    (`Cexp_pair`,
     [candle_dim_jet_compute_interval;
      list_mk_comb
       (`Cexp_pair`,[candle_dim_jet_compute_interval;`Cexp_num 0`])]);;

let candle_dim_jet_compute_smoke =
  compute candle_cv_q_dim_jet_compute_eqs
    (list_mk_comb
      (`candle_cv_q_dim_jet_whole_box_check`,
       [candle_dim_jet_compute_program;candle_dim_jet_compute_boxes]));;

if hyp candle_dim_jet_compute_smoke <> [] then
  failwith "dimension-generic reflected jet smoke theorem has assumptions";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_DIM_JET_COMPUTE_OK";;
