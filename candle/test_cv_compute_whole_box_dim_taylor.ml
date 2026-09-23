needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_diff.ml";;
needs "candle/cv_compute_whole_box_dim_taylor.ml";;
needs "candle/cv_compute_exact_interval_reify.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_whole_box_dim_taylor;;

let candle_dim_taylor_expression =
 `Candle_poly_add
    (Candle_poly_add
      (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 5))
      (Candle_poly_square (Candle_poly_var 2)))
    (Candle_poly_const 0 1 0)`;;

let rec candle_dim_taylor_repeat_conv n conv =
  if n = 0 then ALL_CONV
  else conv THENC candle_dim_taylor_repeat_conv (n - 1) conv;;

let candle_dim_taylor_diff_conv =
  candle_dim_taylor_repeat_conv 16
   (SIMP_CONV[candle_poly_diff2_def; candle_poly_diff_def; ARITH]);;

let candle_dim_taylor_compile_conv =
  candle_dim_taylor_repeat_conv 16
   (SIMP_CONV[candle_poly_compile_def; APPEND]);;

let candle_dim_taylor_diff di =
  rand
   (concl
     (candle_dim_taylor_diff_conv
       (list_mk_comb
         (`candle_poly_diff`,
          [mk_small_numeral di;candle_dim_taylor_expression]))));;

let candle_dim_taylor_diff2 dj di =
  rand
   (concl
     (candle_dim_taylor_diff_conv
       (list_mk_comb
         (`candle_poly_diff2`,
          [mk_small_numeral dj;mk_small_numeral di;
           candle_dim_taylor_expression]))));;

let candle_dim_taylor_compile expression =
  rand
   (concl
     (candle_dim_taylor_compile_conv
       (mk_comb (`candle_poly_compile`,expression))));;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-dim-taylor scope=six-var phase=preparation event=begin";;

let candle_dim_taylor_pf =
  candle_dim_taylor_compile candle_dim_taylor_expression;;

let candle_dim_taylor_pds =
  map (fun di -> candle_dim_taylor_compile (candle_dim_taylor_diff di))
    (0--5);;

let candle_dim_taylor_pdds =
  map
   (fun di ->
      map
       (fun dj ->
          candle_dim_taylor_compile (candle_dim_taylor_diff2 dj di))
       (0--5))
   (0--5);;

let candle_dim_taylor_box =
 `((((0,0),0),((1,0),7)):
   ((num#num)#num)#((num#num)#num))`;;

let candle_dim_taylor_boxes =
  mk_list (replicate candle_dim_taylor_box 6,candle_q_interval_type);;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-dim-taylor scope=six-var phase=preparation event=end";;

let candle_dim_taylor_program_rep program =
  rand (concl (candle_q_program_encode_conv program));;

let candle_dim_taylor_interval_rep interval =
  rand
   (concl
     (REWRITE_CONV[candle_cv_q_interval_def; candle_cv_q_def;
                   candle_cv_lc_z_def]
       (mk_comb (`candle_cv_q_interval`,interval))));;

let candle_dim_taylor_cval_list elements =
  itlist
   (fun h t -> list_mk_comb (`Cexp_pair`,[h;t]))
   elements `Cexp_num 0`;;

let candle_dim_taylor_pf_rep =
  candle_dim_taylor_program_rep candle_dim_taylor_pf;;

let candle_dim_taylor_pds_rep =
  candle_dim_taylor_cval_list
    (map candle_dim_taylor_program_rep candle_dim_taylor_pds);;

let candle_dim_taylor_pdds_rep =
  candle_dim_taylor_cval_list
   (map
     (fun row ->
        candle_dim_taylor_cval_list
          (map candle_dim_taylor_program_rep row))
     candle_dim_taylor_pdds);;

let candle_dim_taylor_boxes_rep =
  candle_dim_taylor_cval_list
    (replicate (candle_dim_taylor_interval_rep candle_dim_taylor_box) 6);;

let candle_dim_taylor_compute_tm =
  list_mk_comb
   (`candle_cv_q_dim_whole_box_upper`,
    [candle_dim_taylor_pf_rep;candle_dim_taylor_pds_rep;
     candle_dim_taylor_pdds_rep;candle_dim_taylor_boxes_rep]);;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-dim-taylor scope=six-var phase=compute event=begin";;

let candle_dim_taylor_compute_th =
  compute candle_cv_q_dim_whole_box_compute_eqs
    candle_dim_taylor_compute_tm;;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-dim-taylor scope=six-var phase=compute event=end";;

let candle_dim_taylor_result = rand (concl candle_dim_taylor_compute_th);;

let candle_dim_taylor_dest_unary expected tm =
  let operator,argument = dest_comb tm in
  if aconv operator expected then argument
  else failwith "unexpected reflected unary constructor";;

let candle_dim_taylor_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "unexpected reflected pair constructor";;

let candle_dim_taylor_dest_num tm =
  dest_small_numeral (candle_dim_taylor_dest_unary `Cexp_num` tm);;

let candle_dim_taylor_result_z,candle_dim_taylor_result_d =
  candle_dim_taylor_dest_pair candle_dim_taylor_result;;
let candle_dim_taylor_result_p,candle_dim_taylor_result_n =
  candle_dim_taylor_dest_pair candle_dim_taylor_result_z;;

let candle_dim_taylor_result_parts =
  (candle_dim_taylor_dest_num candle_dim_taylor_result_p,
   candle_dim_taylor_dest_num candle_dim_taylor_result_n,
   1 + candle_dim_taylor_dest_num candle_dim_taylor_result_d);;

let candle_dim_taylor_p,candle_dim_taylor_n,candle_dim_taylor_d =
  candle_dim_taylor_result_parts;;

if candle_dim_taylor_p >= candle_dim_taylor_n
then failwith "dimension-parametric Taylor fixture is not negative";;

if hyp candle_dim_taylor_compute_th <> [] ||
   hyp candle_cv_q_dim_whole_box_upper_correct <> []
then failwith "dimension-parametric Taylor theorem assumptions mismatch";;

let candle_dim_taylor_program_count =
  1 + length candle_dim_taylor_pds +
  itlist (fun interval_program_row n ->
            length interval_program_row + n)
    candle_dim_taylor_pdds 0;;

let candle_dim_taylor_instruction_count =
  length (dest_list candle_dim_taylor_pf) +
  itlist (fun p n -> length (dest_list p) + n)
    candle_dim_taylor_pds 0 +
  itlist
    (fun interval_program_row n ->
       itlist (fun p m -> length (dest_list p) + m)
         interval_program_row 0 + n)
    candle_dim_taylor_pdds 0;;

if candle_dim_taylor_program_count <> 43 ||
   candle_dim_taylor_instruction_count <> 1298
then failwith "dimension-parametric Taylor program inventory mismatch";;

print_endline
 ("CANDLE_CV_WHOLE_BOX_DIM_TAYLOR programs=" ^
  string_of_int candle_dim_taylor_program_count ^
  " instructions=" ^
  string_of_int candle_dim_taylor_instruction_count);;

print_endline
 ("CANDLE_CV_WHOLE_BOX_DIM_TAYLOR upper=(" ^
  string_of_int candle_dim_taylor_p ^ "-" ^
  string_of_int candle_dim_taylor_n ^ ")/" ^
  string_of_int candle_dim_taylor_d);;

print_endline "CANDLE_CV_WHOLE_BOX_DIM_TAYLOR_OK";;
