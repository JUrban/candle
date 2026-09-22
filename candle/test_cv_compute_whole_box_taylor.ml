needs "candle/compute.ml";;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box scope=cubic phase=library-setup event=begin";;

needs "candle/cv_compute_whole_box_taylor.ml";;
needs "candle/cv_compute_exact_interval_reify.ml";;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box scope=cubic phase=library-setup event=end";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_whole_box_taylor;;

let candle_whole_box_variables = [`x:real`;`y:real`];;

(* A cubic with a genuinely box-varying Hessian. *)
let candle_whole_box_f = `x pow 3 + x * y pow 2 - &1`;;
let candle_whole_box_fx = `&3 * x pow 2 + y pow 2`;;
let candle_whole_box_fy = `&2 * x * y`;;
let candle_whole_box_fxx = `&6 * x`;;
let candle_whole_box_fxy = `&2 * y`;;
let candle_whole_box_fyy = `&2 * x`;;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box scope=cubic phase=expression-setup event=begin";;

let candle_whole_box_pf,candle_whole_box_pf_th =
  candle_q_reify_real_expression candle_whole_box_variables candle_whole_box_f;;
let candle_whole_box_pfx,candle_whole_box_pfx_th =
  candle_q_reify_real_expression candle_whole_box_variables candle_whole_box_fx;;
let candle_whole_box_pfy,candle_whole_box_pfy_th =
  candle_q_reify_real_expression candle_whole_box_variables candle_whole_box_fy;;
let candle_whole_box_pfxx,candle_whole_box_pfxx_th =
  candle_q_reify_real_expression candle_whole_box_variables candle_whole_box_fxx;;
let candle_whole_box_pfxy,candle_whole_box_pfxy_th =
  candle_q_reify_real_expression candle_whole_box_variables candle_whole_box_fxy;;
let candle_whole_box_pfyy,candle_whole_box_pfyy_th =
  candle_q_reify_real_expression candle_whole_box_variables candle_whole_box_fyy;;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box scope=cubic phase=expression-setup event=end";;

let candle_whole_box_ix =
 `((((0,0),0),((1,0),3)):
   ((num#num)#num)#((num#num)#num))`;;
let candle_whole_box_iy = candle_whole_box_ix;;

let candle_whole_box_program_rep program =
  candle_q_program_encode_conv program;;

let candle_whole_box_interval_rep interval =
  REWRITE_CONV[candle_cv_q_interval_def; candle_cv_q_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_interval`,interval));;

let candle_whole_box_program_reps =
  map candle_whole_box_program_rep
    [candle_whole_box_pf;candle_whole_box_pfx;candle_whole_box_pfy;
     candle_whole_box_pfxx;candle_whole_box_pfxy;candle_whole_box_pfyy];;

let candle_whole_box_ix_rep = candle_whole_box_interval_rep candle_whole_box_ix;;
let candle_whole_box_iy_rep = candle_whole_box_interval_rep candle_whole_box_iy;;

let candle_whole_box_compute_tm =
  list_mk_comb
    (`candle_cv_q_whole_box_check`,
     map (fun th -> rand (concl th)) candle_whole_box_program_reps @
     [rand (concl candle_whole_box_ix_rep);
      rand (concl candle_whole_box_iy_rep)]);;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box scope=cubic phase=whole-box-compute event=begin";;

let candle_whole_box_compute_th =
  compute candle_cv_q_whole_box_compute_eqs candle_whole_box_compute_tm;;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box scope=cubic phase=whole-box-compute event=end";;

let candle_whole_box_result = rand (concl candle_whole_box_compute_th);;
let candle_whole_box_verdict = rand (rator candle_whole_box_result);;
let candle_whole_box_upper = rand candle_whole_box_result;;

let candle_whole_box_dest_unary expected tm =
  let operator,argument = dest_comb tm in
  if aconv operator expected then argument
  else failwith "unexpected reflected unary constructor";;

let candle_whole_box_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "unexpected reflected pair constructor";;

let candle_whole_box_dest_num tm =
  dest_small_numeral (candle_whole_box_dest_unary `Cexp_num` tm);;

let candle_whole_box_upper_z,candle_whole_box_upper_d =
  candle_whole_box_dest_pair candle_whole_box_upper;;
let candle_whole_box_upper_p,candle_whole_box_upper_n =
  candle_whole_box_dest_pair candle_whole_box_upper_z;;
let candle_whole_box_upper_parts =
  (candle_whole_box_dest_num candle_whole_box_upper_p,
   candle_whole_box_dest_num candle_whole_box_upper_n,
   1 + candle_whole_box_dest_num candle_whole_box_upper_d);;

if not (aconv candle_whole_box_verdict `Cexp_num 1`)
then failwith "whole-box Taylor checker rejected the cubic fixture";;

let candle_whole_box_program_lengths =
  map (fun p -> length (dest_list p))
    [candle_whole_box_pf;candle_whole_box_pfx;candle_whole_box_pfy;
     candle_whole_box_pfxx;candle_whole_box_pfxy;candle_whole_box_pfyy];;

print_endline
  ("CANDLE_CV_WHOLE_BOX_TAYLOR programs=" ^
   String.concat "," (map string_of_int candle_whole_box_program_lengths));;

let candle_whole_box_upper_pn,candle_whole_box_upper_nn,
    candle_whole_box_upper_den = candle_whole_box_upper_parts;;

print_endline
  ("CANDLE_CV_WHOLE_BOX_TAYLOR upper=(" ^
   string_of_int candle_whole_box_upper_pn ^ "-" ^
   string_of_int candle_whole_box_upper_nn ^ ")/" ^
   string_of_int candle_whole_box_upper_den);;

if hyp candle_whole_box_compute_th <> [] ||
   hyp candle_cv_q_whole_box_check_correct <> [] ||
   hyp candle_q_abs_upper_sound <> [] ||
   exists (fun th -> hyp th <> [])
     [candle_whole_box_pf_th;candle_whole_box_pfx_th;
      candle_whole_box_pfy_th;candle_whole_box_pfxx_th;
      candle_whole_box_pfxy_th;candle_whole_box_pfyy_th]
then failwith "whole-box Taylor theorem assumptions mismatch";;

print_endline "CANDLE_CV_WHOLE_BOX_TAYLOR_OK";;
