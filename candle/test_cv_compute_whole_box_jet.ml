needs "candle/compute.ml";;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box-jet scope=cubic phase=library-setup event=begin";;

needs "candle/cv_compute_whole_box_jet.ml";;
needs "candle/cv_compute_exact_interval_reify.ml";;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box-jet scope=cubic phase=library-setup event=end";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_jet;;

let candle_whole_box_jet_variables = [`x:real`;`y:real`];;
let candle_whole_box_jet_expression = `x pow 3 + x * y pow 2 - &1`;;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box-jet scope=cubic phase=expression-setup event=begin";;

let candle_whole_box_jet_program,candle_whole_box_jet_program_th =
  candle_q_reify_real_expression
    candle_whole_box_jet_variables candle_whole_box_jet_expression;;

let candle_whole_box_jet_program_rep =
  candle_q_program_encode_conv candle_whole_box_jet_program;;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box-jet scope=cubic phase=expression-setup event=end";;

let candle_whole_box_jet_ix =
 `((((0,0),0),((1,0),3)):
   ((num#num)#num)#((num#num)#num))`;;
let candle_whole_box_jet_iy = candle_whole_box_jet_ix;;

let candle_whole_box_jet_interval_rep interval =
  REWRITE_CONV[candle_cv_q_interval_def; candle_cv_q_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_interval`,interval));;

let candle_whole_box_jet_ix_rep =
  candle_whole_box_jet_interval_rep candle_whole_box_jet_ix;;
let candle_whole_box_jet_iy_rep =
  candle_whole_box_jet_interval_rep candle_whole_box_jet_iy;;

let candle_whole_box_jet_compute_tm =
  list_mk_comb
    (`candle_cv_q_jet_whole_box_check`,
     [rand (concl candle_whole_box_jet_program_rep);
      rand (concl candle_whole_box_jet_ix_rep);
      rand (concl candle_whole_box_jet_iy_rep)]);;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box-jet scope=cubic phase=whole-box-compute event=begin";;

let candle_whole_box_jet_compute_th =
  compute candle_cv_q_jet_whole_box_compute_eqs
    candle_whole_box_jet_compute_tm;;

print_endline
 "CANDLE_CERT_PROFILE lane=nonlinear-whole-box-jet scope=cubic phase=whole-box-compute event=end";;

let candle_whole_box_jet_result = rand (concl candle_whole_box_jet_compute_th);;
let candle_whole_box_jet_verdict = rand (rator candle_whole_box_jet_result);;
let candle_whole_box_jet_upper = rand candle_whole_box_jet_result;;

if not (aconv candle_whole_box_jet_verdict `Cexp_num 1`)
then failwith "one-program whole-box jet checker rejected the cubic fixture";;

let candle_whole_box_jet_correctness_th =
  REWRITE_RULE
    [candle_whole_box_jet_program_rep;
     candle_whole_box_jet_ix_rep; candle_whole_box_jet_iy_rep;
     candle_whole_box_jet_compute_th]
    (SPECL
      [candle_whole_box_jet_program;
       candle_whole_box_jet_ix; candle_whole_box_jet_iy]
      candle_cv_q_jet_whole_box_check_correct);;

let candle_whole_box_jet_acceptance_goal =
  list_mk_comb
    (`candle_q_jet_whole_box_accept`,
     [candle_whole_box_jet_program;
      candle_whole_box_jet_ix; candle_whole_box_jet_iy]);;

let candle_whole_box_jet_acceptance_th = prove
 (candle_whole_box_jet_acceptance_goal,
  MP_TAC candle_whole_box_jet_correctness_th THEN
  REWRITE_TAC[injectivity "cval"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_whole_box_jet_dest_unary expected tm =
  let operator,argument = dest_comb tm in
  if aconv operator expected then argument
  else failwith "unexpected reflected unary constructor";;

let candle_whole_box_jet_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "unexpected reflected pair constructor";;

let candle_whole_box_jet_dest_num tm =
  dest_small_numeral (candle_whole_box_jet_dest_unary `Cexp_num` tm);;

let candle_whole_box_jet_upper_z,candle_whole_box_jet_upper_d =
  candle_whole_box_jet_dest_pair candle_whole_box_jet_upper;;
let candle_whole_box_jet_upper_p,candle_whole_box_jet_upper_n =
  candle_whole_box_jet_dest_pair candle_whole_box_jet_upper_z;;

let candle_whole_box_jet_upper_parts =
  (candle_whole_box_jet_dest_num candle_whole_box_jet_upper_p,
   candle_whole_box_jet_dest_num candle_whole_box_jet_upper_n,
   1 + candle_whole_box_jet_dest_num candle_whole_box_jet_upper_d);;

let candle_whole_box_jet_upper_pn,candle_whole_box_jet_upper_nn,
    candle_whole_box_jet_upper_den = candle_whole_box_jet_upper_parts;;

if 128 * (candle_whole_box_jet_upper_pn - candle_whole_box_jet_upper_nn) <>
   (-123) * candle_whole_box_jet_upper_den
then failwith "one-program whole-box jet upper bound mismatch";;

print_endline
  ("CANDLE_CV_WHOLE_BOX_JET program=" ^
   string_of_int (length (dest_list candle_whole_box_jet_program)) ^
   " upper=(" ^ string_of_int candle_whole_box_jet_upper_pn ^ "-" ^
   string_of_int candle_whole_box_jet_upper_nn ^ ")/" ^
   string_of_int candle_whole_box_jet_upper_den);;

if hyp candle_whole_box_jet_compute_th <> [] ||
   hyp candle_whole_box_jet_program_th <> [] ||
   hyp candle_cv_q_jet_whole_box_check_correct <> [] ||
   hyp candle_q_jet_program_contains <> [] ||
   hyp candle_whole_box_jet_acceptance_th <> []
then failwith "one-program whole-box jet theorem assumptions mismatch";;

print_endline "CANDLE_CV_WHOLE_BOX_JET_OK";;
