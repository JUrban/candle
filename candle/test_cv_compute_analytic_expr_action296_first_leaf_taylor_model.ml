(* ========================================================================== *)
(* Two-cell centered-Taylor-model probe on the first genuine action-296 leaf. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This test establishes the numerical promise   *)
(* of the centered interpreter only.  The semantic bridge and final parent    *)
(* theorem are separate gates.                                                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_compute.ml";;
needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_point_certificate_prepare.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;

let candle_action296_taylor_model_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_taylor_model_find domain_th tree =
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      status,function_index,raw_flag,domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 Taylor model: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_taylor_model_find left_domain left
  | P_result_mono _ ->
      failwith "action296 Taylor model: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 Taylor model: unexpected reference node";;

let candle_action296_taylor_model_status,
    candle_action296_taylor_model_function_index,
    candle_action296_taylor_model_raw_flag,
    candle_action296_taylor_model_parent_domain =
  candle_action296_taylor_model_find
    candle_action296_taylor_model_root_domain
    candle_action296_plan_precision_tree;;

if candle_action296_taylor_model_function_index <> 0 ||
   candle_action296_taylor_model_raw_flag then
  failwith "action296 Taylor model: selected pass drift";;

let candle_action296_taylor_model_left_domain,
    candle_action296_taylor_model_right_domain =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_taylor_model_parent_domain;;

(* The exact checker authenticates these untrusted proposals.  The five      *)
(* coordinate intervals whose mathematical lower endpoint is 2 carry a      *)
(* small margin because the fixed-scale model rounds the input lower bound    *)
(* outward by at most one unit at scale 10^12.                                *)

let candle_action296_taylor_model_variable_sqrt_intervals =
 [`((((47,0),19),((241,0),99)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((2047,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((2047,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`];;

let candle_action296_taylor_model_box_sqrt_interval tm =
  let rec choose variables intervals =
    match variables,intervals with
    | variable :: variable_tail,interval :: interval_tail ->
        if aconv tm variable then interval
        else choose variable_tail interval_tail
    | [],[] ->
        `((((38,0),0),((80,0),0)):
          ((num#num)#num)#((num#num)#num))`
    | _ -> failwith "action296 Taylor model: sqrt interval shape" in
  choose candle_action296_plan_sqrt_variables
    candle_action296_taylor_model_variable_sqrt_intervals;;

let candle_action296_taylor_model_box_prepared =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_action296_taylor_model_box_sqrt_interval
    candle_action296_plan_prepared.function_term;;

let candle_action296_taylor_model_compute tm =
  candle_q_dim_analytic_jet_compute
    candle_cv_q_dim_taylor_model_compute_eqs tm;;

let candle_action296_taylor_model_dest_cexp_num tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then
    match arguments with
    | [value] -> dest_numeral value
    | _ -> failwith "action296 Taylor model: malformed cexp number"
  else failwith "action296 Taylor model: expected cexp number";;

let candle_action296_taylor_model_q_float value =
  let signed,denominator_predecessor =
    candle_q_dim_analytic_jet_dest_pair value in
  let positive_term,negative_term =
    candle_q_dim_analytic_jet_dest_pair signed in
  let positive =
    candle_action296_taylor_model_dest_cexp_num positive_term and
      negative =
        candle_action296_taylor_model_dest_cexp_num negative_term and
      denominator =
        Num.add_num
          (candle_action296_taylor_model_dest_cexp_num
            denominator_predecessor)
          (Num.num_of_int 1) in
  Num.float_of_num
    (Num.div_num (Num.sub_num positive negative) denominator);;

let rec candle_action296_taylor_model_dest_list value =
  let operator,arguments = strip_comb value in
  if aconv operator `Cexp_num` then []
  else if aconv operator `Cexp_pair` then
    match arguments with
    | [head;tail] ->
        head :: candle_action296_taylor_model_dest_list tail
    | _ -> failwith "action296 Taylor model: malformed list pair"
  else failwith "action296 Taylor model: expected reflected list";;

let candle_action296_taylor_model_check_domain label domain =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  let center_prepared =
    candle_q_dim_analytic_jet_prepare_point_six
      candle_action296_plan_prepared.function_term lower upper in
  let boxes =
    Candle_cv_polynomial_expr_flyspeck_fixture.candle_poly_fixture_q_boxes
      lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  let boxes_term = rand (concl boxes_representation) in
  print_endline
    ("CANDLE_CV_ACTION296_TAYLOR_MODEL_STAGE cell=" ^ label ^
     " event=compute_begin");
  let traced_result =
    rand
      (concl
        (candle_action296_taylor_model_compute
          (list_mk_comb
            (`candle_cv_q_dim_taylor_model_program_trace`,
             [center_prepared.program_representation_term;
              candle_action296_taylor_model_box_prepared.
                program_representation_term;
              boxes_term])))) in
  let program_result,domain_trace =
    candle_q_dim_analytic_jet_dest_pair traced_result in
  let compute_apply operator arguments =
    rand
      (concl
        (candle_action296_taylor_model_compute
          (list_mk_comb (operator,arguments)))) in
  let result =
    compute_apply `candle_cv_q_dim_taylor_model_finish`
      [boxes_term;program_result] in
  let accept,upper_q = candle_q_dim_analytic_jet_dest_pair result in
  let accept_num = candle_action296_taylor_model_dest_cexp_num accept and
      upper_float = candle_action296_taylor_model_q_float upper_q in
  let domain_bits =
    rev
      (map
        (fun entry ->
          let accumulated,_ =
            candle_q_dim_analytic_jet_dest_pair entry in
          candle_action296_taylor_model_dest_cexp_num accumulated)
        (candle_action296_taylor_model_dest_list domain_trace)) in
  let rec first_false index = function
    | [] -> -1
    | bit :: tail ->
        if Num.eq_num bit (Num.num_of_int 0) then index
        else first_false (index + 1) tail in
  let first_false_index = first_false 0 domain_bits in
  print_endline
    ("CANDLE_CV_ACTION296_TAYLOR_MODEL_RESULT cell=" ^ label ^
     " accept=" ^ Num.string_of_num accept_num ^
     " upper=" ^ string_of_float upper_float ^
     " actions=" ^ string_of_int (length domain_bits) ^
     " first_false_domain=" ^ string_of_int first_false_index);
  if not (Num.eq_num accept_num (Num.num_of_int 1)) ||
     not (Float.compare upper_float 0.0 = -1) ||
     first_false_index <> -1 then
    failwith
      ("action296 Taylor model: reflected child did not close: " ^ label);
  upper_float;;

let candle_action296_taylor_model_left_upper =
  candle_action296_taylor_model_check_domain "left"
    candle_action296_taylor_model_left_domain;;
let candle_action296_taylor_model_right_upper =
  candle_action296_taylor_model_check_domain "right"
    candle_action296_taylor_model_right_domain;;

print_endline
  ("CANDLE_CV_ACTION296_FIRST_LEAF_TAYLOR_MODEL_TWO_CELL_OK " ^
   "left_upper=" ^
   string_of_float candle_action296_taylor_model_left_upper ^
   " right_upper=" ^
   string_of_float candle_action296_taylor_model_right_upper ^
   " DEVELOPMENT_NON_RELEASE");;
