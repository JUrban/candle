(* ========================================================================== *)
(* Numerical bound comparison on the first genuine action-296 leaf.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This compares the components of the legacy    *)
(* theorem-producing Taylor bound with the current reflected split checker.  *)
(* It is diagnostic only and makes no release or certificate-completion claim. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_point_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_split_certificate_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_split_certificate_check;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_polynomial_expr_jet;;

let candle_action296_bound_compare_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_bound_compare_find domain_th tree =
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      status,function_index,raw_flag,domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 bound compare: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_bound_compare_find left_domain left
  | P_result_mono _ ->
      failwith "action296 bound compare: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 bound compare: unexpected reference node";;

let candle_action296_bound_compare_status,
    candle_action296_bound_compare_function_index,
    candle_action296_bound_compare_raw_flag,
    candle_action296_bound_compare_domain =
  candle_action296_bound_compare_find
    candle_action296_bound_compare_root_domain
    candle_action296_plan_precision_tree;;

if candle_action296_bound_compare_function_index <> 0 ||
   candle_action296_bound_compare_raw_flag then
  failwith "action296 bound compare: selected pass drift";;

let candle_action296_bound_compare_float_interval_abs pair =
  let lower,upper = dest_pair pair in
  let lower_abs =
    Float.abs (More_float.float_of_float_tm lower) and
      upper_abs =
        Float.abs (More_float.float_of_float_tm upper) in
  if Float.compare lower_abs upper_abs = -1 then upper_abs else lower_abs;;

let candle_action296_bound_compare_legacy_verifier =
  List.nth candle_action296_plan_formal_functions
    candle_action296_bound_compare_function_index;;

print_endline
  "CANDLE_CV_ACTION296_BOUND_COMPARE_STAGE lane=legacy event=begin";;
let candle_action296_bound_compare_legacy_taylor =
  candle_action296_bound_compare_legacy_verifier.taylor
    candle_action296_bound_compare_status.pp
    candle_action296_bound_compare_status.pp
    candle_action296_bound_compare_domain;;
let candle_action296_bound_compare_legacy_upper_theorem =
  M_taylor.eval_m_taylor_upper_bound
    candle_action296_plan_dimension
    candle_action296_bound_compare_status.pp
    candle_action296_bound_compare_legacy_taylor;;
print_endline
  "CANDLE_CV_ACTION296_BOUND_COMPARE_STAGE lane=legacy event=end";;

let _,_,_,candle_action296_bound_compare_legacy_radii_vector,
    candle_action296_bound_compare_legacy_value_interval,
    candle_action296_bound_compare_legacy_gradient_intervals,
    candle_action296_bound_compare_legacy_hessian_intervals =
  M_taylor.dest_m_taylor
    (concl candle_action296_bound_compare_legacy_taylor);;

let candle_action296_bound_compare_legacy_radii =
  map More_float.float_of_float_tm
    (dest_list (rand candle_action296_bound_compare_legacy_radii_vector));;
let candle_action296_bound_compare_legacy_value_upper =
  More_float.float_of_float_tm
    (snd (dest_pair candle_action296_bound_compare_legacy_value_interval));;
let candle_action296_bound_compare_legacy_gradient_upper =
  itlist2
    (fun radius interval total ->
      radius *.
        candle_action296_bound_compare_float_interval_abs interval +. total)
    candle_action296_bound_compare_legacy_radii
    (dest_list candle_action296_bound_compare_legacy_gradient_intervals)
    0.0;;

let candle_action296_bound_compare_legacy_hessian_rows =
  map dest_list
    (dest_list candle_action296_bound_compare_legacy_hessian_intervals);;
let candle_action296_bound_compare_legacy_hessian_row_contribution index row =
  let radius =
    List.nth candle_action296_bound_compare_legacy_radii index in
  let diagonal =
    candle_action296_bound_compare_float_interval_abs
      (List.nth row index) in
  let rec off_diagonal column subtotal =
    if column >= index then subtotal
    else
      off_diagonal (column + 1)
        (subtotal +.
         List.nth candle_action296_bound_compare_legacy_radii column *.
         candle_action296_bound_compare_float_interval_abs
           (List.nth row column)) in
  0.5 *. radius *. (radius *. diagonal +.
    2.0 *. off_diagonal 0 0.0);;
let candle_action296_bound_compare_legacy_hessian_row_contributions =
  let rec rows index remaining total =
    match remaining with
    | [] -> rev total
    | row :: tail ->
        rows (index + 1) tail
          (candle_action296_bound_compare_legacy_hessian_row_contribution
             index row :: total) in
  rows 0 candle_action296_bound_compare_legacy_hessian_rows [];;
let candle_action296_bound_compare_legacy_half_hessian_upper =
  itlist ( +. )
    candle_action296_bound_compare_legacy_hessian_row_contributions 0.0;;

let candle_action296_bound_compare_legacy_upper =
  let body = snd (dest_forall
    (concl candle_action296_bound_compare_legacy_upper_theorem)) in
  let _,consequent = dest_comb body in
  let _,upper = dest_comb consequent in
  More_float.float_of_float_tm upper;;

print_endline
  ("CANDLE_CV_ACTION296_BOUND_COMPARE_LEGACY value_upper=" ^
   string_of_float candle_action296_bound_compare_legacy_value_upper ^
   " gradient_upper=" ^
   string_of_float candle_action296_bound_compare_legacy_gradient_upper ^
   " half_hessian_upper=" ^
   string_of_float
     candle_action296_bound_compare_legacy_half_hessian_upper ^
   " final_upper=" ^
   string_of_float candle_action296_bound_compare_legacy_upper);;

let _ =
  let rec print_rows index = function
    | [] -> ()
    | contribution :: tail ->
        print_endline
          ("CANDLE_CV_ACTION296_BOUND_COMPARE_LEGACY_ROW index=" ^
           string_of_int index ^ " half_contribution=" ^
           string_of_float contribution);
        print_rows (index + 1) tail in
  print_rows 0
    candle_action296_bound_compare_legacy_hessian_row_contributions;;

let candle_action296_bound_compare_variable_sqrt_intervals =
 [`((((47,0),19),((241,0),99)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((2047,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((2047,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`];;

let candle_action296_bound_compare_box_sqrt_interval tm =
  let rec choose variables intervals =
    match variables,intervals with
    | variable :: variable_tail,interval :: interval_tail ->
        if aconv tm variable then interval
        else choose variable_tail interval_tail
    | [],[] ->
        `((((38,0),0),((80,0),0)):
          ((num#num)#num)#((num#num)#num))`
    | _ -> failwith "action296 bound compare: sqrt interval shape" in
  choose candle_action296_plan_sqrt_variables
    candle_action296_bound_compare_variable_sqrt_intervals;;

let candle_action296_bound_compare_box_prepared =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_action296_bound_compare_box_sqrt_interval
    candle_action296_plan_prepared.function_term;;

let candle_action296_bound_compare_domain_pair,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_bound_compare_domain);;
let candle_action296_bound_compare_actual_lower,
    candle_action296_bound_compare_actual_upper =
  dest_pair candle_action296_bound_compare_domain_pair;;
let candle_action296_bound_compare_lower,_ =
  candle_reflected_nl_normalize_vector
    candle_action296_bound_compare_actual_lower;;
let candle_action296_bound_compare_upper,_ =
  candle_reflected_nl_normalize_vector
    candle_action296_bound_compare_actual_upper;;
let candle_action296_bound_compare_center_prepared =
  candle_q_dim_analytic_jet_prepare_point_six
    candle_action296_plan_prepared.function_term
    candle_action296_bound_compare_lower
    candle_action296_bound_compare_upper;;
let candle_action296_bound_compare_boxes =
  Candle_cv_polynomial_expr_flyspeck_fixture.candle_poly_fixture_q_boxes
    candle_action296_bound_compare_lower
    candle_action296_bound_compare_upper;;
let candle_action296_bound_compare_boxes_representation =
  candle_q_dim_analytic_jet_boxes_encode_conv
    candle_action296_bound_compare_boxes;;
let candle_action296_bound_compare_boxes_term =
  rand (concl candle_action296_bound_compare_boxes_representation);;

let candle_action296_bound_compare_compute tm =
  candle_q_dim_analytic_jet_compute
    candle_cv_q_dim_analytic_split_certificate_compute_eqs tm;;

let candle_action296_bound_compare_dest_cexp_num tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then
    match arguments with
    | [value] -> dest_numeral value
    | _ -> failwith "action296 bound compare: malformed cexp number"
  else failwith "action296 bound compare: expected cexp number";;

let candle_action296_bound_compare_q_float value =
  let signed,denominator_predecessor =
    candle_q_dim_analytic_jet_dest_pair value in
  let positive_term,negative_term =
    candle_q_dim_analytic_jet_dest_pair signed in
  let positive =
    candle_action296_bound_compare_dest_cexp_num positive_term and
      negative =
        candle_action296_bound_compare_dest_cexp_num negative_term and
      denominator =
        Num.add_num
          (candle_action296_bound_compare_dest_cexp_num
            denominator_predecessor)
          (Num.num_of_int 1) in
  Num.float_of_num
    (Num.div_num (Num.sub_num positive negative) denominator);;

let rec candle_action296_bound_compare_dest_cexp_list tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_pair` then
    match arguments with
    | [head;tail] ->
        head :: candle_action296_bound_compare_dest_cexp_list tail
    | _ -> failwith "action296 bound compare: malformed cexp pair"
  else if aconv operator `Cexp_num` then []
  else failwith "action296 bound compare: malformed cexp list";;

let candle_action296_bound_compare_q_interval_abs interval =
  let lower,upper = candle_q_dim_analytic_jet_dest_pair interval in
  let lower_abs =
    Float.abs (candle_action296_bound_compare_q_float lower) and
      upper_abs =
        Float.abs (candle_action296_bound_compare_q_float upper) in
  if Float.compare lower_abs upper_abs = -1 then upper_abs else lower_abs;;

print_endline
  "CANDLE_CV_ACTION296_BOUND_COMPARE_STAGE lane=reflected event=begin";;
let candle_action296_bound_compare_center_environment =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (mk_comb
          (`candle_cv_q_center_environment_list`,
           candle_action296_bound_compare_boxes_term))));;
let candle_action296_bound_compare_center =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (list_mk_comb
          (`candle_cv_q_dim_analytic_first_program`,
           [candle_action296_bound_compare_center_environment;
            candle_action296_bound_compare_center_prepared.
              program_representation_term]))));;
let candle_action296_bound_compare_box =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (list_mk_comb
          (`candle_cv_q_dim_analytic_program`,
           [candle_action296_bound_compare_boxes_term;
            candle_action296_bound_compare_box_prepared.
              program_representation_term]))));;
let candle_action296_bound_compare_radii =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (mk_comb
          (`candle_cv_q_radius_list`,
           candle_action296_bound_compare_boxes_term))));;
let candle_action296_bound_compare_center_jet =
  mk_comb
    (`candle_cv_q_dim_analytic_first_result_jet`,
     candle_action296_bound_compare_center);;
let candle_action296_bound_compare_box_jet =
  mk_comb
    (`candle_cv_q_dim_analytic_result_jet`,
     candle_action296_bound_compare_box);;
let candle_action296_bound_compare_center_value =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (mk_comb
          (`Cexp_snd`,
           mk_comb
             (`candle_cv_q_dim_first_jet_f`,
              candle_action296_bound_compare_center_jet)))));;
let candle_action296_bound_compare_center_gradient =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (mk_comb
          (`candle_cv_q_dim_first_jet_gradient`,
           candle_action296_bound_compare_center_jet))));;
let candle_action296_bound_compare_box_hessian =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (mk_comb
          (`candle_cv_q_dim_jet_hessian`,
           candle_action296_bound_compare_box_jet))));;
let candle_action296_bound_compare_gradient_upper =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (list_mk_comb
          (`candle_cv_q_dot_abs_upper_extended`,
           [candle_action296_bound_compare_radii;
            candle_action296_bound_compare_center_gradient]))));;
let candle_action296_bound_compare_hessian_upper =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (list_mk_comb
          (`candle_cv_q_weighted_rows_abs_upper_extended`,
           [candle_action296_bound_compare_radii;
            candle_action296_bound_compare_radii;
            candle_action296_bound_compare_box_hessian]))));;
let candle_action296_bound_compare_half_hessian =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (list_mk_comb
          (`candle_cv_q_mul_normalized_extended`,
           [`candle_cv_q_half`;
            candle_action296_bound_compare_hessian_upper]))));;
let candle_action296_bound_compare_reflected_upper =
  rand
    (concl
      (candle_action296_bound_compare_compute
        (list_mk_comb
          (`candle_cv_q_dim_analytic_split_certificate_upper_pair`,
           [candle_action296_bound_compare_boxes_term;
            candle_action296_bound_compare_center;
            candle_action296_bound_compare_box]))));;
print_endline
  "CANDLE_CV_ACTION296_BOUND_COMPARE_STAGE lane=reflected event=end";;

let candle_action296_bound_compare_reflected_value_upper =
  candle_action296_bound_compare_q_float
    candle_action296_bound_compare_center_value;;
let candle_action296_bound_compare_reflected_gradient_upper =
  candle_action296_bound_compare_q_float
    candle_action296_bound_compare_gradient_upper;;
let candle_action296_bound_compare_reflected_half_hessian_upper =
  candle_action296_bound_compare_q_float
    candle_action296_bound_compare_half_hessian;;
let candle_action296_bound_compare_reflected_final_upper =
  candle_action296_bound_compare_q_float
    candle_action296_bound_compare_reflected_upper;;
let candle_action296_bound_compare_reflected_radii =
  map candle_action296_bound_compare_q_float
    (candle_action296_bound_compare_dest_cexp_list
      candle_action296_bound_compare_radii);;
let candle_action296_bound_compare_reflected_hessian_rows =
  map candle_action296_bound_compare_dest_cexp_list
    (candle_action296_bound_compare_dest_cexp_list
      candle_action296_bound_compare_box_hessian);;
let candle_action296_bound_compare_reflected_hessian_row_contributions =
  let rec rows index remaining result =
    match remaining with
    | [] -> rev result
    | row :: tail ->
        let radius =
          List.nth candle_action296_bound_compare_reflected_radii index in
        let dot =
          itlist2
            (fun column_radius interval total ->
              column_radius *.
                candle_action296_bound_compare_q_interval_abs interval +.
                total)
            candle_action296_bound_compare_reflected_radii row 0.0 in
        rows (index + 1) tail (0.5 *. radius *. dot :: result) in
  rows 0 candle_action296_bound_compare_reflected_hessian_rows [];;

print_endline
  ("CANDLE_CV_ACTION296_BOUND_COMPARE_REFLECTED value_upper=" ^
   string_of_float candle_action296_bound_compare_reflected_value_upper ^
   " gradient_upper=" ^
   string_of_float candle_action296_bound_compare_reflected_gradient_upper ^
   " half_hessian_upper=" ^
   string_of_float
     candle_action296_bound_compare_reflected_half_hessian_upper ^
   " final_upper=" ^
   string_of_float candle_action296_bound_compare_reflected_final_upper);;

let _ =
  let rec print_rows index = function
    | [] -> ()
    | contribution :: tail ->
        print_endline
          ("CANDLE_CV_ACTION296_BOUND_COMPARE_REFLECTED_ROW index=" ^
           string_of_int index ^ " half_contribution=" ^
           string_of_float contribution);
        print_rows (index + 1) tail in
  print_rows 0
    candle_action296_bound_compare_reflected_hessian_row_contributions;;

let _ =
  for row = 0 to 5 do
    for column = 0 to row do
      let legacy =
        candle_action296_bound_compare_float_interval_abs
          (List.nth
            (List.nth candle_action296_bound_compare_legacy_hessian_rows row)
            column) in
      let reflected =
        candle_action296_bound_compare_q_interval_abs
          (List.nth
            (List.nth
              candle_action296_bound_compare_reflected_hessian_rows row)
            column) in
      let ratio =
        if Float.compare legacy 0.0 = 0 then 0.0
        else reflected /. legacy in
      print_endline
        ("CANDLE_CV_ACTION296_BOUND_COMPARE_HESSIAN row=" ^
         string_of_int row ^ " column=" ^ string_of_int column ^
         " legacy_abs=" ^ string_of_float legacy ^
         " reflected_abs=" ^ string_of_float reflected ^
         " ratio=" ^ string_of_float ratio)
    done
  done;;

let rec candle_action296_bound_compare_sqrt_children expression =
  let operator,arguments = strip_comb expression in
  match fst (dest_const operator),arguments with
  | "Candle_analytic_poly",[_]
  | "Candle_analytic_pi_half",[] -> []
  | "Candle_analytic_neg",[child]
  | "Candle_analytic_square",[child]
  | "Candle_analytic_inv",[child]
  | "Candle_analytic_atn",[child] ->
      candle_action296_bound_compare_sqrt_children child
  | "Candle_analytic_add",[left;right]
  | "Candle_analytic_mul",[left;right] ->
      candle_action296_bound_compare_sqrt_children left @
      candle_action296_bound_compare_sqrt_children right
  | "Candle_analytic_sqrt",[lp;ln;ld;up;un;ud;child] ->
      child :: candle_action296_bound_compare_sqrt_children child
  | _ -> failwith "action296 bound compare: unexpected analytic AST";;

let candle_action296_bound_compare_sqrt_child_interval child =
  let compile_theorem =
    REWRITE_CONV
      [candle_analytic_compile_def;candle_poly_compile_def;APPEND]
      (mk_comb (`candle_analytic_compile`,child)) in
  let program_representation =
    candle_q_dim_analytic_jet_program_encode_conv
      (rand (concl compile_theorem)) in
  let result =
    rand
      (concl
        (candle_action296_bound_compare_compute
          (list_mk_comb
            (`candle_cv_q_dim_analytic_program`,
             [candle_action296_bound_compare_boxes_term;
              rand (concl program_representation)])))) in
  rand
    (concl
      (candle_action296_bound_compare_compute
        (mk_comb
          (`candle_cv_q_dim_jet_f`,
           mk_comb (`candle_cv_q_dim_analytic_result_jet`,result)))));;

let candle_action296_bound_compare_sqrt_child_intervals =
  map candle_action296_bound_compare_sqrt_child_interval
    (candle_action296_bound_compare_sqrt_children
      candle_action296_bound_compare_box_prepared.expression_term);;

let _ =
  let rec print_intervals index = function
    | [] -> ()
    | interval :: tail ->
        let lower,upper = candle_q_dim_analytic_jet_dest_pair interval in
        let lower_value = candle_action296_bound_compare_q_float lower and
            upper_value = candle_action296_bound_compare_q_float upper in
        print_endline
          ("CANDLE_CV_ACTION296_BOUND_COMPARE_SQRT_CHILD index=" ^
           string_of_int index ^ " lower=" ^ string_of_float lower_value ^
           " upper=" ^ string_of_float upper_value ^
           " sqrt_lower=" ^
           (if Float.compare lower_value 0.0 = -1 then "nan"
            else string_of_float (Float.sqrt lower_value)) ^
           " sqrt_upper=" ^
           (if Float.compare upper_value 0.0 = -1 then "nan"
            else string_of_float (Float.sqrt upper_value)));
        print_intervals (index + 1) tail in
  print_intervals 0 candle_action296_bound_compare_sqrt_child_intervals;;

if hyp candle_action296_bound_compare_legacy_taylor <> [] ||
   hyp candle_action296_bound_compare_legacy_upper_theorem <> [] ||
   Float.compare candle_action296_bound_compare_legacy_upper 0.0 <> -1 ||
   Float.compare candle_action296_bound_compare_reflected_final_upper 0.0 = -1 then
  failwith "action296 bound compare: expected numerical boundary drift";;

print_endline "CANDLE_CV_ACTION296_BOUND_COMPARE_OK";;
