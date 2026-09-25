(* ========================================================================== *)
(* Normalized Taylor-accumulator probe on the first action-296 leaf.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is a numerical diagnostic only.  It does *)
(* not perform the theorem handoff or count as a proved certificate leaf.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_exact_rational_normalize_extended.ml";;

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_first_center_check;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_exact_rational_normalize_extended;;

let candle_action296_probe_variable_sqrt_intervals =
 [`((((589,0),249),((2399,0),999)):
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

let candle_action296_probe_center_sqrt_intervals =
 [`((((2377,0),999),((1189,0),499)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2023,0),999),((253,0),124)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2023,0),999),((253,0),124)):
     ((num#num)#num)#((num#num)#num))`;
  `((((254,0),124),((2033,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((254,0),124),((2033,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((254,0),124),((2033,0),999)):
     ((num#num)#num)#((num#num)#num))`];;

let candle_action296_probe_choose_sqrt_interval fallback intervals tm =
  let rec find variables candidates =
    match variables,candidates with
    | variable :: variable_tail,interval :: interval_tail ->
        if aconv tm variable then interval
        else find variable_tail interval_tail
    | [],[] -> fallback
    | _ -> failwith "action296 normalized probe: sqrt interval shape" in
  find candle_action296_plan_sqrt_variables intervals;;

let candle_action296_probe_sqrt_interval tm =
  candle_action296_probe_choose_sqrt_interval
    `((((56,0),0),((63,0),0)):
      ((num#num)#num)#((num#num)#num))`
    candle_action296_probe_variable_sqrt_intervals tm;;

let candle_action296_probe_center_sqrt_interval tm =
  candle_action296_probe_choose_sqrt_interval
    `((((593,0),9),((297,0),4)):
      ((num#num)#num)#((num#num)#num))`
    candle_action296_probe_center_sqrt_intervals tm;;

let candle_action296_probe_prepared =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_action296_probe_sqrt_interval
    candle_action296_plan_prepared.function_term;;

let candle_action296_probe_center_prepared =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_action296_probe_center_sqrt_interval
    candle_action296_plan_prepared.function_term;;

let candle_action296_probe_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_probe_first_leaf domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      function_index,raw_flag,domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 normalized probe: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_probe_first_leaf left_domain left
  | P_result_mono _ ->
      failwith "action296 normalized probe: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 normalized probe: unexpected reference node";;

let candle_action296_probe_function_index,
    candle_action296_probe_raw,
    candle_action296_probe_domain =
  candle_action296_probe_first_leaf candle_action296_probe_root_domain
    candle_action296_plan_precision_tree;;

if candle_action296_probe_function_index <> 0 ||
   candle_action296_probe_raw then
  failwith "action296 normalized probe: unexpected pass selection";;

let candle_action296_probe_domain_pair,_,_ =
  M_taylor.dest_m_cell_domain (concl candle_action296_probe_domain);;
let candle_action296_probe_actual_lower,
    candle_action296_probe_actual_upper =
  dest_pair candle_action296_probe_domain_pair;;
let candle_action296_probe_lower,_ =
  candle_reflected_nl_normalize_vector candle_action296_probe_actual_lower;;
let candle_action296_probe_upper,_ =
  candle_reflected_nl_normalize_vector candle_action296_probe_actual_upper;;
let candle_action296_probe_boxes =
  Candle_cv_polynomial_expr_flyspeck_fixture.candle_poly_fixture_q_boxes
    candle_action296_probe_lower candle_action296_probe_upper;;
let candle_action296_probe_boxes_representation =
  candle_q_dim_analytic_jet_boxes_encode_conv
    candle_action296_probe_boxes;;
let candle_action296_probe_boxes_term =
  rand (concl candle_action296_probe_boxes_representation);;

let candle_action296_probe_compute stage tm =
  print_endline
    ("CANDLE_CV_ACTION296_NORMALIZED_PROBE_STAGE event=" ^ stage ^
     "-begin");
  let theorem =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_extended_normalized_compute_eqs @
       candle_cv_q_dim_analytic_first_center_compute_eqs) tm in
  print_endline
    ("CANDLE_CV_ACTION296_NORMALIZED_PROBE_STAGE event=" ^ stage ^
     "-end");
  theorem;;

let rec candle_action296_probe_dest_cexp_list tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_pair` then
    match arguments with
    | [head;tail] ->
        head :: candle_action296_probe_dest_cexp_list tail
    | _ -> failwith "action296 normalized probe: malformed cexp pair"
  else if aconv operator `Cexp_num` then []
  else failwith "action296 normalized probe: malformed cexp list";;

let candle_action296_probe_dest_cexp_pair tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_pair` then
    match arguments with
    | [left;right] -> left,right
    | _ -> failwith "action296 normalized probe: malformed cexp pair"
  else failwith "action296 normalized probe: expected cexp pair";;

let candle_action296_probe_dest_cexp_num tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then
    match arguments with
    | [value] -> dest_numeral value
    | _ -> failwith "action296 normalized probe: malformed cexp num"
  else failwith "action296 normalized probe: expected cexp num";;

let candle_action296_probe_num_bits value =
  let zero = Num.num_of_int 0 and two = Num.num_of_int 2 in
  let rec loop n bits =
    if Num.eq_num n zero then bits
    else loop (Num.quo_num n two) (bits + 1) in
  loop value 0;;

let candle_action296_probe_gcd_profile numerator denominator =
  let zero = Num.num_of_int 0 in
  let rec loop steps a b =
    if Num.eq_num b zero then steps,a
    else loop (steps + 1) b (Num.mod_num a b) in
  loop 0 numerator denominator;;

let candle_action296_probe_rational_profile label value =
  let z,denominator_predecessor =
    candle_action296_probe_dest_cexp_pair value in
  let positive_term,negative_term =
    candle_action296_probe_dest_cexp_pair z in
  let positive = candle_action296_probe_dest_cexp_num positive_term and
      negative = candle_action296_probe_dest_cexp_num negative_term and
      denominator =
        Num.add_num
          (candle_action296_probe_dest_cexp_num denominator_predecessor)
          (Num.num_of_int 1) in
  let normalized_numerator =
    if Num.ge_num positive negative then Num.sub_num positive negative
    else Num.sub_num negative positive in
  let gcd_steps,gcd =
    candle_action296_probe_gcd_profile normalized_numerator denominator in
  let signed_numerator = Num.sub_num positive negative in
  let approximate =
    Num.float_of_num (Num.div_num signed_numerator denominator) in
  print_endline
    ("CANDLE_CV_ACTION296_NORMALIZED_PROBE_RATIONAL label=" ^ label ^
     " positive_bits=" ^
       string_of_int (candle_action296_probe_num_bits positive) ^
     " negative_bits=" ^
       string_of_int (candle_action296_probe_num_bits negative) ^
     " normalized_numerator_bits=" ^
       string_of_int (candle_action296_probe_num_bits normalized_numerator) ^
     " denominator_bits=" ^
       string_of_int (candle_action296_probe_num_bits denominator) ^
     " gcd_steps=" ^ string_of_int gcd_steps ^
     " gcd_bits=" ^
       string_of_int (candle_action296_probe_num_bits gcd) ^
     " approximate=" ^ string_of_float approximate);;

let candle_action296_probe_verdict,
    candle_action296_probe_upper_chars =
  let center_environment_theorem =
    candle_action296_probe_compute "center-environment"
      (mk_comb
        (`candle_cv_q_center_environment_list`,
         candle_action296_probe_boxes_term)) in
  let center_environment = rand (concl center_environment_theorem) in
  let center_theorem =
    candle_action296_probe_compute "center-jet"
      (list_mk_comb
         (`candle_cv_q_dim_analytic_first_program`,
         [center_environment;
          candle_action296_probe_center_prepared.program_representation_term])) in
  let center = rand (concl center_theorem) in
  let box_theorem =
    candle_action296_probe_compute "box-jet"
      (list_mk_comb
         (`candle_cv_q_dim_analytic_program`,
         [candle_action296_probe_boxes_term;
          candle_action296_probe_prepared.program_representation_term])) in
  let box = rand (concl box_theorem) in
  let domain_theorem =
    candle_action296_probe_compute "domain"
      (list_mk_comb
        (`candle_cv_bool_and`,
         [mk_comb
           (`candle_cv_q_dim_analytic_first_result_domain`,center);
          mk_comb (`candle_cv_q_dim_analytic_result_domain`,box)])) in
  let domain_value = rand (concl domain_theorem) in
  let valid_theorem =
    candle_action296_probe_compute "box-validity"
      (mk_comb
        (`candle_cv_q_box_valid_list`,candle_action296_probe_boxes_term)) in
  let valid = rand (concl valid_theorem) in
  let center_jet =
    mk_comb (`candle_cv_q_dim_analytic_first_result_jet`,center) in
  let box_jet =
    mk_comb (`candle_cv_q_dim_analytic_result_jet`,box) in
  let radii_theorem =
    candle_action296_probe_compute "radii"
      (mk_comb
        (`candle_cv_q_radius_list`,candle_action296_probe_boxes_term)) in
  let radii = rand (concl radii_theorem) in
  let center_value_theorem =
    candle_action296_probe_compute "center-value-upper"
      (mk_comb
        (`Cexp_snd`,mk_comb (`candle_cv_q_dim_first_jet_f`,center_jet))) in
  let center_value = rand (concl center_value_theorem) in
  candle_action296_probe_rational_profile "center-value-upper" center_value;
  let center_gradient_theorem =
    candle_action296_probe_compute "center-gradient"
      (mk_comb (`candle_cv_q_dim_first_jet_gradient`,center_jet)) in
  let center_gradient = rand (concl center_gradient_theorem) in
  let box_hessian_theorem =
    candle_action296_probe_compute "box-hessian"
      (mk_comb (`candle_cv_q_dim_jet_hessian`,box_jet)) in
  let box_hessian = rand (concl box_hessian_theorem) in
  let gradient_upper_theorem =
    candle_action296_probe_compute "gradient-upper"
      (list_mk_comb
        (`candle_cv_q_dot_abs_upper_normalized`,
         [radii;center_gradient])) in
  let gradient_upper = rand (concl gradient_upper_theorem) in
  candle_action296_probe_rational_profile "gradient-upper" gradient_upper;
  let radius_values = candle_action296_probe_dest_cexp_list radii in
  let hessian_rows =
    candle_action296_probe_dest_cexp_list box_hessian in
  let compute_weighted_row index weight row =
    let label = "hessian-row-" ^ string_of_int index in
    let dot_theorem =
      candle_action296_probe_compute (label ^ "-dot")
        (list_mk_comb
          (`candle_cv_q_dot_abs_upper_normalized`,[radii;row])) in
    let dot = rand (concl dot_theorem) in
    let scaled_theorem =
      candle_action296_probe_compute (label ^ "-scale")
        (list_mk_comb
          (`candle_cv_q_mul_normalized_extended`,[weight;dot])) in
    rand (concl scaled_theorem) in
  let rec accumulate_rows index weights rows accumulator =
    match weights,rows with
    | [],[] -> accumulator
    | weight :: weight_tail,row :: row_tail ->
        let scaled = compute_weighted_row index weight row in
        candle_action296_probe_rational_profile
          ("hessian-row-" ^ string_of_int index ^ "-scaled") scaled;
        candle_action296_probe_rational_profile
          ("hessian-row-" ^ string_of_int index ^ "-accumulator")
          accumulator;
        let raw_sum_theorem =
          candle_action296_probe_compute
            ("hessian-row-" ^ string_of_int index ^ "-raw-sum")
            (list_mk_comb (`candle_cv_q_add`,[scaled;accumulator])) in
        let raw_sum = rand (concl raw_sum_theorem) in
        candle_action296_probe_rational_profile
          ("hessian-row-" ^ string_of_int index ^ "-raw-sum") raw_sum;
        let sum_theorem =
          candle_action296_probe_compute
            ("hessian-row-" ^ string_of_int index ^ "-sum")
            (list_mk_comb
              (`candle_cv_q_add_normalized_extended`,[scaled;accumulator])) in
        accumulate_rows (index + 1) weight_tail row_tail
          (rand (concl sum_theorem))
    | _ -> failwith "action296 normalized probe: Hessian shape mismatch" in
  let hessian_upper =
    match radius_values,hessian_rows with
    | first_weight :: weight_tail,first_row :: row_tail ->
        accumulate_rows 1 weight_tail row_tail
          (compute_weighted_row 0 first_weight first_row)
    | _ -> failwith "action296 normalized probe: empty Hessian" in
  candle_action296_probe_rational_profile "hessian-upper" hessian_upper;
  let half_hessian_theorem =
    candle_action296_probe_compute "half-hessian"
      (list_mk_comb
        (`candle_cv_q_mul_normalized_extended`,
         [`candle_cv_q_half`;hessian_upper])) in
  let half_hessian = rand (concl half_hessian_theorem) in
  candle_action296_probe_rational_profile "half-hessian" half_hessian;
  let remainder_theorem =
    candle_action296_probe_compute "remainder"
      (list_mk_comb
        (`candle_cv_q_add_normalized_extended`,
         [gradient_upper;half_hessian])) in
  let remainder = rand (concl remainder_theorem) in
  candle_action296_probe_rational_profile "remainder" remainder;
  let upper_theorem =
    candle_action296_probe_compute "normalized-upper"
      (list_mk_comb
        (`candle_cv_q_add_normalized_extended`,[center_value;remainder])) in
  let upper = rand (concl upper_theorem) in
  candle_action296_probe_rational_profile "final-upper" upper;
  let finish_theorem =
    candle_action296_probe_compute "finish"
      (list_mk_comb
        (`candle_cv_q_dim_whole_box_finish`,
         [domain_value;valid;upper])) in
  let finish = rand (concl finish_theorem) in
  let verdict,final_upper =
    candle_q_dim_analytic_jet_dest_pair finish in
  verdict,String.length (string_of_term final_upper);;

print_endline
  ("CANDLE_CV_ACTION296_NORMALIZED_PROBE_RESULT verdict=" ^
   (if aconv candle_action296_probe_verdict `Cexp_num 1`
    then "accept" else "reject") ^
   " upper_term_chars=" ^
   string_of_int candle_action296_probe_upper_chars);
print_endline "CANDLE_CV_ACTION296_NORMALIZED_PROBE_OK";;
