(* ========================================================================== *)
(* Normalized Taylor-accumulator probe on the first action-296 leaf.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is a numerical diagnostic only.  It does *)
(* not perform the theorem handoff or count as a proved certificate leaf.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_first_center_check;;
open Candle_cv_analytic_expr_action296_plan;;

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
      candle_cv_q_dim_analytic_first_center_compute_eqs tm in
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
          candle_action296_plan_prepared.program_representation_term])) in
  let center = rand (concl center_theorem) in
  let box_theorem =
    candle_action296_probe_compute "box-jet"
      (list_mk_comb
        (`candle_cv_q_dim_analytic_program`,
         [candle_action296_probe_boxes_term;
          candle_action296_plan_prepared.program_representation_term])) in
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
          (`candle_cv_q_mul_normalized`,[weight;dot])) in
    rand (concl scaled_theorem) in
  let rec accumulate_rows index weights rows accumulator =
    match weights,rows with
    | [],[] -> accumulator
    | weight :: weight_tail,row :: row_tail ->
        let scaled = compute_weighted_row index weight row in
        let sum_theorem =
          candle_action296_probe_compute
            ("hessian-row-" ^ string_of_int index ^ "-sum")
            (list_mk_comb
              (`candle_cv_q_add_normalized`,[scaled;accumulator])) in
        accumulate_rows (index + 1) weight_tail row_tail
          (rand (concl sum_theorem))
    | _ -> failwith "action296 normalized probe: Hessian shape mismatch" in
  let hessian_upper =
    match radius_values,hessian_rows with
    | first_weight :: weight_tail,first_row :: row_tail ->
        accumulate_rows 1 weight_tail row_tail
          (compute_weighted_row 0 first_weight first_row)
    | _ -> failwith "action296 normalized probe: empty Hessian" in
  let half_hessian_theorem =
    candle_action296_probe_compute "half-hessian"
      (list_mk_comb
        (`candle_cv_q_mul_normalized`,
         [`candle_cv_q_half`;hessian_upper])) in
  let half_hessian = rand (concl half_hessian_theorem) in
  let remainder_theorem =
    candle_action296_probe_compute "remainder"
      (list_mk_comb
        (`candle_cv_q_add_normalized`,
         [gradient_upper;half_hessian])) in
  let remainder = rand (concl remainder_theorem) in
  let upper_theorem =
    candle_action296_probe_compute "normalized-upper"
      (list_mk_comb
        (`candle_cv_q_add_normalized`,[center_value;remainder])) in
  let upper = rand (concl upper_theorem) in
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
