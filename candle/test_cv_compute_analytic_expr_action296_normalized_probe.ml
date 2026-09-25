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
  let upper_theorem =
    candle_action296_probe_compute "normalized-upper"
      (list_mk_comb
        (`candle_cv_q_dim_taylor_upper_normalized`,
         [mk_comb
           (`candle_cv_q_radius_list`,candle_action296_probe_boxes_term);
          mk_comb
           (`candle_cv_q_dim_first_jet_f`,
            mk_comb (`candle_cv_q_dim_analytic_first_result_jet`,center));
          mk_comb
           (`candle_cv_q_dim_first_jet_gradient`,
            mk_comb (`candle_cv_q_dim_analytic_first_result_jet`,center));
          mk_comb
           (`candle_cv_q_dim_jet_hessian`,
            mk_comb (`candle_cv_q_dim_analytic_result_jet`,box))])) in
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
