(* Diagnostic: exact first-leaf box and one fresh subdivision per axis. *)

needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;
needs "candle/cv_compute_analytic_expr_action296_plan.ml";;

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_action296_plan;;

let candle_action296_bounds_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_bounds_first_leaf domain_th tree =
  match tree with
  | P_result_pass _ -> domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 bounds: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_bounds_first_leaf left_domain left
  | P_result_mono _ ->
      failwith "action296 bounds: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 bounds: unexpected reference node";;

let candle_action296_bounds_leaf =
  candle_action296_bounds_first_leaf candle_action296_bounds_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_bounds_print label domain_th =
  let pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let lower_vector,upper_vector = dest_pair pair in
  let lower,_ = candle_reflected_nl_normalize_vector lower_vector in
  let upper,_ = candle_reflected_nl_normalize_vector upper_vector in
  print_endline
    ("CANDLE_CV_ACTION296_BOUNDS label=" ^ label ^
     " lower=" ^ string_of_term (mk_list (lower,`:real`)) ^
     " upper=" ^ string_of_term (mk_list (upper,`:real`)));;

candle_action296_bounds_print "leaf" candle_action296_bounds_leaf;;

for axis = 1 to 6 do
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis candle_action296_bounds_leaf in
  candle_action296_bounds_print
    ("axis-" ^ string_of_int axis ^ "-left") left;
  candle_action296_bounds_print
    ("axis-" ^ string_of_int axis ^ "-right") right
done;;

print_endline "CANDLE_CV_ACTION296_BOUNDS_OK";;
