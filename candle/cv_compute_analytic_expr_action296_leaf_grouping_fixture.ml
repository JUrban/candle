(* ========================================================================== *)
(* Reusable genuine action-296 leaf domains and envelope operations.          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_action296_plan;;

let candle_action296_leaf_grouping_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_leaf_grouping_collect domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 leaf grouping: unexpected pass selection";
      [domain_th]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "action296 leaf grouping: unexpected convex branch";
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_leaf_grouping_collect left_domain left @
      candle_action296_leaf_grouping_collect right_domain right
  | P_result_mono _ ->
      failwith "action296 leaf grouping: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 leaf grouping: unexpected reference node";;

let candle_action296_leaf_grouping_leaves : thm list ref = ref [];;
let _ =
  candle_action296_leaf_grouping_leaves :=
    candle_action296_leaf_grouping_collect
      candle_action296_leaf_grouping_root_domain
      candle_action296_plan_precision_tree;;

if length !candle_action296_leaf_grouping_leaves <> 1061 then
  failwith "action296 leaf grouping: leaf cardinality drift";;

let candle_action296_leaf_grouping_indices = [0;1;2;3;4;5;6;7];;
let candle_action296_leaf_grouping_domains =
  map
    (fun index -> List.nth !candle_action296_leaf_grouping_leaves index)
    candle_action296_leaf_grouping_indices;;

let candle_action296_leaf_grouping_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_leaf_grouping_envelope_lower left right =
  map2
    (fun l r -> if Num.le_num (rat_of_term l) (rat_of_term r) then l else r)
    left right;;

let candle_action296_leaf_grouping_envelope_upper left right =
  map2
    (fun l r -> if Num.le_num (rat_of_term l) (rat_of_term r) then r else l)
    left right;;

let candle_action296_leaf_grouping_envelope domains =
  match map candle_action296_leaf_grouping_domain_bounds domains with
  | first :: remaining ->
      List.fold_left
        (fun (lower,upper) (next_lower,next_upper) ->
          candle_action296_leaf_grouping_envelope_lower lower next_lower,
          candle_action296_leaf_grouping_envelope_upper upper next_upper)
        first remaining
  | [] -> failwith "action296 leaf grouping: empty envelope";;

let rec candle_action296_leaf_grouping_take count items =
  if count = 0 then [],items else
  match items with
  | [] -> failwith "action296 leaf grouping: incomplete group"
  | head :: tail ->
      let selected,remaining =
        candle_action296_leaf_grouping_take (count - 1) tail in
      head :: selected,remaining;;

let rec candle_action296_leaf_grouping_partition group_size items =
  match items with
  | [] -> []
  | _ ->
      let group,remaining =
        candle_action296_leaf_grouping_take group_size items in
      group ::
        candle_action296_leaf_grouping_partition group_size remaining;;
