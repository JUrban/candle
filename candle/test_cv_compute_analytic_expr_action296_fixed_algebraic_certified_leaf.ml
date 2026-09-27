(* ========================================================================== *)
(* Complete tagged fixed/rational proof of the first genuine action-296 leaf. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The parent certificate leaf needs two child   *)
(* boxes.  Each child is discharged by the proved algebraic hybrid and the    *)
(* existing Flyspeck cell interface glues them back to the parent.             *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_certified_prove;;

let candle_action296_fixed_algebraic_leaf_axioms_before = axioms ();;
let candle_action296_fixed_algebraic_leaf_started = Unix.gettimeofday ();;

let candle_action296_fixed_algebraic_leaf_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_fixed_algebraic_leaf_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 fixed algebraic leaf: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 fixed algebraic leaf: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_fixed_algebraic_leaf_find left_domain left
  | P_result_mono _ ->
      failwith "action296 fixed algebraic leaf: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 fixed algebraic leaf: unexpected reference node";;

let candle_action296_fixed_algebraic_leaf_parent_domain =
  candle_action296_fixed_algebraic_leaf_find
    candle_action296_fixed_algebraic_leaf_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_fixed_algebraic_leaf_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_fixed_algebraic_leaf_parent_lower,
    candle_action296_fixed_algebraic_leaf_parent_upper =
  candle_action296_fixed_algebraic_leaf_domain_bounds
    candle_action296_fixed_algebraic_leaf_parent_domain;;

let candle_action296_fixed_algebraic_leaf_box_prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    candle_action296_plan_prepared.function_term
    candle_action296_fixed_algebraic_leaf_parent_lower
    candle_action296_fixed_algebraic_leaf_parent_upper;;

let candle_action296_fixed_algebraic_leaf_point_plan =
  candle_q_dim_taylor_model_point_plan_six
    candle_action296_fixed_algebraic_leaf_box_prepared;;

let candle_action296_fixed_algebraic_leaf_left_domain,
    candle_action296_fixed_algebraic_leaf_right_domain =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_fixed_algebraic_leaf_parent_domain;;

type candle_action296_fixed_algebraic_leaf_cell = {
  fixed_algebraic_leaf_center_variant :
    candle_q_dim_taylor_model_program_variant_six;
  fixed_algebraic_leaf_lower : term list;
  fixed_algebraic_leaf_upper : term list;
};;

let candle_action296_fixed_algebraic_leaf_cell domain_th =
  let lower,upper =
    candle_action296_fixed_algebraic_leaf_domain_bounds domain_th in
  let center_variant =
    candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
      candle_action296_fixed_algebraic_leaf_box_prepared
      candle_action296_fixed_algebraic_leaf_point_plan lower upper in
  {
    fixed_algebraic_leaf_center_variant = center_variant;
    fixed_algebraic_leaf_lower = lower;
    fixed_algebraic_leaf_upper = upper;
  };;

let candle_action296_fixed_algebraic_leaf_left_cell =
  candle_action296_fixed_algebraic_leaf_cell
    candle_action296_fixed_algebraic_leaf_left_domain;;
let candle_action296_fixed_algebraic_leaf_right_cell =
  candle_action296_fixed_algebraic_leaf_cell
    candle_action296_fixed_algebraic_leaf_right_domain;;

let rec candle_action296_fixed_algebraic_leaf_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_action296_fixed_algebraic_leaf_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_action296_fixed_algebraic_leaf_profile_events :
    string list ref = ref [];;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      candle_action296_fixed_algebraic_leaf_profile_events :=
        event :: !candle_action296_fixed_algebraic_leaf_profile_events;
      print_endline
        ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_LEAF_STAGE event=" ^ event));;

let candle_action296_fixed_algebraic_leaf_prove label cell domain_th =
  let started = Unix.gettimeofday () in
  print_endline
    ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_LEAF_CELL cell=" ^ label ^
     " event=begin");
  let theorem =
    candle_reflected_nl_source_pass_with
      candle_action296_plan_prepared.function_term
      (fun lower upper ->
        if not
            (candle_action296_fixed_algebraic_leaf_aconv_lists
               lower cell.fixed_algebraic_leaf_lower &&
             candle_action296_fixed_algebraic_leaf_aconv_lists
               upper cell.fixed_algebraic_leaf_upper) then
          failwith "action296 fixed algebraic leaf: unexpected handoff box";
        candle_q_dim_taylor_model_fixed_algebraic_certified_prove_box_variant_six
          cell.fixed_algebraic_leaf_center_variant
          candle_action296_fixed_algebraic_leaf_box_prepared lower upper)
      domain_th in
  print_endline
    ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_LEAF_CELL cell=" ^ label ^
     " event=end seconds=" ^
     string_of_float (Unix.gettimeofday () -. started));
  theorem;;

let candle_action296_fixed_algebraic_leaf_left_theorem =
  candle_action296_fixed_algebraic_leaf_prove "left"
    candle_action296_fixed_algebraic_leaf_left_cell
    candle_action296_fixed_algebraic_leaf_left_domain;;

let candle_action296_fixed_algebraic_leaf_right_theorem =
  candle_action296_fixed_algebraic_leaf_prove "right"
    candle_action296_fixed_algebraic_leaf_right_cell
    candle_action296_fixed_algebraic_leaf_right_domain;;

let candle_action296_fixed_algebraic_leaf_theorem =
  M_verifier.merge_m_cell_list_pass candle_action296_plan_dimension
    (M_verifier.m_glue_cells_list
      candle_action296_plan_dimension 4
      candle_action296_fixed_algebraic_leaf_left_theorem
      candle_action296_fixed_algebraic_leaf_right_theorem);;

let candle_action296_fixed_algebraic_leaf_functions,
    candle_action296_fixed_algebraic_leaf_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_action296_fixed_algebraic_leaf_theorem);;

let candle_action296_fixed_algebraic_leaf_expected_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_fixed_algebraic_leaf_parent_domain);;

let candle_action296_fixed_algebraic_leaf_theorem_md5 =
  Digest.to_hex
    (Digest.string
      (string_of_thm candle_action296_fixed_algebraic_leaf_theorem));;

if candle_action296_fixed_algebraic_leaf_functions <>
     [candle_action296_plan_prepared.function_term] ||
   not
     (aconv candle_action296_fixed_algebraic_leaf_proved_domain
       candle_action296_fixed_algebraic_leaf_expected_domain) ||
   hyp candle_action296_fixed_algebraic_leaf_theorem <> [] ||
   candle_action296_fixed_algebraic_leaf_theorem_md5 <>
     "926f44ab8d5f2303064fe5788cead588" then
  failwith "action296 fixed algebraic leaf: final theorem mismatch";;

let candle_action296_fixed_algebraic_leaf_axioms_after = axioms ();;

if length candle_action296_fixed_algebraic_leaf_axioms_after <>
     length candle_action296_fixed_algebraic_leaf_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_fixed_algebraic_leaf_axioms_before)
       candle_action296_fixed_algebraic_leaf_axioms_after) then
  failwith "action296 fixed algebraic leaf: changed the global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_LEAF_RESULT cells=2 computes=2" ^
   " theorem_md5=" ^ candle_action296_fixed_algebraic_leaf_theorem_md5 ^
   " profile_events=" ^
   string_of_int
     (length !candle_action296_fixed_algebraic_leaf_profile_events) ^
   " total_seconds=" ^
   string_of_float
     (Unix.gettimeofday () -. candle_action296_fixed_algebraic_leaf_started));;
print_endline
  "CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_LEAF_OK DEVELOPMENT_NON_RELEASE";;
