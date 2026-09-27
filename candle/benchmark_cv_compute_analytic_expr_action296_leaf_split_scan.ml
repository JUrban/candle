(* ========================================================================== *)
(* One-split scan for rejected genuine action-296 precision leaves.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE diagnostic.  For each of the first four genuine *)
(* precision leaves, check the unsplit box and both children from splitting   *)
(* each of the six coordinates.  One parent-local box certificate and point   *)
(* plan are shared across its thirteen checks.                                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_compute.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;

let candle_action296_leaf_split_scan_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-leaf-split-scan scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_leaf_split_scan_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_leaf_split_scan_collect domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 leaf split scan: unexpected pass selection";
      [domain_th]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "action296 leaf split scan: unexpected convex branch";
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_leaf_split_scan_collect left_domain left @
      candle_action296_leaf_split_scan_collect right_domain right
  | P_result_mono _ ->
      failwith "action296 leaf split scan: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 leaf split scan: unexpected reference node";;

let candle_action296_leaf_split_scan_leaves : thm list ref = ref [];;
let _ =
  candle_action296_leaf_split_scan_leaves :=
    candle_action296_leaf_split_scan_collect
      candle_action296_leaf_split_scan_root_domain
      candle_action296_plan_precision_tree;;

if length !candle_action296_leaf_split_scan_leaves <> 1061 then
  failwith "action296 leaf split scan: leaf cardinality drift";;

let candle_action296_leaf_split_scan_indices = [0;1;2;3];;
let candle_action296_leaf_split_scan_parents =
  map
    (fun index -> List.nth !candle_action296_leaf_split_scan_leaves index)
    candle_action296_leaf_split_scan_indices;;

let candle_action296_leaf_split_scan_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_leaf_split_scan_children parent =
  List.flatten
    (map
      (fun axis ->
        let left,right =
          M_verifier.split_domain
            candle_action296_plan_dimension 6 axis parent in
        [left;right])
      [1;2;3;4;5;6]);;

let candle_cv_action296_leaf_split_scan_flags_def = define
 `(candle_cv_action296_leaf_split_scan_flags
      box_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_leaf_split_scan_flags
      box_program (Cexp_pair job jobs) =
     Cexp_pair
       (Cexp_fst
         (candle_cv_fs_q_dim_taylor_model_certified_check
           (Cexp_fst job) box_program (Cexp_snd job)))
       (candle_cv_action296_leaf_split_scan_flags box_program jobs))`;;

let candle_cv_action296_leaf_split_scan_flags_compute = prove
 (`!box_program jobs.
     candle_cv_action296_leaf_split_scan_flags box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (Cexp_fst
           (candle_cv_fs_q_dim_taylor_model_certified_check
             (Cexp_fst (Cexp_fst jobs)) box_program
             (Cexp_snd (Cexp_fst jobs))))
         (candle_cv_action296_leaf_split_scan_flags
           box_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_leaf_split_scan_flags_def;cexp_if_def;
              cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_action296_leaf_split_scan_eqs =
  union candle_cv_fs_q_dim_taylor_model_compute_eqs
    [SPEC_ALL candle_cv_action296_leaf_split_scan_flags_compute];;

let candle_action296_leaf_split_scan_case prepared plan domain_th =
  let lower,upper = candle_action296_leaf_split_scan_domain_bounds domain_th in
  let center_variant =
    candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
      prepared plan lower upper in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  list_mk_comb
    (`Cexp_pair`,
     [center_variant.variant_program_representation_term;
      rand (concl boxes_representation)]);;

let candle_action296_leaf_split_scan_cases_term cases =
  itlist
    (fun item tail -> list_mk_comb (`Cexp_pair`,[item;tail]))
    cases `Cexp_num 0`;;

let rec candle_action296_leaf_split_scan_dest_flags tm =
  if aconv tm `Cexp_num 0` then []
  else
    let operator,arguments = strip_comb tm in
    if aconv operator `Cexp_pair` then
      match arguments with
      | [flag;tail] -> flag :: candle_action296_leaf_split_scan_dest_flags tail
      | _ -> failwith "action296 leaf split scan: malformed flag pair"
    else failwith "action296 leaf split scan: malformed flag list";;

let candle_action296_leaf_split_scan_compute (prepared,cases) =
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_action296_leaf_split_scan_eqs
      (list_mk_comb
        (`candle_cv_action296_leaf_split_scan_flags`,
         [prepared.program_representation_term;
          candle_action296_leaf_split_scan_cases_term cases])) in
  if hyp theorem <> [] then
    failwith "action296 leaf split scan: computed theorem assumptions";
  let flags =
    candle_action296_leaf_split_scan_dest_flags (rand (concl theorem)) in
  if length flags <> length cases then
    failwith "action296 leaf split scan: result cardinality";
  flags;;

let candle_action296_leaf_split_scan_flag_bool flag =
  if aconv flag `Cexp_num 1` then true
  else if aconv flag `Cexp_num 0` then false
  else failwith "action296 leaf split scan: non-Boolean result";;

let candle_action296_leaf_split_scan_scope = "leaves-0-3";;

let _ =
  candle_action296_leaf_split_scan_marker
    candle_action296_leaf_split_scan_scope "source-preparation" "begin";;
let candle_action296_leaf_split_scan_prepared :
    (thm * candle_q_dim_analytic_jet_prepared_six) list ref = ref [];;
let _ =
  candle_action296_leaf_split_scan_prepared :=
    map
      (fun parent ->
        let lower,upper =
          candle_action296_leaf_split_scan_domain_bounds parent in
        parent,
        candle_q_dim_analytic_jet_prepare_box_six
          candle_action296_plan_prepared.function_term lower upper)
      candle_action296_leaf_split_scan_parents;;
let _ =
  candle_action296_leaf_split_scan_marker
    candle_action296_leaf_split_scan_scope "source-preparation" "end";;

let _ =
  candle_action296_leaf_split_scan_marker
    candle_action296_leaf_split_scan_scope "point-plan-compilation" "begin";;
let candle_action296_leaf_split_scan_planned :
    (thm * candle_q_dim_analytic_jet_prepared_six *
     candle_q_dim_taylor_model_point_plan_six) list ref = ref [];;
let _ =
  candle_action296_leaf_split_scan_planned :=
    map
      (fun (parent,prepared) ->
        parent,prepared,candle_q_dim_taylor_model_point_plan_six prepared)
      !candle_action296_leaf_split_scan_prepared;;
let _ =
  candle_action296_leaf_split_scan_marker
    candle_action296_leaf_split_scan_scope "point-plan-compilation" "end";;

let _ =
  candle_action296_leaf_split_scan_marker
    candle_action296_leaf_split_scan_scope "per-box-preparation" "begin";;
let candle_action296_leaf_split_scan_computed :
    (candle_q_dim_analytic_jet_prepared_six * term list) list ref = ref [];;
let _ =
  candle_action296_leaf_split_scan_computed :=
    map
      (fun (parent,prepared,plan) ->
        let domains =
          parent :: candle_action296_leaf_split_scan_children parent in
        prepared,
        map (candle_action296_leaf_split_scan_case prepared plan) domains)
      !candle_action296_leaf_split_scan_planned;;
let _ =
  candle_action296_leaf_split_scan_marker
    candle_action296_leaf_split_scan_scope "per-box-preparation" "end";;

let _ =
  candle_action296_leaf_split_scan_marker
    candle_action296_leaf_split_scan_scope "kernel-compute" "begin";;
let candle_action296_leaf_split_scan_flag_sets : term list list ref = ref [];;
let _ =
  candle_action296_leaf_split_scan_flag_sets :=
    map candle_action296_leaf_split_scan_compute
      !candle_action296_leaf_split_scan_computed;;
let _ =
  candle_action296_leaf_split_scan_marker
    candle_action296_leaf_split_scan_scope "kernel-compute" "end";;

let candle_action296_leaf_split_scan_viable_axes booleans =
  let rec scan axis remaining =
    if axis > 6 then [] else
    match remaining with
    | left :: right :: tail ->
        let rest = scan (axis + 1) tail in
        if left && right then axis :: rest else rest
    | _ -> failwith "action296 leaf split scan: child flag shape" in
  match booleans with
  | false :: children -> scan 1 children
  | true :: _ -> failwith "action296 leaf split scan: parent unexpectedly passed"
  | [] -> failwith "action296 leaf split scan: empty result";;

let rec candle_action296_leaf_split_scan_iter2 action left right =
  match left,right with
  | [],[] -> ()
  | left_head :: left_tail,right_head :: right_tail ->
      action left_head right_head;
      candle_action296_leaf_split_scan_iter2 action left_tail right_tail
  | _ -> failwith "action296 leaf split scan: reporting shape";;

let candle_action296_leaf_split_scan_reported = ref false;;
let _ =
  if length !candle_action296_leaf_split_scan_flag_sets <> 4 then
    failwith "action296 leaf split scan: parent result cardinality";
  candle_action296_leaf_split_scan_iter2
    (fun index flags ->
      if length flags <> 13 then
        failwith "action296 leaf split scan: flag-set cardinality";
      let booleans = map candle_action296_leaf_split_scan_flag_bool flags in
      let children =
        match booleans with
        | false :: child_flags -> child_flags
        | true :: _ ->
            failwith "action296 leaf split scan: parent unexpectedly passed"
        | [] -> failwith "action296 leaf split scan: empty result" in
      let viable_axes = candle_action296_leaf_split_scan_viable_axes booleans in
      let child_accepts =
        List.fold_left
          (fun count accepted -> if accepted then count + 1 else count)
          0 children in
      print_endline
        ("CANDLE_CV_ACTION296_LEAF_SPLIT_SCAN_RESULT index=" ^
         string_of_int index ^ " child_accepts=" ^
         string_of_int child_accepts ^ "/12 viable_axes=" ^
         String.concat "," (map string_of_int viable_axes) ^ " flags=" ^
         String.concat ","
           (map (fun accepted -> if accepted then "1" else "0") booleans)))
    candle_action296_leaf_split_scan_indices
    !candle_action296_leaf_split_scan_flag_sets;
  candle_action296_leaf_split_scan_reported := true;;

if not !candle_action296_leaf_split_scan_reported then
  failwith "action296 leaf split scan: results were not reported"
else
  print_endline
    "CANDLE_CV_ACTION296_LEAF_SPLIT_SCAN_OK DEVELOPMENT_NON_RELEASE";;
