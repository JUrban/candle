(* ========================================================================== *)
(* Focused depth-two scan for genuine action-296 precision leaf 696.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE diagnostic.  The parent has no viable complete *)
(* one-coordinate split, but the right axis-6 child accepts.  Reuse one      *)
(* parent-local source certificate and scan all axes below the rejected left *)
(* axis-6 child.                                                              *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_grouped_32_split_scan_algebraic.ml";;

let candle_action296_leaf696_depth2_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-leaf696-depth2-scan-algebraic" ^
     " scope=axis6-left phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_leaf696_depth2_parent =
  List.nth !candle_action296_leaf_grouping_leaves 696;;

let candle_action296_leaf696_depth2_left,
    candle_action296_leaf696_depth2_right =
  M_verifier.split_domain candle_action296_plan_dimension 6 6
    candle_action296_leaf696_depth2_parent;;

let _ = candle_action296_leaf696_depth2_marker "source-preparation" "begin";;
let candle_action296_leaf696_depth2_prepared_ref :
    candle_q_dim_analytic_jet_prepared_six option ref = ref None;;
let _ =
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds
      candle_action296_leaf696_depth2_parent in
  candle_action296_leaf696_depth2_prepared_ref :=
    Some
      (candle_q_dim_analytic_jet_prepare_box_six
        candle_action296_plan_prepared.function_term lower upper);;
let _ = candle_action296_leaf696_depth2_marker "source-preparation" "end";;

let candle_action296_leaf696_depth2_prepared () =
  match !candle_action296_leaf696_depth2_prepared_ref with
  | Some prepared -> prepared
  | None -> failwith "action296 leaf696 depth2: missing preparation";;

let _ =
  candle_action296_leaf696_depth2_marker "point-plan-compilation" "begin";;
let candle_action296_leaf696_depth2_plan_ref :
    candle_q_dim_taylor_model_point_plan_six option ref = ref None;;
let _ =
  candle_action296_leaf696_depth2_plan_ref :=
    Some
      (candle_q_dim_taylor_model_point_plan_six
        (candle_action296_leaf696_depth2_prepared ()));;
let _ =
  candle_action296_leaf696_depth2_marker "point-plan-compilation" "end";;

let candle_action296_leaf696_depth2_plan () =
  match !candle_action296_leaf696_depth2_plan_ref with
  | Some plan -> plan
  | None -> failwith "action296 leaf696 depth2: missing point plan";;

let _ =
  candle_action296_leaf696_depth2_marker "grandchild-preparation" "begin";;
let candle_action296_leaf696_depth2_cases_ref :
    candle_action296_adaptive_grouping_case_six list option ref = ref None;;
let _ =
  let prepared = candle_action296_leaf696_depth2_prepared () and
      plan = candle_action296_leaf696_depth2_plan () in
  let grandchildren =
    candle_action296_grouped_32_split_scan_children
      candle_action296_leaf696_depth2_left in
  candle_action296_leaf696_depth2_cases_ref :=
    Some
      (map
        (candle_action296_adaptive_grouping_case prepared plan)
        grandchildren);;
let _ =
  candle_action296_leaf696_depth2_marker "grandchild-preparation" "end";;

let candle_action296_leaf696_depth2_cases () =
  match !candle_action296_leaf696_depth2_cases_ref with
  | Some cases -> cases
  | None -> failwith "action296 leaf696 depth2: missing cases";;

let _ = candle_action296_leaf696_depth2_marker "kernel-compute" "begin";;
let candle_action296_leaf696_depth2_flags_ref : term list option ref = ref None;;
let _ =
  candle_action296_leaf696_depth2_flags_ref :=
    Some
      (candle_action296_adaptive_grouping_compute
        (candle_action296_leaf696_depth2_prepared (),
         candle_action296_leaf696_depth2_cases ()));;
let _ = candle_action296_leaf696_depth2_marker "kernel-compute" "end";;

let candle_action296_leaf696_depth2_flags () =
  match !candle_action296_leaf696_depth2_flags_ref with
  | Some flags -> flags
  | None -> failwith "action296 leaf696 depth2: missing flags";;

let candle_action296_leaf696_depth2_bools =
  map
    (fun flag ->
      match candle_action296_adaptive_grouping_flag_string flag with
      | "0" -> false
      | "1" -> true
      | _ -> failwith "action296 leaf696 depth2: Boolean conversion")
    (candle_action296_leaf696_depth2_flags ());;

let candle_action296_leaf696_depth2_viable_axes =
  let rec scan axis = function
    | [] ->
        if axis = 7 then []
        else failwith "action296 leaf696 depth2: incomplete child flags"
    | left :: right :: tail ->
        let remaining = scan (axis + 1) tail in
        if left && right then axis :: remaining else remaining
    | _ -> failwith "action296 leaf696 depth2: odd child flags" in
  scan 1 candle_action296_leaf696_depth2_bools;;

if length (candle_action296_leaf696_depth2_flags ()) <> 12 then
  failwith "action296 leaf696 depth2: flag cardinality";;

let candle_action296_leaf696_depth2_signature =
  String.concat ","
    (map
      (fun accepted -> if accepted then "1" else "0")
      candle_action296_leaf696_depth2_bools);;

if candle_action296_leaf696_depth2_viable_axes <> [1;2;3;4;5;6] ||
   candle_action296_leaf696_depth2_signature <>
     "1,1,1,1,1,1,1,1,1,1,1,1" then
  failwith "action296 leaf696 depth2: expected verdict drift";;

print_endline
  ("CANDLE_CV_ACTION296_LEAF696_DEPTH2_SCAN_RESULT" ^
   " first_axis=6 accepted_sibling=right" ^
   " viable_second_axes=" ^
   String.concat ","
     (map string_of_int candle_action296_leaf696_depth2_viable_axes) ^
   " flags=" ^ candle_action296_leaf696_depth2_signature);;
print_endline
  "CANDLE_CV_ACTION296_LEAF696_DEPTH2_SCAN_OK DEVELOPMENT_NON_RELEASE";;
