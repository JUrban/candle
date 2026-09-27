(* ========================================================================== *)
(* One-split axis scan for genuine action-296 precision leaf 1057.            *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_leaf_split_scan.ml";;

let candle_action296_leaf1057_axis_scan_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-leaf1057-axis-scan scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_leaf1057_axis_scan_parent =
  List.nth !candle_action296_leaf_split_scan_leaves 1057;;

let _ =
  candle_action296_leaf1057_axis_scan_marker
    "index-1057" "source-preparation" "begin";;
let candle_action296_leaf1057_axis_scan_prepared :
    candle_q_dim_analytic_jet_prepared_six option ref = ref None;;
let _ =
  let lower,upper =
    candle_action296_leaf_split_scan_domain_bounds
      candle_action296_leaf1057_axis_scan_parent in
  candle_action296_leaf1057_axis_scan_prepared :=
    Some
      (candle_q_dim_analytic_jet_prepare_box_six
        candle_action296_plan_prepared.function_term lower upper);;
let _ =
  candle_action296_leaf1057_axis_scan_marker
    "index-1057" "source-preparation" "end";;

let candle_action296_leaf1057_axis_scan_get_prepared () =
  match !candle_action296_leaf1057_axis_scan_prepared with
  | Some prepared -> prepared
  | None -> failwith "action296 leaf1057 axis scan: missing preparation";;

let _ =
  candle_action296_leaf1057_axis_scan_marker
    "index-1057" "point-plan-compilation" "begin";;
let candle_action296_leaf1057_axis_scan_plan :
    candle_q_dim_taylor_model_point_plan_six option ref = ref None;;
let _ =
  candle_action296_leaf1057_axis_scan_plan :=
    Some
      (candle_q_dim_taylor_model_point_plan_six
        (candle_action296_leaf1057_axis_scan_get_prepared ()));;
let _ =
  candle_action296_leaf1057_axis_scan_marker
    "index-1057" "point-plan-compilation" "end";;

let candle_action296_leaf1057_axis_scan_get_plan () =
  match !candle_action296_leaf1057_axis_scan_plan with
  | Some plan -> plan
  | None -> failwith "action296 leaf1057 axis scan: missing point plan";;

let _ =
  candle_action296_leaf1057_axis_scan_marker
    "index-1057" "per-box-preparation" "begin";;
let candle_action296_leaf1057_axis_scan_cases : term list ref = ref [];;
let _ =
  let prepared = candle_action296_leaf1057_axis_scan_get_prepared () and
      plan = candle_action296_leaf1057_axis_scan_get_plan () in
  let domains =
    candle_action296_leaf1057_axis_scan_parent ::
    candle_action296_leaf_split_scan_children
      candle_action296_leaf1057_axis_scan_parent in
  candle_action296_leaf1057_axis_scan_cases :=
    map (candle_action296_leaf_split_scan_case prepared plan) domains;;
let _ =
  candle_action296_leaf1057_axis_scan_marker
    "index-1057" "per-box-preparation" "end";;

let _ =
  candle_action296_leaf1057_axis_scan_marker
    "index-1057" "kernel-compute" "begin";;
let candle_action296_leaf1057_axis_scan_flags : term list ref = ref [];;
let _ =
  candle_action296_leaf1057_axis_scan_flags :=
    candle_action296_leaf_split_scan_compute
      (candle_action296_leaf1057_axis_scan_get_prepared (),
       !candle_action296_leaf1057_axis_scan_cases);;
let _ =
  candle_action296_leaf1057_axis_scan_marker
    "index-1057" "kernel-compute" "end";;

let candle_action296_leaf1057_axis_scan_reported = ref false;;
let _ =
  if length !candle_action296_leaf1057_axis_scan_flags <> 13 then
    failwith "action296 leaf1057 axis scan: flag cardinality";
  let booleans =
    map candle_action296_leaf_split_scan_flag_bool
      !candle_action296_leaf1057_axis_scan_flags in
  let children =
    match booleans with
    | false :: child_flags -> child_flags
    | true :: _ -> failwith "action296 leaf1057 axis scan: parent passed"
    | [] -> failwith "action296 leaf1057 axis scan: empty result" in
  let viable_axes = candle_action296_leaf_split_scan_viable_axes booleans in
  let child_accepts =
    List.fold_left
      (fun count accepted -> if accepted then count + 1 else count)
      0 children in
  print_endline
    ("CANDLE_CV_ACTION296_LEAF1057_AXIS_SCAN_RESULT child_accepts=" ^
     string_of_int child_accepts ^ "/12 viable_axes=" ^
     String.concat "," (map string_of_int viable_axes) ^ " flags=" ^
     String.concat ","
       (map (fun accepted -> if accepted then "1" else "0") booleans));
  candle_action296_leaf1057_axis_scan_reported := true;;

if not !candle_action296_leaf1057_axis_scan_reported then
  failwith "action296 leaf1057 axis scan: results were not reported"
else
  print_endline
    "CANDLE_CV_ACTION296_LEAF1057_AXIS_SCAN_OK DEVELOPMENT_NON_RELEASE";;
