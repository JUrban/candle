(* ========================================================================== *)
(* Separated genuine action-296 leaf sample with one axis-4 refinement.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE diagnostic.  Twelve leaves from the quarter,    *)
(* middle, and far end of the 1,061-leaf precision tree are checked with      *)
(* parent-local certificates.  Each rejected parent is compared with its two  *)
(* exact axis-4 children.                                                      *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_leaf_split_scan.ml";;

let candle_action296_leaf_varied_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-leaf-varied scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_leaf_varied_indices =
  [255;256;257;258; 511;512;513;514; 1057;1058;1059;1060];;

let candle_action296_leaf_varied_parents =
  map
    (fun index -> List.nth !candle_action296_leaf_split_scan_leaves index)
    candle_action296_leaf_varied_indices;;

let candle_action296_leaf_varied_axis4_children parent =
  let left,right =
    M_verifier.split_domain candle_action296_plan_dimension 6 4 parent in
  [left;right];;

let candle_action296_leaf_varied_scope = "separated-12";;

let _ =
  candle_action296_leaf_varied_marker
    candle_action296_leaf_varied_scope "source-preparation" "begin";;
let candle_action296_leaf_varied_prepared :
    (thm * candle_q_dim_analytic_jet_prepared_six) list ref = ref [];;
let _ =
  candle_action296_leaf_varied_prepared :=
    map
      (fun parent ->
        let lower,upper =
          candle_action296_leaf_split_scan_domain_bounds parent in
        parent,
        candle_q_dim_analytic_jet_prepare_box_six
          candle_action296_plan_prepared.function_term lower upper)
      candle_action296_leaf_varied_parents;;
let _ =
  candle_action296_leaf_varied_marker
    candle_action296_leaf_varied_scope "source-preparation" "end";;

let _ =
  candle_action296_leaf_varied_marker
    candle_action296_leaf_varied_scope "point-plan-compilation" "begin";;
let candle_action296_leaf_varied_planned :
    (thm * candle_q_dim_analytic_jet_prepared_six *
     candle_q_dim_taylor_model_point_plan_six) list ref = ref [];;
let _ =
  candle_action296_leaf_varied_planned :=
    map
      (fun (parent,prepared) ->
        parent,prepared,candle_q_dim_taylor_model_point_plan_six prepared)
      !candle_action296_leaf_varied_prepared;;
let _ =
  candle_action296_leaf_varied_marker
    candle_action296_leaf_varied_scope "point-plan-compilation" "end";;

let _ =
  candle_action296_leaf_varied_marker
    candle_action296_leaf_varied_scope "per-box-preparation" "begin";;
let candle_action296_leaf_varied_computed :
    (candle_q_dim_analytic_jet_prepared_six * term list) list ref = ref [];;
let _ =
  candle_action296_leaf_varied_computed :=
    map
      (fun (parent,prepared,plan) ->
        let domains =
          parent :: candle_action296_leaf_varied_axis4_children parent in
        prepared,
        map (candle_action296_leaf_split_scan_case prepared plan) domains)
      !candle_action296_leaf_varied_planned;;
let _ =
  candle_action296_leaf_varied_marker
    candle_action296_leaf_varied_scope "per-box-preparation" "end";;

let _ =
  candle_action296_leaf_varied_marker
    candle_action296_leaf_varied_scope "kernel-compute" "begin";;
let candle_action296_leaf_varied_flag_sets : term list list ref = ref [];;
let _ =
  candle_action296_leaf_varied_flag_sets :=
    map candle_action296_leaf_split_scan_compute
      !candle_action296_leaf_varied_computed;;
let _ =
  candle_action296_leaf_varied_marker
    candle_action296_leaf_varied_scope "kernel-compute" "end";;

let candle_action296_leaf_varied_direct = ref 0;;
let candle_action296_leaf_varied_closed = ref 0;;
let candle_action296_leaf_varied_reported = ref false;;
let _ =
  if length !candle_action296_leaf_varied_flag_sets <> 12 then
    failwith "action296 varied leaves: result cardinality";
  candle_action296_leaf_split_scan_iter2
    (fun index flags ->
      let booleans = map candle_action296_leaf_split_scan_flag_bool flags in
      let parent,left,right =
        match booleans with
        | [parent;left;right] -> parent,left,right
        | _ -> failwith "action296 varied leaves: flag-set shape" in
      let closed = parent || (left && right) in
      if parent then
        candle_action296_leaf_varied_direct :=
          !candle_action296_leaf_varied_direct + 1;
      if closed then
        candle_action296_leaf_varied_closed :=
          !candle_action296_leaf_varied_closed + 1;
      print_endline
        ("CANDLE_CV_ACTION296_LEAF_VARIED_RESULT index=" ^
         string_of_int index ^ " parent=" ^
         (if parent then "1" else "0") ^ " axis4=" ^
         (if left then "1" else "0") ^ "," ^
         (if right then "1" else "0") ^ " closed=" ^
         (if closed then "1" else "0")))
    candle_action296_leaf_varied_indices
    !candle_action296_leaf_varied_flag_sets;
  candle_action296_leaf_varied_reported := true;;

if not !candle_action296_leaf_varied_reported then
  failwith "action296 varied leaves: results were not reported"
else
  print_endline
    ("CANDLE_CV_ACTION296_LEAF_VARIED_SUMMARY total=12 direct=" ^
     string_of_int !candle_action296_leaf_varied_direct ^ " closed=" ^
     string_of_int !candle_action296_leaf_varied_closed);;

if not !candle_action296_leaf_varied_reported then
  failwith "action296 varied leaves: missing success state"
else
  print_endline
    "CANDLE_CV_ACTION296_LEAF_VARIED_OK DEVELOPMENT_NON_RELEASE";;
