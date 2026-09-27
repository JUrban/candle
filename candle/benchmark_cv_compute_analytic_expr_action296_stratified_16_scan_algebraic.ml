(* ========================================================================== *)
(* Stratified one-split coverage scan for genuine action-296 leaves.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE diagnostic.  Select the midpoint leaf from each *)
(* of sixteen equal index strata over the 1,061-leaf precision tree.  Each   *)
(* parent has its own authenticated source box and point plan; the parent and *)
(* both children of every coordinate split are checked in one compact call.  *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_grouped_32_split_scan_algebraic.ml";;

let candle_action296_stratified_16_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-stratified-16-scan-algebraic" ^
     " scope=midpoint-leaves phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_stratified_16_indices =
  [33;99;165;232;298;364;431;497;
   563;629;696;762;828;895;961;1027];;

let candle_action296_stratified_16_parents =
  map
    (fun index ->
      index,List.nth !candle_action296_leaf_grouping_leaves index)
    candle_action296_stratified_16_indices;;

let _ =
  candle_action296_stratified_16_marker "source-preparation" "begin";;
let candle_action296_stratified_16_prepared_ref :
    (int * thm * candle_q_dim_analytic_jet_prepared_six) list option ref =
  ref None;;
let _ =
  candle_action296_stratified_16_prepared_ref :=
    Some
      (map
        (fun (index,parent) ->
          let lower,upper =
            candle_action296_leaf_grouping_domain_bounds parent in
          index,parent,
          candle_q_dim_analytic_jet_prepare_box_six
            candle_action296_plan_prepared.function_term lower upper)
        candle_action296_stratified_16_parents);;
let _ =
  candle_action296_stratified_16_marker "source-preparation" "end";;

let candle_action296_stratified_16_prepared () =
  match !candle_action296_stratified_16_prepared_ref with
  | Some prepared -> prepared
  | None -> failwith "action296 stratified 16: missing preparation";;

let _ =
  candle_action296_stratified_16_marker "point-plan-compilation" "begin";;
let candle_action296_stratified_16_planned_ref :
    (int * thm * candle_q_dim_analytic_jet_prepared_six *
     candle_q_dim_taylor_model_point_plan_six) list option ref = ref None;;
let _ =
  candle_action296_stratified_16_planned_ref :=
    Some
      (map
        (fun (index,parent,prepared) ->
          index,parent,prepared,
          candle_q_dim_taylor_model_point_plan_six prepared)
        (candle_action296_stratified_16_prepared ()));;
let _ =
  candle_action296_stratified_16_marker "point-plan-compilation" "end";;

let candle_action296_stratified_16_planned () =
  match !candle_action296_stratified_16_planned_ref with
  | Some planned -> planned
  | None -> failwith "action296 stratified 16: missing point plans";;

let candle_action296_stratified_16_results_ref :
    (int * term list) list option ref = ref None;;
let _ = candle_action296_stratified_16_marker "sequential-scan" "begin";;
let _ =
  candle_action296_stratified_16_results_ref :=
    Some
      (map
        (fun (index,parent,prepared,plan) ->
          let scope = "leaf-" ^ string_of_int index in
          let _ =
            candle_action296_stratified_16_marker
              (scope ^ "-job-preparation") "begin" in
          let domains =
            parent ::
            candle_action296_grouped_32_split_scan_children parent in
          let cases =
            map
              (candle_action296_adaptive_grouping_case prepared plan)
              domains in
          let _ =
            candle_action296_stratified_16_marker
              (scope ^ "-job-preparation") "end" in
          let _ =
            candle_action296_stratified_16_marker
              (scope ^ "-kernel-compute") "begin" in
          let flags =
            candle_action296_adaptive_grouping_compute (prepared,cases) in
          let _ =
            candle_action296_stratified_16_marker
              (scope ^ "-kernel-compute") "end" in
          index,flags)
        (candle_action296_stratified_16_planned ()));;
let _ = candle_action296_stratified_16_marker "sequential-scan" "end";;

let candle_action296_stratified_16_results () =
  match !candle_action296_stratified_16_results_ref with
  | Some results -> results
  | None -> failwith "action296 stratified 16: missing results";;

let candle_action296_stratified_16_bools flags =
  map
    (fun flag ->
      match candle_action296_adaptive_grouping_flag_string flag with
      | "0" -> false
      | "1" -> true
      | _ -> failwith "action296 stratified 16: Boolean conversion")
    flags;;

let candle_action296_stratified_16_viable_axes children =
  let rec scan axis remaining =
    if axis > 6 then [] else
    match remaining with
    | left :: right :: tail ->
        let rest = scan (axis + 1) tail in
        if left && right then axis :: rest else rest
    | _ -> failwith "action296 stratified 16: child flag shape" in
  scan 1 children;;

let candle_action296_stratified_16_direct = ref 0;;
let candle_action296_stratified_16_one_split = ref 0;;
let candle_action296_stratified_16_hard : int list ref = ref [];;
let candle_action296_stratified_16_signatures : string list ref = ref [];;
let _ =
  if length (candle_action296_stratified_16_results ()) <> 16 then
    failwith "action296 stratified 16: result cardinality";
  List.iter
    (fun (index,raw_flags) ->
      let flags = candle_action296_stratified_16_bools raw_flags in
      let parent,children =
        match flags with
        | parent :: children when length children = 12 -> parent,children
        | _ -> failwith "action296 stratified 16: flag-set shape" in
      let viable_axes =
        candle_action296_stratified_16_viable_axes children in
      let closed = parent || viable_axes <> [] in
      if parent then
        candle_action296_stratified_16_direct :=
          !candle_action296_stratified_16_direct + 1;
      if closed then
        candle_action296_stratified_16_one_split :=
          !candle_action296_stratified_16_one_split + 1
      else
        candle_action296_stratified_16_hard :=
          !candle_action296_stratified_16_hard @ [index];
      let signature =
        String.concat ","
          (map (fun accepted -> if accepted then "1" else "0") flags) in
      candle_action296_stratified_16_signatures :=
        !candle_action296_stratified_16_signatures @
        [string_of_int index ^ ":" ^ signature];
      print_endline
        ("CANDLE_CV_ACTION296_STRATIFIED_16_SCAN_LEAF index=" ^
         string_of_int index ^ " parent=" ^
         (if parent then "1" else "0") ^ " viable_axes=" ^
         String.concat "," (map string_of_int viable_axes) ^
         " closed=" ^ (if closed then "1" else "0") ^
         " flags=" ^ signature))
    (candle_action296_stratified_16_results ());;

let candle_action296_stratified_16_expected_signatures =
  ["33:0,1,1,1,1,1,1,1,1,1,1,1,1";
   "99:1,1,1,1,1,1,1,1,1,1,1,1,1";
   "165:1,1,1,1,1,1,1,1,1,1,1,1,1";
   "232:1,1,1,1,1,1,1,1,1,1,1,1,1";
   "298:1,1,1,1,1,1,1,1,1,1,1,1,1";
   "364:0,1,1,1,1,1,1,1,1,1,1,1,1";
   "431:0,1,1,1,1,1,1,1,1,1,1,1,1";
   "497:0,1,1,1,1,1,1,1,1,1,1,1,1";
   "563:1,1,1,1,1,1,1,1,1,1,1,1,1";
   "629:0,1,1,1,1,1,1,1,1,1,1,1,1";
   "696:0,0,0,0,0,0,0,0,0,0,0,0,1";
   "762:0,1,1,1,1,1,1,1,1,1,1,1,1";
   "828:1,1,1,1,1,1,1,1,1,1,1,1,1";
   "895:1,1,1,1,1,1,1,1,1,1,1,1,1";
   "961:0,1,1,1,1,0,1,0,1,0,0,0,1";
   "1027:0,1,1,0,0,0,0,0,0,0,0,0,1"];;

if !candle_action296_stratified_16_direct <> 7 ||
   !candle_action296_stratified_16_one_split <> 15 ||
   !candle_action296_stratified_16_hard <> [696] ||
   !candle_action296_stratified_16_signatures <>
     candle_action296_stratified_16_expected_signatures then
  failwith "action296 stratified 16: expected verdict drift";;

print_endline
  ("CANDLE_CV_ACTION296_STRATIFIED_16_SCAN_RESULT total=16 direct=" ^
   string_of_int !candle_action296_stratified_16_direct ^
   " closed_at_most_one_split=" ^
   string_of_int !candle_action296_stratified_16_one_split ^
   " hard=" ^
   String.concat "," (map string_of_int !candle_action296_stratified_16_hard) ^
   " signatures=" ^
   String.concat ";" !candle_action296_stratified_16_signatures);;
print_endline
  "CANDLE_CV_ACTION296_STRATIFIED_16_SCAN_OK DEVELOPMENT_NON_RELEASE";;
