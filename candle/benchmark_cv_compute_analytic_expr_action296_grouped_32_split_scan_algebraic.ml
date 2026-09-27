(* ========================================================================== *)
(* One-split coverage scan for rejected leaves in the genuine 32-leaf batch. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Reuse the exact authenticated source boxes    *)
(* and point plans from the whole-leaf discriminator.  For each rejected     *)
(* parent, check both children of all six coordinate splits.                  *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_grouped_32_algebraic.ml";;

let candle_action296_grouped_32_split_scan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-grouped-32-split-scan-algebraic" ^
     " scope=rejected-whole-leaves phase=" ^ phase ^ " event=" ^ event);;

type candle_action296_grouped_32_split_scan_selected_six = {
  grouped_32_split_scan_prepared :
    candle_q_dim_analytic_jet_prepared_six;
  grouped_32_split_scan_plan :
    candle_q_dim_taylor_model_point_plan_six;
  grouped_32_split_scan_parents : (int * thm) list;
};;

type candle_action296_grouped_32_split_scan_job_six = {
  grouped_32_split_scan_job_prepared :
    candle_q_dim_analytic_jet_prepared_six;
  grouped_32_split_scan_job_parents : (int * thm) list;
  grouped_32_split_scan_job_cases :
    candle_action296_adaptive_grouping_case_six list;
};;

let rec candle_action296_grouped_32_split_scan_rejected
    index domains flags =
  match domains,flags with
  | [],[] -> []
  | domain :: remaining_domains,flag :: remaining_flags ->
      let remaining =
        candle_action296_grouped_32_split_scan_rejected
          (index + 1) remaining_domains remaining_flags in
      if candle_action296_adaptive_grouping_flag_string flag = "0" then
        (index,domain) :: remaining
      else remaining
  | _ -> failwith "action296 grouped 32 split scan: group flag shape";;

let rec candle_action296_grouped_32_split_scan_select
    offset planned flags =
  match planned with
  | [] ->
      if flags = [] then []
      else failwith "action296 grouped 32 split scan: trailing flags"
  | (domains,prepared,plan) :: remaining_planned ->
      let group_flags,remaining_flags =
        candle_action296_leaf_grouping_take (length domains) flags in
      {
        grouped_32_split_scan_prepared = prepared;
        grouped_32_split_scan_plan = plan;
        grouped_32_split_scan_parents =
          candle_action296_grouped_32_split_scan_rejected
            offset domains group_flags;
      } ::
      candle_action296_grouped_32_split_scan_select
        (offset + length domains) remaining_planned remaining_flags;;

let candle_action296_grouped_32_split_scan_selected_ref :
    candle_action296_grouped_32_split_scan_selected_six list option ref =
  ref None;;
let _ =
  candle_action296_grouped_32_split_scan_selected_ref :=
    Some
      (candle_action296_grouped_32_split_scan_select 0
        (candle_action296_grouped_32_plans ())
        (candle_action296_grouped_32_flags ()));;

let candle_action296_grouped_32_split_scan_selected () =
  match !candle_action296_grouped_32_split_scan_selected_ref with
  | Some selected -> selected
  | None -> failwith "action296 grouped 32 split scan: missing selection";;

let candle_action296_grouped_32_split_scan_children parent =
  List.flatten
    (map
      (fun axis ->
        let left,right =
          M_verifier.split_domain
            candle_action296_plan_dimension 6 axis parent in
        [left;right])
      [1;2;3;4;5;6]);;

let _ =
  candle_action296_grouped_32_split_scan_marker
    "retry-per-box-preparation" "begin";;
let candle_action296_grouped_32_split_scan_jobs_ref :
    candle_action296_grouped_32_split_scan_job_six list option ref =
  ref None;;
let _ =
  candle_action296_grouped_32_split_scan_jobs_ref :=
    Some
      (map
        (fun selected ->
          let prepared = selected.grouped_32_split_scan_prepared and
              plan = selected.grouped_32_split_scan_plan in
          let child_domains =
            List.flatten
              (map
                (fun (_,parent) ->
                  candle_action296_grouped_32_split_scan_children parent)
                selected.grouped_32_split_scan_parents) in
          {
            grouped_32_split_scan_job_prepared = prepared;
            grouped_32_split_scan_job_parents =
              selected.grouped_32_split_scan_parents;
            grouped_32_split_scan_job_cases =
              map
                (candle_action296_adaptive_grouping_case prepared plan)
                child_domains;
          })
        (candle_action296_grouped_32_split_scan_selected ()));;
let _ =
  candle_action296_grouped_32_split_scan_marker
    "retry-per-box-preparation" "end";;

let candle_action296_grouped_32_split_scan_jobs () =
  match !candle_action296_grouped_32_split_scan_jobs_ref with
  | Some jobs -> jobs
  | None -> failwith "action296 grouped 32 split scan: missing jobs";;

let _ =
  candle_action296_grouped_32_split_scan_marker "retry-kernel-compute" "begin";;
let candle_action296_grouped_32_split_scan_group_flags_ref :
    term list list option ref = ref None;;
let _ =
  candle_action296_grouped_32_split_scan_group_flags_ref :=
    Some
      (map
        (fun job ->
          candle_action296_adaptive_grouping_compute
            (job.grouped_32_split_scan_job_prepared,
             job.grouped_32_split_scan_job_cases))
        (candle_action296_grouped_32_split_scan_jobs ()));;
let _ =
  candle_action296_grouped_32_split_scan_marker "retry-kernel-compute" "end";;

let candle_action296_grouped_32_split_scan_group_flags () =
  match !candle_action296_grouped_32_split_scan_group_flags_ref with
  | Some flags -> flags
  | None -> failwith "action296 grouped 32 split scan: missing flags";;

let rec candle_action296_grouped_32_split_scan_results parents flags =
  match parents with
  | [] ->
      if flags = [] then []
      else failwith "action296 grouped 32 split scan: trailing child flags"
  | (index,parent) :: remaining ->
      let child_flags,remaining_flags =
        candle_action296_leaf_grouping_take 12 flags in
      (index,parent,child_flags) ::
      candle_action296_grouped_32_split_scan_results
        remaining remaining_flags;;

let rec candle_action296_grouped_32_split_scan_map2 action left right =
  match left,right with
  | [],[] -> []
  | left_head :: left_tail,right_head :: right_tail ->
      action left_head right_head ::
      candle_action296_grouped_32_split_scan_map2 action left_tail right_tail
  | _ -> failwith "action296 grouped 32 split scan: result group shape";;

let candle_action296_grouped_32_split_scan_results_ref :
    (int * thm * term list) list option ref = ref None;;
let _ =
  candle_action296_grouped_32_split_scan_results_ref :=
    Some
      (List.flatten
        (candle_action296_grouped_32_split_scan_map2
          (fun job flags ->
            candle_action296_grouped_32_split_scan_results
              job.grouped_32_split_scan_job_parents flags)
          (candle_action296_grouped_32_split_scan_jobs ())
          (candle_action296_grouped_32_split_scan_group_flags ())));;

let candle_action296_grouped_32_split_scan_results () =
  match !candle_action296_grouped_32_split_scan_results_ref with
  | Some results -> results
  | None -> failwith "action296 grouped 32 split scan: missing results";;

let candle_action296_grouped_32_split_scan_bools flags =
  map
    (fun flag ->
      match candle_action296_adaptive_grouping_flag_string flag with
      | "0" -> false
      | "1" -> true
      | _ -> failwith "action296 grouped 32 split scan: Boolean conversion")
    flags;;

let candle_action296_grouped_32_split_scan_viable_axes flags =
  let rec scan axis remaining =
    if axis > 6 then [] else
    match remaining with
    | left :: right :: tail ->
        let rest = scan (axis + 1) tail in
        if left && right then axis :: rest else rest
    | _ -> failwith "action296 grouped 32 split scan: child flag shape" in
  scan 1 flags;;

let candle_action296_grouped_32_split_scan_closed = ref 0;;
let candle_action296_grouped_32_split_scan_child_accepts = ref 0;;
let candle_action296_grouped_32_split_scan_signatures : string list ref =
  ref [];;
let _ =
  if length (candle_action296_grouped_32_split_scan_results ()) <> 23 then
    failwith "action296 grouped 32 split scan: rejected-parent cardinality";
  List.iter
    (fun (index,_,raw_flags) ->
      let flags =
        candle_action296_grouped_32_split_scan_bools raw_flags in
      let viable_axes =
        candle_action296_grouped_32_split_scan_viable_axes flags in
      let accepts =
        List.fold_left
          (fun count flag -> if flag then count + 1 else count) 0 flags in
      candle_action296_grouped_32_split_scan_child_accepts :=
        !candle_action296_grouped_32_split_scan_child_accepts + accepts;
      if viable_axes <> [] then
        candle_action296_grouped_32_split_scan_closed :=
          !candle_action296_grouped_32_split_scan_closed + 1;
      let flag_string =
        String.concat ","
          (map (fun flag -> if flag then "1" else "0") flags) in
      candle_action296_grouped_32_split_scan_signatures :=
        !candle_action296_grouped_32_split_scan_signatures @
        [string_of_int index ^ ":" ^ flag_string];
      print_endline
        ("CANDLE_CV_ACTION296_GROUPED_32_SPLIT_SCAN_LEAF" ^
         " index=" ^ string_of_int index ^
         " child_accepts=" ^ string_of_int accepts ^ "/12" ^
         " viable_axes=" ^
         String.concat "," (map string_of_int viable_axes) ^
         " flags=" ^ flag_string))
    (candle_action296_grouped_32_split_scan_results ());;

let candle_action296_grouped_32_split_scan_expected_signatures =
  ["0:1,1,0,0,0,0,1,1,1,1,1,1";
   "1:0,1,0,0,0,0,1,1,0,1,1,1";
   "2:0,1,0,0,0,0,1,1,1,1,0,1";
   "3:1,1,1,1,1,1,1,1,1,1,1,1";
   "8:1,1,1,1,1,1,1,1,1,1,1,1";
   "9:1,1,0,1,1,1,1,1,1,1,1,1";
   "12:0,1,0,0,1,1,1,1,0,1,0,0";
   "13:1,1,1,1,1,1,1,1,1,1,1,1";
   "16:0,1,1,0,0,1,1,1,1,1,1,1";
   "17:1,1,1,1,1,1,1,1,1,1,1,1";
   "18:0,1,0,0,1,1,1,1,0,1,0,1";
   "19:0,1,0,0,1,1,0,1,0,0,0,1";
   "20:0,0,0,0,0,0,0,0,0,0,0,0";
   "21:0,0,1,1,1,1,0,1,0,1,0,1";
   "22:1,1,1,1,1,1,1,1,1,1,1,1";
   "23:1,1,1,1,1,1,1,1,1,1,1,1";
   "24:0,1,0,0,1,1,1,1,0,0,0,0";
   "25:0,1,0,0,1,1,1,1,0,0,0,0";
   "26:0,0,0,0,1,0,0,0,0,0,0,0";
   "27:0,0,0,0,0,0,0,0,0,0,0,0";
   "28:0,1,1,1,1,1,1,1,0,1,0,0";
   "30:1,1,1,1,1,1,1,1,1,1,1,1";
   "31:0,0,1,1,0,1,0,1,0,0,0,0"];;

if !candle_action296_grouped_32_split_scan_signatures <>
     candle_action296_grouped_32_split_scan_expected_signatures ||
   !candle_action296_grouped_32_split_scan_closed <> 20 ||
   !candle_action296_grouped_32_split_scan_child_accepts <> 172 then
  failwith "action296 grouped 32 split scan: expected verdict drift";;

print_endline
  ("CANDLE_CV_ACTION296_GROUPED_32_SPLIT_SCAN_RESULT" ^
   " rejected_parents=23 one_split_closed=" ^
   string_of_int !candle_action296_grouped_32_split_scan_closed ^
   " child_accepts=" ^
   string_of_int !candle_action296_grouped_32_split_scan_child_accepts ^
   "/276");;
print_endline
  "CANDLE_CV_ACTION296_GROUPED_32_SPLIT_SCAN_OK DEVELOPMENT_NON_RELEASE";;
