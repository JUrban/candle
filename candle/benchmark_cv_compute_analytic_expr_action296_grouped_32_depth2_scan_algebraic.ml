(* ========================================================================== *)
(* Depth-two scan for the three genuine leaves not closed by one split.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Choose the best simple first split found by   *)
(* the pinned one-split scan, retain any accepted child, and scan every axis  *)
(* only below the five remaining rejected children.                          *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_grouped_32_split_scan_algebraic.ml";;

let candle_action296_grouped_32_depth2_scan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-grouped-32-depth2-scan-algebraic" ^
     " scope=hard-leaves-20-26-27 phase=" ^ phase ^ " event=" ^ event);;

type candle_action296_grouped_32_depth2_intermediate = {
  grouped_32_depth2_parent_index : int;
  grouped_32_depth2_branch : int;
  grouped_32_depth2_domain : thm;
};;

type candle_action296_grouped_32_depth2_group_six = {
  grouped_32_depth2_prepared : candle_q_dim_analytic_jet_prepared_six;
  grouped_32_depth2_plan : candle_q_dim_taylor_model_point_plan_six;
  grouped_32_depth2_intermediates :
    candle_action296_grouped_32_depth2_intermediate list;
};;

type candle_action296_grouped_32_depth2_job_six = {
  grouped_32_depth2_job_prepared : candle_q_dim_analytic_jet_prepared_six;
  grouped_32_depth2_job_intermediates :
    candle_action296_grouped_32_depth2_intermediate list;
  grouped_32_depth2_job_cases :
    candle_action296_adaptive_grouping_case_six list;
};;

let candle_action296_grouped_32_depth2_policies = [(20,4);(26,3);(27,4)];;

let rec candle_action296_grouped_32_depth2_find_result index = function
  | [] -> failwith "action296 grouped 32 depth2: parent result not found"
  | (candidate,parent,flags) :: remaining ->
      if candidate = index then parent,flags
      else candle_action296_grouped_32_depth2_find_result index remaining;;

let rec candle_action296_grouped_32_depth2_drop count items =
  if count = 0 then items else
  match items with
  | [] -> failwith "action296 grouped 32 depth2: incomplete flag drop"
  | _ :: remaining ->
      candle_action296_grouped_32_depth2_drop (count - 1) remaining;;

let candle_action296_grouped_32_depth2_first_children index axis =
  let parent,raw_flags =
    candle_action296_grouped_32_depth2_find_result index
      (candle_action296_grouped_32_split_scan_results ()) in
  let left,right =
    M_verifier.split_domain candle_action296_plan_dimension 6 axis parent in
  let axis_flags =
    candle_action296_grouped_32_depth2_drop (2 * (axis - 1))
      (candle_action296_grouped_32_split_scan_bools raw_flags) in
  match axis_flags with
  | left_flag :: right_flag :: _ ->
      (if left_flag then [] else
         [{grouped_32_depth2_parent_index = index;
           grouped_32_depth2_branch = 0;
           grouped_32_depth2_domain = left}]) @
      (if right_flag then [] else
         [{grouped_32_depth2_parent_index = index;
           grouped_32_depth2_branch = 1;
           grouped_32_depth2_domain = right}])
  | _ -> failwith "action296 grouped 32 depth2: first-child flag shape";;

let candle_action296_grouped_32_depth2_intermediates =
  List.flatten
    (map
      (fun (index,axis) ->
        candle_action296_grouped_32_depth2_first_children index axis)
      candle_action296_grouped_32_depth2_policies);;

let rec candle_action296_grouped_32_depth2_parent_list_has index = function
  | [] -> false
  | (candidate,_) :: remaining ->
      if candidate = index then true
      else candle_action296_grouped_32_depth2_parent_list_has index remaining;;

let candle_action296_grouped_32_depth2_parent_in selected index =
  candle_action296_grouped_32_depth2_parent_list_has index
    selected.grouped_32_split_scan_parents;;

let candle_action296_grouped_32_depth2_groups =
  List.fold_left
    (fun groups selected ->
      let intermediates =
        List.filter
          (fun intermediate ->
            candle_action296_grouped_32_depth2_parent_in selected
              intermediate.grouped_32_depth2_parent_index)
          candle_action296_grouped_32_depth2_intermediates in
      if intermediates = [] then groups else
      groups @
        [{grouped_32_depth2_prepared =
            selected.grouped_32_split_scan_prepared;
          grouped_32_depth2_plan = selected.grouped_32_split_scan_plan;
          grouped_32_depth2_intermediates = intermediates}])
    [] (candle_action296_grouped_32_split_scan_selected ());;

let _ =
  if length candle_action296_grouped_32_depth2_intermediates <> 5 ||
     length candle_action296_grouped_32_depth2_groups <> 2 then
    failwith "action296 grouped 32 depth2: selected shape";;

let _ =
  candle_action296_grouped_32_depth2_scan_marker
    "depth2-per-box-preparation" "begin";;
let candle_action296_grouped_32_depth2_jobs_ref :
    candle_action296_grouped_32_depth2_job_six list option ref = ref None;;
let _ =
  candle_action296_grouped_32_depth2_jobs_ref :=
    Some
      (map
        (fun group ->
          let child_domains =
            List.flatten
              (map
                (fun intermediate ->
                  candle_action296_grouped_32_split_scan_children
                    intermediate.grouped_32_depth2_domain)
                group.grouped_32_depth2_intermediates) in
          {
            grouped_32_depth2_job_prepared = group.grouped_32_depth2_prepared;
            grouped_32_depth2_job_intermediates =
              group.grouped_32_depth2_intermediates;
            grouped_32_depth2_job_cases =
              map
                (candle_action296_adaptive_grouping_case
                  group.grouped_32_depth2_prepared
                  group.grouped_32_depth2_plan)
                child_domains;
          })
        candle_action296_grouped_32_depth2_groups);;
let _ =
  candle_action296_grouped_32_depth2_scan_marker
    "depth2-per-box-preparation" "end";;

let candle_action296_grouped_32_depth2_jobs () =
  match !candle_action296_grouped_32_depth2_jobs_ref with
  | Some jobs -> jobs
  | None -> failwith "action296 grouped 32 depth2: missing jobs";;

let _ =
  candle_action296_grouped_32_depth2_scan_marker
    "depth2-kernel-compute" "begin";;
let candle_action296_grouped_32_depth2_group_flags_ref :
    term list list option ref = ref None;;
let _ =
  candle_action296_grouped_32_depth2_group_flags_ref :=
    Some
      (map
        (fun job ->
          candle_action296_adaptive_grouping_compute
            (job.grouped_32_depth2_job_prepared,
             job.grouped_32_depth2_job_cases))
        (candle_action296_grouped_32_depth2_jobs ()));;
let _ =
  candle_action296_grouped_32_depth2_scan_marker
    "depth2-kernel-compute" "end";;

let candle_action296_grouped_32_depth2_group_flags () =
  match !candle_action296_grouped_32_depth2_group_flags_ref with
  | Some flags -> flags
  | None -> failwith "action296 grouped 32 depth2: missing flags";;

let rec candle_action296_grouped_32_depth2_results intermediates flags =
  match intermediates with
  | [] ->
      if flags = [] then []
      else failwith "action296 grouped 32 depth2: trailing flags"
  | intermediate :: remaining ->
      let child_flags,remaining_flags =
        candle_action296_leaf_grouping_take 12 flags in
      (intermediate,child_flags) ::
      candle_action296_grouped_32_depth2_results
        remaining remaining_flags;;

let candle_action296_grouped_32_depth2_results_ref :
    (candle_action296_grouped_32_depth2_intermediate * term list) list
      option ref = ref None;;
let _ =
  candle_action296_grouped_32_depth2_results_ref :=
    Some
      (List.flatten
        (candle_action296_grouped_32_split_scan_map2
          (fun job flags ->
            candle_action296_grouped_32_depth2_results
              job.grouped_32_depth2_job_intermediates flags)
          (candle_action296_grouped_32_depth2_jobs ())
          (candle_action296_grouped_32_depth2_group_flags ())));;

let candle_action296_grouped_32_depth2_results () =
  match !candle_action296_grouped_32_depth2_results_ref with
  | Some results -> results
  | None -> failwith "action296 grouped 32 depth2: missing results";;

let candle_action296_grouped_32_depth2_closed_intermediates = ref 0;;
let candle_action296_grouped_32_depth2_signatures : string list ref = ref [];;
let _ =
  List.iter
    (fun (intermediate,raw_flags) ->
      let flags =
        candle_action296_grouped_32_split_scan_bools raw_flags in
      let viable_axes =
        candle_action296_grouped_32_split_scan_viable_axes flags in
      let accepts =
        List.fold_left
          (fun count flag -> if flag then count + 1 else count) 0 flags in
      if viable_axes <> [] then
        candle_action296_grouped_32_depth2_closed_intermediates :=
          !candle_action296_grouped_32_depth2_closed_intermediates + 1;
      let signature =
        string_of_int intermediate.grouped_32_depth2_parent_index ^ "." ^
        string_of_int intermediate.grouped_32_depth2_branch ^ ":" ^
        String.concat ","
          (map (fun flag -> if flag then "1" else "0") flags) in
      candle_action296_grouped_32_depth2_signatures :=
        !candle_action296_grouped_32_depth2_signatures @ [signature];
      print_endline
        ("CANDLE_CV_ACTION296_GROUPED_32_DEPTH2_SCAN_NODE" ^
         " parent=" ^
         string_of_int intermediate.grouped_32_depth2_parent_index ^
         " branch=" ^ string_of_int intermediate.grouped_32_depth2_branch ^
         " child_accepts=" ^ string_of_int accepts ^ "/12" ^
         " viable_axes=" ^
         String.concat "," (map string_of_int viable_axes) ^
         " flags=" ^
         String.concat ","
           (map (fun flag -> if flag then "1" else "0") flags)))
    (candle_action296_grouped_32_depth2_results ());;

let candle_action296_grouped_32_depth2_expected_signatures =
  ["20.0:1,1,1,1,1,1,0,1,1,1,1,1";
   "20.1:1,1,1,1,1,1,1,1,1,1,1,1";
   "26.1:1,1,1,1,1,1,1,1,1,1,1,1";
   "27.0:1,1,1,1,1,1,1,1,1,1,1,1";
   "27.1:1,1,1,1,1,1,1,1,1,1,1,1"];;

if !candle_action296_grouped_32_depth2_signatures <>
     candle_action296_grouped_32_depth2_expected_signatures ||
   !candle_action296_grouped_32_depth2_closed_intermediates <> 5 then
  failwith "action296 grouped 32 depth2: expected verdict drift";;

print_endline
  ("CANDLE_CV_ACTION296_GROUPED_32_DEPTH2_SCAN_RESULT" ^
   " hard_parents=3 rejected_first_children=5 closed_intermediates=" ^
   string_of_int !candle_action296_grouped_32_depth2_closed_intermediates);;
print_endline
  "CANDLE_CV_ACTION296_GROUPED_32_DEPTH2_SCAN_OK DEVELOPMENT_NON_RELEASE";;
