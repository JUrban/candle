(* ========================================================================== *)
(* Sequential bounded-memory coverage scan for action-296 precision leaves. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A preceding configuration fragment supplies  *)
(* [candle_action296_chunk_scan_indices] and a label.  Each genuine parent is *)
(* prepared, scanned through depth two, reduced to ordinary policy data, and *)
(* released before the next parent.  The resulting policies are untrusted;   *)
(* a proof-producing pass must recheck every selected final cell.             *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_grouped_32_depth2_scan_algebraic.ml";;

let candle_action296_chunk_scan_axioms_before = axioms ();;

let candle_action296_chunk_scan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-chunk-scan-algebraic" ^
     " scope=chunk phase=" ^ phase ^ " event=" ^ event);;

type candle_action296_chunk_scan_branch = {
  chunk_scan_branch_number : int;
  chunk_scan_branch_viable_axes : int list;
  chunk_scan_branch_selected_axis : int option;
  chunk_scan_branch_signature : string;
};;

type candle_action296_chunk_scan_leaf = {
  chunk_scan_index : int;
  chunk_scan_depth : int option;
  chunk_scan_final_cells : int;
  chunk_scan_first_axis : int option;
  chunk_scan_depth1_signature : string;
  chunk_scan_depth2_branches : candle_action296_chunk_scan_branch list;
};;

let rec candle_action296_chunk_scan_strict_indices previous = function
  | [] -> true
  | index :: remaining ->
      index > previous && index >= 0 && index < 1061 &&
      candle_action296_chunk_scan_strict_indices index remaining;;

if candle_action296_chunk_scan_indices = [] ||
   not
     (candle_action296_chunk_scan_strict_indices
       (-1) candle_action296_chunk_scan_indices) then
  failwith "action296 chunk scan: invalid configured indices";;

let candle_action296_chunk_scan_flag_bools flags =
  map
    (fun flag ->
      match candle_action296_adaptive_grouping_flag_string flag with
      | "0" -> false
      | "1" -> true
      | _ -> failwith "action296 chunk scan: non-Boolean result")
    flags;;

let candle_action296_chunk_scan_signature flags =
  String.concat ","
    (map (fun accepted -> if accepted then "1" else "0") flags);;

let rec candle_action296_chunk_scan_drop count values =
  if count = 0 then values else
  match values with
  | [] -> failwith "action296 chunk scan: incomplete flag drop"
  | _ :: remaining ->
      candle_action296_chunk_scan_drop (count - 1) remaining;;

let candle_action296_chunk_scan_axis_pair axis flags =
  match candle_action296_chunk_scan_drop (2 * (axis - 1)) flags with
  | left :: right :: _ -> left,right
  | _ -> failwith "action296 chunk scan: axis-pair shape";;

let candle_action296_chunk_scan_viable_axes flags =
  let rec scan axis remaining =
    if axis > 6 then [] else
    match remaining with
    | left :: right :: tail ->
        let rest = scan (axis + 1) tail in
        if left && right then axis :: rest else rest
    | _ -> failwith "action296 chunk scan: child flag shape" in
  scan 1 flags;;

let candle_action296_chunk_scan_preferred_axis axes =
  if List.mem 4 axes then 4 else
  match axes with
  | axis :: _ -> axis
  | [] -> failwith "action296 chunk scan: no viable axis";;

let candle_action296_chunk_scan_best_first_axis flags =
  let axis_counts =
    map
      (fun axis ->
        let left,right = candle_action296_chunk_scan_axis_pair axis flags in
        axis,(if left then 1 else 0) + (if right then 1 else 0))
      [1;2;3;4;5;6] in
  let best_count =
    List.fold_left (fun best (_,count) -> max best count) 0 axis_counts in
  let best_axes =
    List.fold_right
      (fun (axis,count) axes ->
        if count = best_count then axis :: axes else axes)
      axis_counts [] in
  candle_action296_chunk_scan_preferred_axis best_axes;;

let candle_action296_chunk_scan_children parent =
  List.flatten
    (map
      (fun axis ->
        let left,right =
          M_verifier.split_domain
            candle_action296_plan_dimension 6 axis parent in
        [left;right])
      [1;2;3;4;5;6]);;

let candle_action296_chunk_scan_compute prepared cases =
  candle_action296_chunk_scan_flag_bools
    (candle_action296_adaptive_grouping_compute (prepared,cases));;

let candle_action296_chunk_scan_depth2_branch
    index branch prepared plan domain =
  let phase =
    "leaf-" ^ string_of_int index ^ "-depth2-branch-" ^
    string_of_int branch in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-job-preparation") "begin" in
  let cases =
    map
      (candle_action296_adaptive_grouping_case prepared plan)
      (candle_action296_chunk_scan_children domain) in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-job-preparation") "end" in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-kernel-compute") "begin" in
  let flags = candle_action296_chunk_scan_compute prepared cases in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-kernel-compute") "end" in
  let viable_axes = candle_action296_chunk_scan_viable_axes flags in
  {
    chunk_scan_branch_number = branch;
    chunk_scan_branch_viable_axes = viable_axes;
    chunk_scan_branch_selected_axis =
      if viable_axes = [] then None
      else Some (candle_action296_chunk_scan_preferred_axis viable_axes);
    chunk_scan_branch_signature =
      candle_action296_chunk_scan_signature flags;
  };;

let candle_action296_chunk_scan_leaf index =
  let parent = List.nth !candle_action296_leaf_grouping_leaves index in
  let lower,upper = candle_action296_leaf_grouping_domain_bounds parent in
  let phase = "leaf-" ^ string_of_int index in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-source-preparation") "begin" in
  let prepared =
    candle_q_dim_analytic_jet_prepare_box_six
      candle_action296_plan_prepared.function_term lower upper in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-source-preparation") "end" in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-point-plan-compilation") "begin" in
  let plan = candle_q_dim_taylor_model_point_plan_six prepared in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-point-plan-compilation") "end" in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-depth1-job-preparation") "begin" in
  let depth1_domains =
    parent :: candle_action296_chunk_scan_children parent in
  let depth1_cases =
    map
      (candle_action296_adaptive_grouping_case prepared plan)
      depth1_domains in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-depth1-job-preparation") "end" in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-depth1-kernel-compute") "begin" in
  let depth1_flags =
    candle_action296_chunk_scan_compute prepared depth1_cases in
  let _ =
    candle_action296_chunk_scan_marker
      (phase ^ "-depth1-kernel-compute") "end" in
  let parent_accepted,child_flags =
    match depth1_flags with
    | accepted :: children when length children = 12 -> accepted,children
    | _ -> failwith "action296 chunk scan: depth1 flag shape" in
  let depth1_signature =
    candle_action296_chunk_scan_signature depth1_flags in
  if parent_accepted then
    {
      chunk_scan_index = index;
      chunk_scan_depth = Some 0;
      chunk_scan_final_cells = 1;
      chunk_scan_first_axis = None;
      chunk_scan_depth1_signature = depth1_signature;
      chunk_scan_depth2_branches = [];
    }
  else
    let viable_axes =
      candle_action296_chunk_scan_viable_axes child_flags in
    if viable_axes <> [] then
      {
        chunk_scan_index = index;
        chunk_scan_depth = Some 1;
        chunk_scan_final_cells = 2;
        chunk_scan_first_axis =
          Some (candle_action296_chunk_scan_preferred_axis viable_axes);
        chunk_scan_depth1_signature = depth1_signature;
        chunk_scan_depth2_branches = [];
      }
    else
      let first_axis =
        candle_action296_chunk_scan_best_first_axis child_flags in
      let left,right =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 first_axis parent in
      let left_accepted,right_accepted =
        candle_action296_chunk_scan_axis_pair first_axis child_flags in
      let pending =
        (if left_accepted then [] else [0,left]) @
        (if right_accepted then [] else [1,right]) in
      let branches =
        map
          (fun (branch,domain) ->
            candle_action296_chunk_scan_depth2_branch
              index branch prepared plan domain)
          pending in
      let closed =
        List.for_all
          (fun branch -> branch.chunk_scan_branch_selected_axis <> None)
          branches in
      let accepted_first_children =
        (if left_accepted then 1 else 0) +
        (if right_accepted then 1 else 0) in
      {
        chunk_scan_index = index;
        chunk_scan_depth = if closed then Some 2 else None;
        chunk_scan_final_cells =
          if closed then accepted_first_children + 2 * length branches
          else 0;
        chunk_scan_first_axis = Some first_axis;
        chunk_scan_depth1_signature = depth1_signature;
        chunk_scan_depth2_branches = branches;
      };;

let candle_action296_chunk_scan_branch_string branch =
  string_of_int branch.chunk_scan_branch_number ^ ":" ^
  (match branch.chunk_scan_branch_selected_axis with
   | Some axis -> string_of_int axis
   | None -> "none") ^ ":" ^ branch.chunk_scan_branch_signature;;

let candle_action296_chunk_scan_result_line result =
  let depth =
    match result.chunk_scan_depth with
    | Some depth -> string_of_int depth
    | None -> "unresolved" in
  let first_axis =
    match result.chunk_scan_first_axis with
    | Some axis -> string_of_int axis
    | None -> "none" in
  "CANDLE_CV_ACTION296_CHUNK_SCAN_LEAF" ^
  " label=" ^ candle_action296_chunk_scan_label ^
  " index=" ^ string_of_int result.chunk_scan_index ^
  " depth=" ^ depth ^
  " final_cells=" ^ string_of_int result.chunk_scan_final_cells ^
  " first_axis=" ^ first_axis ^
  " depth1_flags=" ^ result.chunk_scan_depth1_signature ^
  " depth2=" ^
  String.concat ";"
    (map candle_action296_chunk_scan_branch_string
      result.chunk_scan_depth2_branches);;

let _ = candle_action296_chunk_scan_marker "chunk-scan" "begin";;
let candle_action296_chunk_scan_results_ref :
    candle_action296_chunk_scan_leaf list option ref = ref None;;
let _ =
  candle_action296_chunk_scan_results_ref :=
    Some
      (map
        (fun index ->
          let result = candle_action296_chunk_scan_leaf index in
          print_endline (candle_action296_chunk_scan_result_line result);
          result)
        candle_action296_chunk_scan_indices);;
let _ = candle_action296_chunk_scan_marker "chunk-scan" "end";;

let candle_action296_chunk_scan_results () =
  match !candle_action296_chunk_scan_results_ref with
  | Some results -> results
  | None -> failwith "action296 chunk scan: missing results";;

let candle_action296_chunk_scan_direct =
  List.fold_left
    (fun count result ->
      if result.chunk_scan_depth = Some 0 then count + 1 else count)
    0 (candle_action296_chunk_scan_results ());;

let candle_action296_chunk_scan_depth1 =
  List.fold_left
    (fun count result ->
      if result.chunk_scan_depth = Some 1 then count + 1 else count)
    0 (candle_action296_chunk_scan_results ());;

let candle_action296_chunk_scan_depth2 =
  List.fold_left
    (fun count result ->
      if result.chunk_scan_depth = Some 2 then count + 1 else count)
    0 (candle_action296_chunk_scan_results ());;

let candle_action296_chunk_scan_unresolved =
  List.fold_left
    (fun count result ->
      if result.chunk_scan_depth = None then count + 1 else count)
    0 (candle_action296_chunk_scan_results ());;

let candle_action296_chunk_scan_final_cells =
  List.fold_left
    (fun count result -> count + result.chunk_scan_final_cells)
    0 (candle_action296_chunk_scan_results ());;

let candle_action296_chunk_scan_axioms_after = axioms ();;

if length (candle_action296_chunk_scan_results ()) <>
     length candle_action296_chunk_scan_indices ||
   candle_action296_chunk_scan_direct +
     candle_action296_chunk_scan_depth1 +
     candle_action296_chunk_scan_depth2 +
     candle_action296_chunk_scan_unresolved <>
       length candle_action296_chunk_scan_indices ||
   length candle_action296_chunk_scan_axioms_after <>
     length candle_action296_chunk_scan_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_chunk_scan_axioms_before)
       candle_action296_chunk_scan_axioms_after) then
  failwith "action296 chunk scan: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_CHUNK_SCAN_RESULT" ^
   " label=" ^ candle_action296_chunk_scan_label ^
   " total=" ^ string_of_int (length candle_action296_chunk_scan_indices) ^
   " direct=" ^ string_of_int candle_action296_chunk_scan_direct ^
   " depth1=" ^ string_of_int candle_action296_chunk_scan_depth1 ^
   " depth2=" ^ string_of_int candle_action296_chunk_scan_depth2 ^
   " unresolved=" ^ string_of_int candle_action296_chunk_scan_unresolved ^
   " final_cells=" ^ string_of_int candle_action296_chunk_scan_final_cells);;
print_endline
  "CANDLE_CV_ACTION296_CHUNK_SCAN_OK DEVELOPMENT_NON_RELEASE";;
