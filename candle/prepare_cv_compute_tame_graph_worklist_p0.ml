(* Stable prepared state and compact result decoder for p=0 worklist probes. *)

needs "candle/test_cv_compute_tame_graph_worklist.ml";;

let candle_cv_tame_worklist_dest_pair tm =
  dest_binary "Cexp_pair" tm;;

let candle_cv_tame_worklist_dest_num tm =
  let constructor,args = strip_comb tm in
  if not (aconv constructor `Cexp_num`) then
    failwith "tame worklist decoder: expected Cexp_num"
  else match args with
    [value] -> dest_small_numeral value
  | _ -> failwith "tame worklist decoder: malformed Cexp_num";;

let rec candle_cv_tame_worklist_term_list_length tm =
  if aconv tm `Cexp_num 0` then 0
  else
    let _,rest = candle_cv_tame_worklist_dest_pair tm in
    1 + candle_cv_tame_worklist_term_list_length rest;;

let candle_cv_tame_worklist_decode_stats stats =
  let visited,tail1 = candle_cv_tame_worklist_dest_pair stats in
  let final_visits,tail2 = candle_cv_tame_worklist_dest_pair tail1 in
  let stage0_children,tail3 = candle_cv_tame_worklist_dest_pair tail2 in
  let retained_children,tail4 = candle_cv_tame_worklist_dest_pair tail3 in
  let final_pruned,maximum_frontier =
    candle_cv_tame_worklist_dest_pair tail4 in
  (candle_cv_tame_worklist_dest_num visited,
   candle_cv_tame_worklist_dest_num final_visits,
   candle_cv_tame_worklist_dest_num stage0_children,
   candle_cv_tame_worklist_dest_num retained_children,
   candle_cv_tame_worklist_dest_num final_pruned,
   candle_cv_tame_worklist_dest_num maximum_frontier);;

let candle_cv_tame_worklist_run_p0_prefix fuel =
  let fuel_term = mk_comb (`Cexp_num`,mk_small_numeral fuel) in
  let workload = list_mk_comb
    (`candle_cv_tame_worklist_run`,
     [fuel_term;
      candle_cv_tame_transition_candidates_p0;
      candle_cv_tame_p0_expected]) in
  let theorem = Candle_cv_tame_graph_worklist.candle_cv_tame_worklist_eval
    workload in
  let result = rand (concl theorem) in
  let frontier,tail = candle_cv_tame_worklist_dest_pair result in
  let finals,stats = candle_cv_tame_worklist_dest_pair tail in
  let visited,final_visits,stage0_children,retained_children,
      final_pruned,maximum_frontier =
    candle_cv_tame_worklist_decode_stats stats in
  let frontier_count = candle_cv_tame_worklist_term_list_length frontier in
  let final_count = candle_cv_tame_worklist_term_list_length finals in
  print_endline
    ("CANDLE_CV_TAME_P0_WORKLIST_PREFIX_OK DEVELOPMENT_NON_RELEASE fuel=" ^
     string_of_int fuel ^
     " visited=" ^ string_of_int visited ^
     " final_visits=" ^ string_of_int final_visits ^
     " stage0_children=" ^ string_of_int stage0_children ^
     " retained_children=" ^ string_of_int retained_children ^
     " final_pruned=" ^ string_of_int final_pruned ^
     " maximum_frontier=" ^ string_of_int maximum_frontier ^
     " frontier=" ^ string_of_int frontier_count ^
     " finals=" ^ string_of_int final_count ^
     " complete=" ^ (if frontier_count = 0 then "true" else "false"));
  theorem;;

let _ = print_endline
  "CANDLE_CV_TAME_P0_WORKLIST_PREPARED_READY DEVELOPMENT_NON_RELEASE";;
