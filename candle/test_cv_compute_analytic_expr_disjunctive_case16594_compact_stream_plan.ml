(* Computation-free validation of all case-16594 streaming token segments. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_compact_stack_complete_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_plan = struct

open Candle_cv_analytic_expr_disjunctive_case16594_compact_stack_complete_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan;;

let _ =
  let chunks =
    candle_disjunctive_case16594_compact_complete_split_chunks 4
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let tokens =
    dest_list (candle_disjunctive_case16594_compact_token_plan ()) in
  let rec validate index leaves glues largest remaining_tokens = function
    | [] ->
        if remaining_tokens <> [] then
          failwith "case16594 compact stream plan: remaining tokens";
        index,leaves,glues,largest
    | cells :: remaining_chunks ->
        let segment,after_segment =
          candle_disjunctive_case16594_compact_complete_take_token_segment
            (length cells) [] remaining_tokens in
        let segment_leaves =
          length
            (filter
              (fun token ->
                aconv token candle_disjunctive_case16594_compact_token_leaf)
              segment) in
        let segment_glues = length segment - segment_leaves in
        if segment_leaves <> length cells then
          failwith "case16594 compact stream plan: leaf mismatch";
        validate (index + 1) (leaves + segment_leaves)
          (glues + segment_glues) (max largest (length segment))
          after_segment remaining_chunks in
  let segments,leaves,glues,largest =
    validate 0 0 0 0 tokens chunks in
  if segments <> 219 || leaves <> 875 || glues <> 874 then
    failwith "case16594 compact stream plan: total mismatch";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STREAM_PLAN_RESULT" ^
     " segments=" ^ string_of_int segments ^
     " leaf_tokens=" ^ string_of_int leaves ^
     " glue_tokens=" ^ string_of_int glues ^
     " largest_segment_tokens=" ^ string_of_int largest);
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STREAM_PLAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
