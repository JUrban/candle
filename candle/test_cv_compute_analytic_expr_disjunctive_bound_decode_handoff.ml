(* Exercise one complete fixed-outer theorem handoff after data-only proposal  *)
(* decoding.  Normal numerical rejection is skipped until an accepted leaf.  *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_bound_decode_handoff = struct

open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan;;

let _ =
  let rec first_accepted attempts prepared point_plan = function
    | [] -> failwith "data-only bound decoder handoff: no accepted sample"
    | (record,index,selected,domain)::remaining ->
        try
          let theorem =
            candle_disjunctive_fixed_outer_attempt
              prepared point_plan 5 4 domain in
          attempts + 1,record,index,selected,theorem
        with Failure _ ->
          first_accepted (attempts + 1) prepared point_plan remaining in
  let axioms_before = axioms () in
  print_endline
    "CANDLE_CV_BOUND_DECODE_HANDOFF_BEGIN DEVELOPMENT_NON_RELEASE";
  let attempts,record,index,selected,theorem =
    try
      first_accepted 0
        candle_disjunctive_next_batch_prepared0
        candle_disjunctive_next_batch_point_plan0
        candle_disjunctive_float_point_sample0
    with Failure _ ->
      first_accepted (length candle_disjunctive_float_point_sample0)
        candle_disjunctive_next_batch_prepared1
        candle_disjunctive_next_batch_point_plan1
        candle_disjunctive_float_point_sample1 in
  let axioms_after = axioms () in
  if hyp theorem <> [] ||
     (selected <> 0 && selected <> 1) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before)
         axioms_after) then
    failwith "data-only bound decoder handoff: validation failed";
  print_endline
    ("CANDLE_CV_BOUND_DECODE_HANDOFF_OK DEVELOPMENT_NON_RELEASE" ^
     " attempts=" ^ string_of_int attempts ^
     " record=" ^ string_of_int record ^
     " index=" ^ string_of_int index ^
     " function=" ^ string_of_int selected ^
     " assumptions=0 axiom_growth=0");;

end;;
