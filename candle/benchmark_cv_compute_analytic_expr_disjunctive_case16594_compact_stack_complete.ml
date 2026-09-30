(* Complete case-16594 benchmark from a compact-stack support checkpoint. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_compact_stack_complete_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_stack_complete = struct

open Candle_cv_analytic_expr_disjunctive_case16594_compact_stack_complete_prove;;

let _ =
  let _ = candle_disjunctive_case16594_compact_stack_complete_prove () in
  ();;

end;;
