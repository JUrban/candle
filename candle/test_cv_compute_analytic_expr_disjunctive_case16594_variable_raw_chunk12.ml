(* Recheck the first raw batch that rejected under the misindexed plan. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_chunk12 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let rec candle_disjunctive_case16594_raw_chunk12_drop count items =
  if count = 0 then items
  else
    match items with
    | [] -> failwith "case16594 raw chunk12: short drop"
    | _ :: tail ->
        candle_disjunctive_case16594_raw_chunk12_drop (count - 1) tail;;

let rec candle_disjunctive_case16594_raw_chunk12_take count items =
  if count = 0 then []
  else
    match items with
    | [] -> failwith "case16594 raw chunk12: short take"
    | head :: tail ->
        head ::
        candle_disjunctive_case16594_raw_chunk12_take (count - 1) tail;;

let _ =
  let cells =
    candle_disjunctive_case16594_raw_chunk12_take 32
      (candle_disjunctive_case16594_raw_chunk12_drop 384
        candle_disjunctive_case16594_variable_raw_plan_cells) in
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-raw-chunk12" ^
         " phase=" ^ event));
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
      candle_disjunctive_case16594_engine_state.family_engine_prepared
      cells in
  let theorem = result.variable_raw_accept_theorem in
  let axioms_after = axioms () in
  if length cells <> 32 || hyp theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before)
         axioms_after) then
    failwith "case16594 raw chunk12: final validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_CHUNK12_RESULT" ^
     " planned_cells=384-415 cells=32 accepts=true assumptions=0" ^
     " theorem_digest=" ^
     Digest.to_hex (Digest.string (string_of_thm theorem)));
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_CHUNK12_OK DEVELOPMENT_NON_RELEASE";;

end;;
