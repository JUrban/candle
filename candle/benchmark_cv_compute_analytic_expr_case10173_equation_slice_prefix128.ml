(* ========================================================================== *)
(* Full versus reachability-sliced Kernel.compute equations on genuine jobs. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  Both lanes evaluate the  *)
(* identical compact whole-expression call and must return the same closed   *)
(* theorem.  Slicing changes only the host-prepared equation bundle.          *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_compact_prefix128.ml";;
needs "candle/cv_compute_equation_slice.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_equation_slice_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_case10173_compact_compute;;
open Candle_cv_compute_equation_slice;;
open Benchmark_cv_compute_analytic_expr_case10173_compact_prefix128;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event -> print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-equation-slice-prefix128 phase=" ^
       event));
  let axioms_before = axioms () in
  candle_q_dim_analytic_jet_profile_event "preparation-begin";
  let plan,encoded_jobs = candle_case10173_compact_prepare () in
  let call = list_mk_comb
    (`candle_cv_case10173_compact_raw_jobs_check`,
     [plan;encoded_jobs;candle_case10173_compact_roots]) in
  let sliced_equations = candle_cv_compute_equation_slice
    candle_cv_case10173_compact_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event "preparation-end";
  print_endline
    ("CANDLE_CV_CASE10173_EQUATION_SLICE_COUNTS full=" ^
     string_of_int (length candle_cv_case10173_compact_compute_eqs) ^
     " sliced=" ^ string_of_int (length sliced_equations));
  let run label equations =
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
    let theorem = candle_q_dim_analytic_jet_compute equations call in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-end");
    if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) ||
       not (aconv (rand (concl theorem)) `Cexp_num 1`)
    then failwith ("case10173 equation slice: malformed " ^ label);
    theorem in
  let full_1 = run "full-1" candle_cv_case10173_compact_compute_eqs in
  let sliced_1 = run "sliced-1" sliced_equations in
  let sliced_2 = run "sliced-2" sliced_equations in
  let full_2 = run "full-2" candle_cv_case10173_compact_compute_eqs in
  if not (aconv (rand (concl full_1)) (rand (concl sliced_1))) ||
     not (aconv (rand (concl sliced_1)) (rand (concl sliced_2))) ||
     not (aconv (rand (concl sliced_2)) (rand (concl full_2))) ||
     length (axioms ()) <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) (axioms ()))
  then failwith "case10173 equation slice: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_EQUATION_SLICE_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 full_repeats=2 sliced_repeats=2 result=1 exact_match=1 assumptions=0 axiom_growth=0";;

end;;
