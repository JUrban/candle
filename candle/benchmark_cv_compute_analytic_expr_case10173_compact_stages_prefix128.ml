(* ========================================================================== *)
(* Stage profile for the compact 128-job case-10173 checker.                 *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.                            *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_compact_prefix128.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_compact_stages_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_case10173_compact_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_compact_prefix128;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event -> print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-compact-stages-prefix128 phase=" ^
       event));
  let axioms_before = axioms () in
  candle_q_dim_analytic_jet_profile_event "stage-preparation-begin";
  let plan,encoded_jobs = candle_case10173_compact_prepare () in
  candle_q_dim_analytic_jet_profile_event "stage-preparation-end";
  let structure_call = list_mk_comb
    (`candle_cv_case10173_compact_structure_check`,
     [encoded_jobs;candle_case10173_compact_roots]) and
      coordinate_call = list_mk_comb
        (`candle_cv_case10173_compact_coordinate_jobs_digest`,
         [plan;encoded_jobs]) and
      direct_coordinate_call = list_mk_comb
        (`candle_cv_case10173_direct_coordinate_jobs_digest`,
         [plan;encoded_jobs]) and
      fixed_coordinate_call = list_mk_comb
        (`candle_cv_case10173_fixed_coordinate_jobs_digest`,
         [`Cexp_num 1`;plan;encoded_jobs]) and
      unchecked_coordinate_call = list_mk_comb
        (`candle_cv_case10173_fixed_coordinate_jobs_digest`,
         [`Cexp_num 0`;plan;encoded_jobs]) and
      angle_call = list_mk_comb
        (`candle_cv_case10173_compact_angle_jobs_digest`,
         [encoded_jobs;candle_case10173_compact_roots]) in
  let run label call =
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
    let theorem = candle_q_dim_analytic_jet_compute
      candle_cv_case10173_compact_compute_eqs call in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-end");
    if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) then
      failwith ("case10173 compact stages: malformed " ^ label);
    theorem in
  let structure_1 = run "structure-1" structure_call in
  let coordinate_1 = run "coordinate-1" coordinate_call in
  let direct_coordinate_1 = run "direct-coordinate-1"
    direct_coordinate_call in
  let fixed_coordinate_1 = run "fixed-coordinate-1"
    fixed_coordinate_call in
  let unchecked_coordinate_1 = run "unchecked-coordinate-1"
    unchecked_coordinate_call in
  let angle_1 = run "angle-1" angle_call in
  let angle_2 = run "angle-2" angle_call in
  let unchecked_coordinate_2 = run "unchecked-coordinate-2"
    unchecked_coordinate_call in
  let fixed_coordinate_2 = run "fixed-coordinate-2"
    fixed_coordinate_call in
  let direct_coordinate_2 = run "direct-coordinate-2"
    direct_coordinate_call in
  let coordinate_2 = run "coordinate-2" coordinate_call in
  let structure_2 = run "structure-2" structure_call in
  if not (aconv (rand (concl structure_1)) `Cexp_num 1`) ||
     not (aconv (rand (concl structure_2)) `Cexp_num 1`) ||
     not (aconv (rand (concl coordinate_1))
       (rand (concl coordinate_2))) ||
     not (aconv (rand (concl direct_coordinate_1))
       (rand (concl direct_coordinate_2))) ||
     not (aconv (rand (concl fixed_coordinate_1))
       (rand (concl fixed_coordinate_2))) ||
     not (aconv (rand (concl unchecked_coordinate_1))
       (rand (concl unchecked_coordinate_2))) ||
     not (aconv (rand (concl fixed_coordinate_1))
       (rand (concl unchecked_coordinate_1))) ||
     not (aconv (rand (concl coordinate_1))
       (rand (concl direct_coordinate_1))) ||
     not (aconv (rand (concl angle_1)) (rand (concl angle_2))) ||
     length (axioms ()) <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) (axioms ()))
  then failwith "case10173 compact stages: repeat validation failed";
  print_endline
    "CANDLE_CV_CASE10173_COMPACT_STAGES_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 structure_repeats=2 coordinate_repeats=2 direct_coordinate_repeats=2 fixed_coordinate_repeats=2 unchecked_coordinate_repeats=2 angle_repeats=2 direct_coordinate_exact_match=1 fixed_coordinate_repeat_equal=1 unchecked_coordinate_exact_match=1 compact_digests_repeat_equal=1 assumptions=0 axiom_growth=0";;

end;;
