(* ========================================================================== *)
(* Compact topology-check benchmark on the authentic first 32 action-296   *)
(* roots.                                                                    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The existing pinned 32-root proof supplies  *)
(* the exact logical trees and an independently constructed well-formedness *)
(* theorem for comparison.  This benchmark rechecks those unchanged trees   *)
(* with the compact reflected checker and validates the theorem handoff.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact_sound.ml";;
needs "candle/test_cv_compute_analytic_expr_action296_grouped_32_adaptive_proof.ml";;

open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_correct;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_sound;;
open Candle_cv_polynomial_expr_dim_jet_prove;;

let candle_action296_grouped_32_compact_axioms_before = axioms ();;

let candle_action296_grouped_32_compact_preparation_seconds = ref 0.0;;
let candle_action296_grouped_32_compact_compute_seconds = ref 0.0;;
let candle_action296_grouped_32_compact_handoff_seconds = ref 0.0;;

let candle_action296_grouped_32_compact_timed total operation =
  let started = Sys.time () in
  let result = operation () in
  total := !total +. (Sys.time () -. started);
  result;;

let candle_action296_grouped_32_compact_profile index phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-compact-tree scope=first-32" ^
     " phase=" ^ phase ^ "-" ^ string_of_int index ^
     " event=" ^ event);;

let candle_action296_grouped_32_compact_check (index,logical) =
  let tree = logical.grouped_32_proof_logical_term in
  let call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_tree_topology_check`,
       [`Cexp_num 6`;
        mk_comb
          (`candle_cv_q_dim_taylor_model_tree_topology`,tree)]) in
  candle_action296_grouped_32_compact_profile
    index "compact-preparation" "begin";
  let representation =
    candle_action296_grouped_32_compact_timed
      candle_action296_grouped_32_compact_preparation_seconds
      (fun () ->
        REWRITE_CONV
          [candle_cv_q_dim_taylor_model_tree_topology_def;
           candle_cv_q_interval_list_def; candle_cv_q_interval_def;
           candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
          call) in
  candle_action296_grouped_32_compact_profile
    index "compact-preparation" "end";
  candle_action296_grouped_32_compact_profile
    index "compact-compute" "begin";
  let verdict =
    candle_action296_grouped_32_compact_timed
      candle_action296_grouped_32_compact_compute_seconds
      (fun () ->
        Kernel.compute
          (COMPUTE_INIT_THMS,
           candle_cv_q_dim_taylor_model_tree_compact_compute_eqs)
          (rand (concl representation))) in
  if not (aconv (rand (concl verdict)) `Cexp_num 1`) then
    failwith
      ("action296 grouped 32 compact tree: root " ^
       string_of_int index ^ " rejected");
  candle_action296_grouped_32_compact_profile
    index "compact-compute" "end";
  candle_action296_grouped_32_compact_profile
    index "compact-handoff" "begin";
  let well_formed =
    candle_action296_grouped_32_compact_timed
      candle_action296_grouped_32_compact_handoff_seconds
      (fun () ->
        let acceptance = TRANS representation verdict in
        MATCH_MP
          (REWRITE_RULE
            [candle_q_dim_poly_jet_dim_six]
            (ISPECL
              [tree;`ARB:real^6`]
              candle_cv_q_dim_taylor_model_tree_topology_accept_sound))
          acceptance) in
  if hyp well_formed <> [] ||
     not
       (aconv (concl well_formed)
         (concl logical.grouped_32_proof_logical_well_formed)) then
    failwith
      ("action296 grouped 32 compact tree: root " ^
       string_of_int index ^ " handoff mismatch");
  candle_action296_grouped_32_compact_profile
    index "compact-handoff" "end";
  index,well_formed;;

print_endline
  "CANDLE_CERT_PROFILE lane=action296-compact-tree scope=first-32 phase=compact-topologies event=begin";;
let candle_action296_grouped_32_compact_results =
  map candle_action296_grouped_32_compact_check
    (List.flatten
      (candle_action296_grouped_32_proof_logical_groups ()));;
print_endline
  "CANDLE_CERT_PROFILE lane=action296-compact-tree scope=first-32 phase=compact-topologies event=end";;

let candle_action296_grouped_32_compact_axioms_after = axioms ();;

if length candle_action296_grouped_32_compact_results <> 32 ||
   length candle_action296_grouped_32_compact_axioms_after <>
     length candle_action296_grouped_32_compact_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_grouped_32_compact_axioms_before)
       candle_action296_grouped_32_compact_axioms_after) then
  failwith "action296 grouped 32 compact tree: final validation";;

let candle_action296_grouped_32_compact_total_seconds =
  !candle_action296_grouped_32_compact_preparation_seconds +.
  !candle_action296_grouped_32_compact_compute_seconds +.
  !candle_action296_grouped_32_compact_handoff_seconds;;

print_endline
  ("CANDLE_CV_ACTION296_GROUPED_32_COMPACT_TREE_RESULT roots=32" ^
   " preparation_seconds=" ^
     string_of_float
       !candle_action296_grouped_32_compact_preparation_seconds ^
   " compute_seconds=" ^
     string_of_float !candle_action296_grouped_32_compact_compute_seconds ^
   " handoff_seconds=" ^
     string_of_float !candle_action296_grouped_32_compact_handoff_seconds ^
   " total_seconds=" ^
     string_of_float candle_action296_grouped_32_compact_total_seconds);;
print_endline
  "CANDLE_CV_ACTION296_GROUPED_32_COMPACT_TREE_OK DEVELOPMENT_NON_RELEASE";;
