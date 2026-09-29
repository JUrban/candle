(* ========================================================================== *)
(* Case 10173 plan with expression-dependent preparation reused from 10172.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This constructs a fresh certificate and      *)
(* adaptive tree for the sibling domain.  It proves no certificate leaf.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_case10173_fixture.ml";;

module Candle_cv_analytic_expr_case10173_reused_plan = struct

open Certificate;;
open Candle_cv_analytic_expr_action296_fixture;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_case10173_fixture;;

let candle_case10173_plan_axioms_before = axioms ();;
let candle_case10173_plan_started = Unix.gettimeofday ();;

if not
     (aconv candle_case10173_analytic_function
        candle_action296_analytic_function) then
  failwith "case10173 plan: shared analytic expression drift";;

let candle_case10173_plan_lo,candle_case10173_plan_hi =
  candle_case10173_analytic_bounds;;
let candle_case10173_plan_lo_list =
  dest_list candle_case10173_plan_lo
and candle_case10173_plan_hi_list =
  dest_list candle_case10173_plan_hi;;
let candle_case10173_plan_named_bounds =
  zip candle_case10173_analytic_variable_names
    (zip candle_case10173_plan_lo_list candle_case10173_plan_hi_list);;
let candle_case10173_plan_ordered_bounds =
  itlist
    (fun name result ->
      assoc name candle_case10173_plan_named_bounds :: result)
    candle_action296_plan_sorted_variable_names [];;
let candle_case10173_plan_xx0,candle_case10173_plan_zz0 =
  unzip candle_case10173_plan_ordered_bounds;;
let candle_case10173_plan_xx = mk_real_list candle_case10173_plan_xx0
and candle_case10173_plan_zz = mk_real_list candle_case10173_plan_zz0;;
let candle_case10173_plan_domain_subset,
    (candle_case10173_plan_xx1,candle_case10173_plan_zz1) =
  M_verifier_main.mk_float_domain 6
    (candle_case10173_plan_xx,candle_case10173_plan_zz);;
let candle_case10173_plan_xx2 =
  Informal_taylor.convert_to_float_list 6 true candle_case10173_plan_xx
and candle_case10173_plan_zz2 =
  Informal_taylor.convert_to_float_list 6 false candle_case10173_plan_zz;;

(* The verifier records, reflected program, validity theorem, source theorem,
   and search functions depend on the expression and parameters, not the box.
   The exact expression check above is the authority for this reuse. *)
let candle_case10173_plan_formal_functions =
  candle_action296_plan_formal_functions;;
let candle_case10173_plan_informal_functions =
  candle_action296_plan_informal_functions;;
let candle_case10173_plan_search_options =
  candle_action296_plan_search_options;;
let candle_case10173_plan_search_functions =
  candle_action296_plan_search_functions;;
let candle_case10173_plan_prepared =
  candle_action296_plan_prepared;;

let candle_case10173_plan_informal_domain =
  Informal_taylor.mk_m_center_domain
    6 candle_case10173_plan_xx2 candle_case10173_plan_zz2;;

let candle_case10173_plan_search_started = Unix.gettimeofday ();;
let candle_case10173_plan_certificate =
  Informal_search.construct_certificate
    candle_case10173_plan_search_options
    candle_case10173_plan_informal_domain
    candle_case10173_plan_search_functions;;
let candle_case10173_plan_search_seconds =
  Unix.gettimeofday () -. candle_case10173_plan_search_started;;
let candle_case10173_plan_stats =
  Certificate.result_stats candle_case10173_plan_certificate;;

if candle_case10173_plan_stats.pass <> 3305 ||
   candle_case10173_plan_stats.pass_raw <> 0 ||
   candle_case10173_plan_stats.pass_mono <> 0 ||
   candle_case10173_plan_stats.mono <> 0 ||
   candle_case10173_plan_stats.glue <> 3304 ||
   candle_case10173_plan_stats.glue_convex <> 0 then
  failwith "case10173 plan: certificate shape drift";;

let candle_case10173_plan_adaptive_started = Unix.gettimeofday ();;
let candle_case10173_plan_precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 candle_case10173_plan_informal_functions
    candle_case10173_plan_certificate
    candle_case10173_plan_xx2 candle_case10173_plan_zz2;;
let candle_case10173_plan_adaptive_seconds =
  Unix.gettimeofday () -. candle_case10173_plan_adaptive_started;;
let candle_case10173_plan_total_seconds =
  Unix.gettimeofday () -. candle_case10173_plan_started;;

if hyp candle_case10173_plan_domain_subset <> [] ||
   hyp candle_case10173_plan_prepared.valid_theorem <> [] ||
   hyp candle_case10173_plan_prepared.source_theorem <> [] then
  failwith "case10173 plan: authenticated state mismatch";;

let candle_case10173_plan_axioms_after = axioms ();;
if length candle_case10173_plan_axioms_after <>
     length candle_case10173_plan_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_case10173_plan_axioms_before)
       candle_case10173_plan_axioms_after) then
  failwith "case10173 plan changed the global axiom set";;

print_endline
  ("CANDLE_CV_CASE10173_REUSED_PLAN_RESULT leaves=3305 glues=3304 " ^
   "instructions=" ^
   string_of_int candle_action296_plan_instruction_count ^
   " expression_preparation=reused search_seconds=" ^
   string_of_float candle_case10173_plan_search_seconds ^
   " adaptive_seconds=" ^
   string_of_float candle_case10173_plan_adaptive_seconds ^
   " total_seconds=" ^ string_of_float candle_case10173_plan_total_seconds);;
print_endline "CANDLE_CV_CASE10173_REUSED_PLAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
