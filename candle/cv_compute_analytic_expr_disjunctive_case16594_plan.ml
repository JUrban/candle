(* ========================================================================== *)
(* Reused-expression verifier plan for disjunctive family member 16594.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The source formula is independently rebuilt, *)
(* while verifier records and reflected programs are reused only after exact *)
(* alpha-equivalence checks against the completed family member 16479.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_plan.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_case16594_fixture.ml";;

module Candle_cv_analytic_expr_disjunctive_case16594_plan = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_fixture;;
open Candle_cv_analytic_expr_disjunctive_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;

let candle_disjunctive_case16594_plan_axioms_before = axioms ();;
let candle_disjunctive_case16594_plan_started = Unix.gettimeofday ();;

let candle_disjunctive_case16594_plan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-plan" ^
     " scope=plan phase=" ^ phase ^ " event=" ^ event);;

let rec candle_disjunctive_case16594_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_case16594_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_disjunctive_case16594_plan_lo,
    candle_disjunctive_case16594_plan_hi =
  candle_disjunctive_case16594_bounds;;
let candle_disjunctive_case16594_plan_sorted_variable_names =
  map (fst o dest_var)
    (dest_vector candle_disjunctive_case16594_variable_vector);;
let candle_disjunctive_case16594_plan_lo_list =
  dest_list candle_disjunctive_case16594_plan_lo
and candle_disjunctive_case16594_plan_hi_list =
  dest_list candle_disjunctive_case16594_plan_hi;;
let candle_disjunctive_case16594_plan_named_bounds =
  zip candle_disjunctive_case16594_variable_names
    (zip candle_disjunctive_case16594_plan_lo_list
      candle_disjunctive_case16594_plan_hi_list);;
let candle_disjunctive_case16594_plan_ordered_bounds =
  itlist
    (fun name result ->
      assoc name candle_disjunctive_case16594_plan_named_bounds :: result)
    candle_disjunctive_case16594_plan_sorted_variable_names [];;
let candle_disjunctive_case16594_plan_xx0,
    candle_disjunctive_case16594_plan_zz0 =
  unzip candle_disjunctive_case16594_plan_ordered_bounds;;
let candle_disjunctive_case16594_plan_xx =
  mk_real_list candle_disjunctive_case16594_plan_xx0
and candle_disjunctive_case16594_plan_zz =
  mk_real_list candle_disjunctive_case16594_plan_zz0;;
let candle_disjunctive_case16594_plan_domain_subset,
    (candle_disjunctive_case16594_plan_xx1,
     candle_disjunctive_case16594_plan_zz1) =
  M_verifier_main.mk_float_domain 6
    (candle_disjunctive_case16594_plan_xx,
     candle_disjunctive_case16594_plan_zz);;
let candle_disjunctive_case16594_plan_xx2 =
  Informal_taylor.convert_to_float_list 6 true
    candle_disjunctive_case16594_plan_xx
and candle_disjunctive_case16594_plan_zz2 =
  Informal_taylor.convert_to_float_list 6 false
    candle_disjunctive_case16594_plan_zz;;

if candle_disjunctive_case16594_plan_sorted_variable_names <>
     candle_disjunctive_plan_sorted_variable_names ||
   not
     (candle_disjunctive_case16594_aconv_lists
       candle_disjunctive_case16594_functions
       candle_disjunctive_analytic_functions) ||
   not
     (aconv candle_disjunctive_case16594_variable_vector
       candle_disjunctive_analytic_variable_vector) then
  failwith "case16594 plan: expression reuse identity mismatch";;

let candle_disjunctive_case16594_plan_formal_functions =
  candle_disjunctive_plan_formal_functions;;
let candle_disjunctive_case16594_plan_informal_functions =
  candle_disjunctive_plan_informal_functions;;
let candle_disjunctive_case16594_plan_prepared =
  candle_disjunctive_plan_prepared;;

let candle_disjunctive_case16594_plan_search_options =
  Candle_informal_search_options.make
    !candle_disjunctive_plan_params.raw_intervals0 1e-10 200 6 0;;
let candle_disjunctive_case16594_plan_search_functions =
  map
    (fun f -> Candle_informal_verifier_record.f f,
      Candle_informal_verifier_record.taylor f)
    candle_disjunctive_case16594_plan_informal_functions;;
let candle_disjunctive_case16594_plan_informal_domain =
  Informal_taylor.mk_m_center_domain 6
    candle_disjunctive_case16594_plan_xx2
    candle_disjunctive_case16594_plan_zz2;;

let _ =
  candle_disjunctive_case16594_plan_marker "certificate-search" "begin";;
let candle_disjunctive_case16594_plan_search_started =
  Unix.gettimeofday ();;
let candle_disjunctive_case16594_plan_certificate =
  Informal_search.construct_certificate
    candle_disjunctive_case16594_plan_search_options
    candle_disjunctive_case16594_plan_informal_domain
    candle_disjunctive_case16594_plan_search_functions;;
let candle_disjunctive_case16594_plan_search_seconds =
  Unix.gettimeofday () -.
    candle_disjunctive_case16594_plan_search_started;;
let _ =
  candle_disjunctive_case16594_plan_marker "certificate-search" "end";;
let candle_disjunctive_case16594_plan_stats =
  Certificate.result_stats
    candle_disjunctive_case16594_plan_certificate;;

if candle_disjunctive_case16594_plan_stats.pass <> 860 ||
   candle_disjunctive_case16594_plan_stats.pass_raw <> 0 ||
   candle_disjunctive_case16594_plan_stats.pass_mono <> 0 ||
   candle_disjunctive_case16594_plan_stats.mono <> 0 ||
   candle_disjunctive_case16594_plan_stats.glue <> 859 ||
   candle_disjunctive_case16594_plan_stats.glue_convex <> 0 then
  failwith "case16594 plan: certificate shape drift";;

let _ =
  candle_disjunctive_case16594_plan_marker "adaptive-precision" "begin";;
let candle_disjunctive_case16594_plan_adaptive_started =
  Unix.gettimeofday ();;
let candle_disjunctive_case16594_plan_precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 candle_disjunctive_case16594_plan_informal_functions
    candle_disjunctive_case16594_plan_certificate
    candle_disjunctive_case16594_plan_xx2
    candle_disjunctive_case16594_plan_zz2;;
let candle_disjunctive_case16594_plan_adaptive_seconds =
  Unix.gettimeofday () -.
    candle_disjunctive_case16594_plan_adaptive_started;;
let _ =
  candle_disjunctive_case16594_plan_marker "adaptive-precision" "end";;

let candle_disjunctive_case16594_plan_function0_leaves = ref 0;;
let candle_disjunctive_case16594_plan_function1_leaves = ref 0;;
let rec candle_disjunctive_case16594_plan_count_functions = function
  | P_result_pass (_,0,false) ->
      candle_disjunctive_case16594_plan_function0_leaves :=
        !candle_disjunctive_case16594_plan_function0_leaves + 1
  | P_result_pass (_,1,false) ->
      candle_disjunctive_case16594_plan_function1_leaves :=
        !candle_disjunctive_case16594_plan_function1_leaves + 1
  | P_result_glue (_,_,false,left,right) ->
      candle_disjunctive_case16594_plan_count_functions left;
      candle_disjunctive_case16594_plan_count_functions right
  | _ -> failwith "case16594 plan: unexpected precision-tree node";;
let _ =
  candle_disjunctive_case16594_plan_count_functions
    candle_disjunctive_case16594_plan_precision_tree;;

let candle_disjunctive_case16594_plan_axioms_after = axioms ();;
if !candle_disjunctive_case16594_plan_function0_leaves +
     !candle_disjunctive_case16594_plan_function1_leaves <> 860 ||
   hyp candle_disjunctive_case16594_plan_domain_subset <> [] ||
   length candle_disjunctive_case16594_plan_axioms_after <>
     length candle_disjunctive_case16594_plan_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_disjunctive_case16594_plan_axioms_before)
       candle_disjunctive_case16594_plan_axioms_after) then
  failwith "case16594 plan: authenticated state mismatch";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_CASE16594_PLAN_RESULT leaves=860 glues=859" ^
   " function0_leaves=" ^
   string_of_int !candle_disjunctive_case16594_plan_function0_leaves ^
   " function1_leaves=" ^
   string_of_int !candle_disjunctive_case16594_plan_function1_leaves ^
   " reused_formal_functions=2 reused_programs=2" ^
   " search_seconds=" ^
   string_of_float candle_disjunctive_case16594_plan_search_seconds ^
   " adaptive_seconds=" ^
   string_of_float candle_disjunctive_case16594_plan_adaptive_seconds ^
   " total_seconds=" ^
   string_of_float
     (Unix.gettimeofday () -. candle_disjunctive_case16594_plan_started));;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_PLAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
