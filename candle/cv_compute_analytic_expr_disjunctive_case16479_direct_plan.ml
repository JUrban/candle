(* Reuse the authenticated direct expression programs for production leaf 149. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16479_direct_fixture.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_case16594_direct_plan.ml";;

module Candle_cv_analytic_expr_disjunctive_case16479_plan = struct

open Certificate;;
open M_verifier_main;;
open Candle_cv_analytic_expr_disjunctive_case16479_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;

let rec candle_disjunctive_case16479_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_case16479_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_disjunctive_case16479_lo,
    candle_disjunctive_case16479_hi =
  candle_disjunctive_case16479_bounds;;
let candle_disjunctive_case16479_sorted_variable_names =
  map (fst o dest_var)
    (M_taylor.dest_vector candle_disjunctive_case16479_variable_vector);;
let candle_disjunctive_case16479_lo_list =
  dest_list candle_disjunctive_case16479_lo
and candle_disjunctive_case16479_hi_list =
  dest_list candle_disjunctive_case16479_hi;;
let candle_disjunctive_case16479_named_bounds =
  zip candle_disjunctive_case16479_variable_names
    (zip candle_disjunctive_case16479_lo_list
      candle_disjunctive_case16479_hi_list);;
let candle_disjunctive_case16479_ordered_bounds =
  itlist
    (fun name result ->
      assoc name candle_disjunctive_case16479_named_bounds :: result)
    candle_disjunctive_case16479_sorted_variable_names [];;
let candle_disjunctive_case16479_xx0,
    candle_disjunctive_case16479_zz0 =
  unzip candle_disjunctive_case16479_ordered_bounds;;
let candle_disjunctive_case16479_xx =
  Misc_vars.mk_real_list candle_disjunctive_case16479_xx0
and candle_disjunctive_case16479_zz =
  Misc_vars.mk_real_list candle_disjunctive_case16479_zz0;;
let candle_disjunctive_case16479_domain_subset,
    (candle_disjunctive_case16479_xx1,
     candle_disjunctive_case16479_zz1) =
  M_verifier_main.mk_float_domain 6
    (candle_disjunctive_case16479_xx,
     candle_disjunctive_case16479_zz);;
let candle_disjunctive_case16479_xx2 =
  Informal_taylor.convert_to_float_list 6 true
    candle_disjunctive_case16479_xx
and candle_disjunctive_case16479_zz2 =
  Informal_taylor.convert_to_float_list 6 false
    candle_disjunctive_case16479_zz;;

if candle_disjunctive_case16479_sorted_variable_names <>
     candle_disjunctive_case16594_plan_sorted_variable_names ||
   not
     (candle_disjunctive_case16479_aconv_lists
       candle_disjunctive_case16479_functions
       candle_disjunctive_case16594_functions) ||
   not
     (aconv candle_disjunctive_case16479_variable_vector
       candle_disjunctive_case16594_variable_vector) then
  failwith "case16479 direct plan: shared expression identity mismatch";;

let candle_disjunctive_case16479_formal_functions =
  candle_disjunctive_case16594_plan_formal_functions;;
let candle_disjunctive_case16479_informal_functions =
  candle_disjunctive_case16594_plan_informal_functions;;
let candle_disjunctive_case16479_prepared =
  candle_disjunctive_case16594_plan_prepared;;
let candle_disjunctive_case16479_search_options =
  Candle_informal_search_options.make
    !candle_disjunctive_case16594_plan_params.raw_intervals0
    1e-10 200 6 0;;
let candle_disjunctive_case16479_search_functions =
  map
    (fun f -> Candle_informal_verifier_record.f f,
      Candle_informal_verifier_record.taylor f)
    candle_disjunctive_case16479_informal_functions;;
let candle_disjunctive_case16479_informal_domain =
  Informal_taylor.mk_m_center_domain 6
    candle_disjunctive_case16479_xx2
    candle_disjunctive_case16479_zz2;;

let candle_disjunctive_case16479_certificate =
  Informal_search.construct_certificate
    candle_disjunctive_case16479_search_options
    candle_disjunctive_case16479_informal_domain
    candle_disjunctive_case16479_search_functions;;
let candle_disjunctive_case16479_stats =
  Certificate.result_stats candle_disjunctive_case16479_certificate;;

if candle_disjunctive_case16479_stats.pass <> 788 ||
   candle_disjunctive_case16479_stats.pass_raw <> 0 ||
   candle_disjunctive_case16479_stats.pass_mono <> 0 ||
   candle_disjunctive_case16479_stats.mono <> 0 ||
   candle_disjunctive_case16479_stats.glue <> 787 ||
   candle_disjunctive_case16479_stats.glue_convex <> 0 then
  failwith "case16479 direct plan: certificate shape drift";;

let candle_disjunctive_case16479_precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 candle_disjunctive_case16479_informal_functions
    candle_disjunctive_case16479_certificate
    candle_disjunctive_case16479_xx2
    candle_disjunctive_case16479_zz2;;

let candle_disjunctive_case16479_function0 = ref 0;;
let candle_disjunctive_case16479_function1 = ref 0;;
let rec candle_disjunctive_case16479_count_functions = function
  | P_result_pass (_,0,false) ->
      candle_disjunctive_case16479_function0 :=
        !candle_disjunctive_case16479_function0 + 1
  | P_result_pass (_,1,false) ->
      candle_disjunctive_case16479_function1 :=
        !candle_disjunctive_case16479_function1 + 1
  | P_result_glue (_,_,false,left,right) ->
      candle_disjunctive_case16479_count_functions left;
      candle_disjunctive_case16479_count_functions right
  | _ -> failwith "case16479 direct plan: unexpected precision-tree node";;
let _ =
  candle_disjunctive_case16479_count_functions
    candle_disjunctive_case16479_precision_tree;;

if !candle_disjunctive_case16479_function0 <> 0 ||
   !candle_disjunctive_case16479_function1 <> 788 ||
   hyp candle_disjunctive_case16479_domain_subset <> [] then
  failwith "case16479 direct plan: authenticated state mismatch";;

print_endline
  ("CANDLE_CV_CASE16479_DIRECT_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " parent=prep-8293089898 index=149 leaves=788 glues=787" ^
   " function0_leaves=0 function1_leaves=788" ^
   " reused_formal_functions=2 reused_direct_programs=2");;

end;;
