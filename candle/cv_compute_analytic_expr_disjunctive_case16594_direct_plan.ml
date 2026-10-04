(* ========================================================================== *)
(* Direct-verifier reflected plan for genuine nonlinear member 16594.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Unlike the historical plan, this constructs  *)
(* the verifier functions and reflected programs directly from the loaded   *)
(* Flyspeck proposition.  Certificate search remains untrusted; all retained *)
(* source programs and later verdicts are authenticated by kernel theorems.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_case16594_direct_fixture.ml";;
needs "formal_ineqs/verifier/certificate.hl";;

module Candle_cv_analytic_expr_disjunctive_case16594_plan = struct

open Certificate;;
open M_verifier_main;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;

let candle_disjunctive_case16594_plan_axioms_before = axioms ();;
let candle_disjunctive_case16594_plan_started = Unix.gettimeofday ();;

let candle_disjunctive_case16594_plan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-direct-plan" ^
     " scope=plan phase=" ^ phase ^ " event=" ^ event);;

let candle_disjunctive_case16594_plan_lo,
    candle_disjunctive_case16594_plan_hi =
  candle_disjunctive_case16594_bounds;;
let candle_disjunctive_case16594_plan_sorted_variable_names =
  map (fst o dest_var)
    (M_taylor.dest_vector candle_disjunctive_case16594_variable_vector);;
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
  Misc_vars.mk_real_list candle_disjunctive_case16594_plan_xx0
and candle_disjunctive_case16594_plan_zz =
  Misc_vars.mk_real_list candle_disjunctive_case16594_plan_zz0;;
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

if length candle_disjunctive_case16594_plan_sorted_variable_names <> 6 then
  failwith "case16594 direct plan: variable-order drift";;

let candle_disjunctive_case16594_plan_params =
  ref
    {M_verifier_main.default_params with
       mono_pass_flag = false;
       convex_flag = false;
       allow_derivatives = false;
       eps = 1e-10};;

let _ =
  candle_disjunctive_case16594_plan_marker "verifier-functions" "begin";;
let candle_disjunctive_case16594_plan_build_started = Unix.gettimeofday ();;
let candle_disjunctive_case16594_plan_formal_functions,
    candle_disjunctive_case16594_plan_informal_functions =
  unzip
    (map
      (M_verifier_main.mk_verification_functions
        candle_disjunctive_case16594_plan_params 6)
      candle_disjunctive_case16594_functions);;
let candle_disjunctive_case16594_plan_build_seconds =
  Unix.gettimeofday () -. candle_disjunctive_case16594_plan_build_started;;
let _ =
  candle_disjunctive_case16594_plan_marker "verifier-functions" "end";;

let candle_disjunctive_case16594_plan_search_options =
  Candle_informal_search_options.make
    !candle_disjunctive_case16594_plan_params.raw_intervals0 1e-10 200 6 0;;
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
let candle_disjunctive_case16594_plan_search_started = Unix.gettimeofday ();;
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
  Certificate.result_stats candle_disjunctive_case16594_plan_certificate;;

if candle_disjunctive_case16594_plan_stats.pass <> 860 ||
   candle_disjunctive_case16594_plan_stats.pass_raw <> 0 ||
   candle_disjunctive_case16594_plan_stats.pass_mono <> 0 ||
   candle_disjunctive_case16594_plan_stats.mono <> 0 ||
   candle_disjunctive_case16594_plan_stats.glue <> 859 ||
   candle_disjunctive_case16594_plan_stats.glue_convex <> 0 then
  failwith "case16594 direct plan: certificate shape drift";;

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
  | _ -> failwith "case16594 direct plan: unexpected precision-tree node";;
let _ =
  candle_disjunctive_case16594_plan_count_functions
    candle_disjunctive_case16594_plan_precision_tree;;

(* The intervals make the source programs concrete only.  Every actual leaf
   supplies and checks its own square-root certificates later. *)
let candle_disjunctive_case16594_plan_sqrt_count = ref 0;;
let candle_disjunctive_case16594_plan_sqrt_interval _ =
  candle_disjunctive_case16594_plan_sqrt_count :=
    !candle_disjunctive_case16594_plan_sqrt_count + 1;
  `((((0,0),0),((100,0),0)):
      ((num#num)#num)#((num#num)#num))`;;

let _ =
  candle_disjunctive_case16594_plan_marker "source-preparation" "begin";;
let candle_disjunctive_case16594_plan_prepare_started =
  Unix.gettimeofday ();;
let candle_disjunctive_case16594_plan_prepared =
  map
    (candle_q_dim_analytic_jet_prepare_six_with
      candle_disjunctive_case16594_plan_sqrt_interval)
    candle_disjunctive_case16594_functions;;
let candle_disjunctive_case16594_plan_prepare_seconds =
  Unix.gettimeofday () -.
    candle_disjunctive_case16594_plan_prepare_started;;
let _ =
  candle_disjunctive_case16594_plan_marker "source-preparation" "end";;
let candle_disjunctive_case16594_plan_instruction_counts =
  map (fun prepared -> length (dest_list prepared.program_term))
    candle_disjunctive_case16594_plan_prepared;;

let candle_disjunctive_case16594_plan_axioms_after = axioms ();;
if !candle_disjunctive_case16594_plan_function0_leaves <> 0 ||
   !candle_disjunctive_case16594_plan_function1_leaves <> 860 ||
   candle_disjunctive_case16594_plan_instruction_counts <> [1;167] ||
   !candle_disjunctive_case16594_plan_sqrt_count <> 10 ||
   hyp candle_disjunctive_case16594_plan_domain_subset <> [] ||
   not
     (List.for_all
       (fun prepared ->
         hyp prepared.valid_theorem = [] &&
         hyp prepared.source_theorem = [] &&
         hyp prepared.compile_theorem = [] &&
         hyp prepared.program_representation = [])
       candle_disjunctive_case16594_plan_prepared) ||
   length candle_disjunctive_case16594_plan_axioms_after <>
     length candle_disjunctive_case16594_plan_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_disjunctive_case16594_plan_axioms_before)
       candle_disjunctive_case16594_plan_axioms_after) then
  failwith "case16594 direct plan: authenticated state mismatch";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_CASE16594_DIRECT_PLAN_RESULT leaves=860 glues=859" ^
   " function0_leaves=0 function1_leaves=860" ^
   " instructions0=1 instructions1=167 sqrt_occurrences=10" ^
   " build_seconds=" ^
   string_of_float candle_disjunctive_case16594_plan_build_seconds ^
   " search_seconds=" ^
   string_of_float candle_disjunctive_case16594_plan_search_seconds ^
   " adaptive_seconds=" ^
   string_of_float candle_disjunctive_case16594_plan_adaptive_seconds ^
   " prepare_seconds=" ^
   string_of_float candle_disjunctive_case16594_plan_prepare_seconds ^
   " total_seconds=" ^
   string_of_float
     (Unix.gettimeofday () -. candle_disjunctive_case16594_plan_started));;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_DIRECT_PLAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
