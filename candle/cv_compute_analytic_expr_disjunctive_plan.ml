(* ========================================================================== *)
(* Exact verifier plan for the smallest retained disjunctive family member. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This constructs the ordinary Flyspeck formal  *)
(* and informal verifier records, the certificate and adaptive precision     *)
(* tree, and one authenticated reflected program for each source disjunct.   *)
(* It proves no certificate leaf.                                             *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_fixture.ml";;

module Candle_cv_analytic_expr_disjunctive_plan = struct

open Certificate;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_fixture;;

let candle_disjunctive_plan_axioms_before = axioms ();;
let candle_disjunctive_plan_started = Unix.gettimeofday ();;

let candle_disjunctive_plan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-plan" ^
     " scope=plan phase=" ^ phase ^ " event=" ^ event);;

let candle_disjunctive_plan_lo,candle_disjunctive_plan_hi =
  candle_disjunctive_analytic_bounds;;
let candle_disjunctive_plan_sorted_variable_names =
  map (fst o dest_var)
    (dest_vector candle_disjunctive_analytic_variable_vector);;

if length candle_disjunctive_plan_sorted_variable_names <> 6 then
  failwith "disjunctive analytic plan: variable-order drift";;

let candle_disjunctive_plan_lo_list =
  dest_list candle_disjunctive_plan_lo
and candle_disjunctive_plan_hi_list =
  dest_list candle_disjunctive_plan_hi;;
let candle_disjunctive_plan_named_bounds =
  zip candle_disjunctive_analytic_variable_names
    (zip candle_disjunctive_plan_lo_list candle_disjunctive_plan_hi_list);;
let candle_disjunctive_plan_ordered_bounds =
  itlist
    (fun name result ->
      assoc name candle_disjunctive_plan_named_bounds :: result)
    candle_disjunctive_plan_sorted_variable_names [];;
let candle_disjunctive_plan_xx0,candle_disjunctive_plan_zz0 =
  unzip candle_disjunctive_plan_ordered_bounds;;
let candle_disjunctive_plan_xx = mk_real_list candle_disjunctive_plan_xx0
and candle_disjunctive_plan_zz = mk_real_list candle_disjunctive_plan_zz0;;
let candle_disjunctive_plan_domain_subset,
    (candle_disjunctive_plan_xx1,candle_disjunctive_plan_zz1) =
  M_verifier_main.mk_float_domain 6
    (candle_disjunctive_plan_xx,candle_disjunctive_plan_zz);;
let candle_disjunctive_plan_dimensions =
  map (get_dim o fst o dest_abs) candle_disjunctive_analytic_functions;;
let candle_disjunctive_plan_xx2 =
  Informal_taylor.convert_to_float_list 6 true candle_disjunctive_plan_xx
and candle_disjunctive_plan_zz2 =
  Informal_taylor.convert_to_float_list 6 false candle_disjunctive_plan_zz;;

let candle_disjunctive_plan_params =
  ref
    {M_verifier_main.default_params with
       mono_pass_flag = false;
       convex_flag = false;
       allow_derivatives = false;
       eps = 1e-10};;

let _ = candle_disjunctive_plan_marker "verifier-functions" "begin";;
let candle_disjunctive_plan_build_started = Unix.gettimeofday ();;
let candle_disjunctive_plan_formal_functions,
    candle_disjunctive_plan_informal_functions =
  unzip
    (map
      (M_verifier_main.mk_verification_functions
        candle_disjunctive_plan_params 6)
      candle_disjunctive_analytic_functions);;
let candle_disjunctive_plan_build_seconds =
  Unix.gettimeofday () -. candle_disjunctive_plan_build_started;;
let _ = candle_disjunctive_plan_marker "verifier-functions" "end";;

let candle_disjunctive_plan_search_options =
  Candle_informal_search_options.make
    !candle_disjunctive_plan_params.raw_intervals0 1e-10 200 6 0;;
let candle_disjunctive_plan_search_functions =
  map
    (fun f -> Candle_informal_verifier_record.f f,
      Candle_informal_verifier_record.taylor f)
    candle_disjunctive_plan_informal_functions;;
let candle_disjunctive_plan_informal_domain =
  Informal_taylor.mk_m_center_domain
    6 candle_disjunctive_plan_xx2 candle_disjunctive_plan_zz2;;

let _ = candle_disjunctive_plan_marker "certificate-search" "begin";;
let candle_disjunctive_plan_search_started = Unix.gettimeofday ();;
let candle_disjunctive_plan_certificate =
  Informal_search.construct_certificate
    candle_disjunctive_plan_search_options
    candle_disjunctive_plan_informal_domain
    candle_disjunctive_plan_search_functions;;
let candle_disjunctive_plan_search_seconds =
  Unix.gettimeofday () -. candle_disjunctive_plan_search_started;;
let _ = candle_disjunctive_plan_marker "certificate-search" "end";;
let candle_disjunctive_plan_stats =
  Certificate.result_stats candle_disjunctive_plan_certificate;;

if candle_disjunctive_plan_stats.pass <> 788 ||
   candle_disjunctive_plan_stats.pass_raw <> 0 ||
   candle_disjunctive_plan_stats.pass_mono <> 0 ||
   candle_disjunctive_plan_stats.mono <> 0 ||
   candle_disjunctive_plan_stats.glue <> 787 ||
   candle_disjunctive_plan_stats.glue_convex <> 0 then
  failwith "disjunctive analytic plan: certificate shape drift";;

let candle_disjunctive_plan_function0_leaves = ref 0;;
let candle_disjunctive_plan_function1_leaves = ref 0;;
let rec candle_disjunctive_plan_count_functions = function
  | Result_pass (0,false) ->
      candle_disjunctive_plan_function0_leaves :=
        !candle_disjunctive_plan_function0_leaves + 1
  | Result_pass (1,false) ->
      candle_disjunctive_plan_function1_leaves :=
        !candle_disjunctive_plan_function1_leaves + 1
  | Result_glue (_,false,left,right) ->
      candle_disjunctive_plan_count_functions left;
      candle_disjunctive_plan_count_functions right
  | _ -> failwith "disjunctive analytic plan: unexpected certificate node";;
let _ =
  candle_disjunctive_plan_count_functions
    candle_disjunctive_plan_certificate;;

if !candle_disjunctive_plan_function0_leaves +
     !candle_disjunctive_plan_function1_leaves <> 788 then
  failwith "disjunctive analytic plan: function count drift";;

let _ = candle_disjunctive_plan_marker "adaptive-precision" "begin";;
let candle_disjunctive_plan_adaptive_started = Unix.gettimeofday ();;
let candle_disjunctive_plan_precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 candle_disjunctive_plan_informal_functions
    candle_disjunctive_plan_certificate
    candle_disjunctive_plan_xx2 candle_disjunctive_plan_zz2;;
let candle_disjunctive_plan_adaptive_seconds =
  Unix.gettimeofday () -. candle_disjunctive_plan_adaptive_started;;
let _ = candle_disjunctive_plan_marker "adaptive-precision" "end";;

(* These payloads merely make the source programs concrete.  Leaf-specific  *)
(* square-root certificates are patched and checked by the reflected prover. *)
let candle_disjunctive_plan_sqrt_count = ref 0;;
let candle_disjunctive_plan_sqrt_interval _ =
  candle_disjunctive_plan_sqrt_count :=
    !candle_disjunctive_plan_sqrt_count + 1;
  `((((0,0),0),((100,0),0)):
      ((num#num)#num)#((num#num)#num))`;;

let _ = candle_disjunctive_plan_marker "source-preparation" "begin";;
let candle_disjunctive_plan_prepare_started = Unix.gettimeofday ();;
let candle_disjunctive_plan_prepared =
  map
    (candle_q_dim_analytic_jet_prepare_six_with
      candle_disjunctive_plan_sqrt_interval)
    candle_disjunctive_analytic_functions;;
let candle_disjunctive_plan_prepare_seconds =
  Unix.gettimeofday () -. candle_disjunctive_plan_prepare_started;;
let _ = candle_disjunctive_plan_marker "source-preparation" "end";;
let candle_disjunctive_plan_instruction_counts =
  map (fun prepared -> length (dest_list prepared.program_term))
    candle_disjunctive_plan_prepared;;
let candle_disjunctive_plan_total_seconds =
  Unix.gettimeofday () -. candle_disjunctive_plan_started;;

if candle_disjunctive_plan_dimensions <> [6;6] ||
   candle_disjunctive_plan_instruction_counts <> [1;167] ||
   !candle_disjunctive_plan_sqrt_count <> 10 ||
   hyp candle_disjunctive_plan_domain_subset <> [] ||
   not
     (List.for_all
       (fun prepared ->
         hyp prepared.valid_theorem = [] &&
         hyp prepared.source_theorem = [] &&
         hyp prepared.compile_theorem = [] &&
         hyp prepared.program_representation = [])
       candle_disjunctive_plan_prepared) then
  failwith "disjunctive analytic plan: authenticated state mismatch";;

let candle_disjunctive_plan_axioms_after = axioms ();;
if length candle_disjunctive_plan_axioms_after <>
     length candle_disjunctive_plan_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_disjunctive_plan_axioms_before)
       candle_disjunctive_plan_axioms_after) then
  failwith "disjunctive analytic plan changed the global axiom set";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_PLAN_RESULT leaves=788 glues=787" ^
   " function0_leaves=" ^
   string_of_int !candle_disjunctive_plan_function0_leaves ^
   " function1_leaves=" ^
   string_of_int !candle_disjunctive_plan_function1_leaves ^
   " instructions0=1 instructions1=167 sqrt_occurrences=10" ^
   " build_seconds=" ^
   string_of_float candle_disjunctive_plan_build_seconds ^
   " search_seconds=" ^
   string_of_float candle_disjunctive_plan_search_seconds ^
   " adaptive_seconds=" ^
   string_of_float candle_disjunctive_plan_adaptive_seconds ^
   " prepare_seconds=" ^
   string_of_float candle_disjunctive_plan_prepare_seconds ^
   " total_seconds=" ^ string_of_float candle_disjunctive_plan_total_seconds);;
print_endline "CANDLE_CV_DISJUNCTIVE_PLAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
