(* ========================================================================== *)
(* Reusable live-verifier plan for the first nonlinear inequality at 296.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This constructs the ordinary Flyspeck formal  *)
(* and informal verifier records, certificate, adaptive precision tree, and  *)
(* authenticated reflected source program.  It proves no certificate leaf.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_analytic_expr_action296_fixture.ml";;

module Candle_cv_analytic_expr_action296_plan = struct

open Certificate;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_fixture;;

let candle_action296_plan_axioms_before = axioms ();;
let candle_action296_plan_started = Unix.gettimeofday ();;

let candle_action296_plan_lo,candle_action296_plan_hi =
  candle_action296_analytic_bounds;;
let candle_action296_plan_sorted_variable_names =
  map (fst o dest_var)
    (dest_vector candle_action296_analytic_variable_vector);;

if length candle_action296_plan_sorted_variable_names <> 6 then
  failwith "action296 analytic plan: variable-order drift";;

let candle_action296_plan_lo_list =
  dest_list candle_action296_plan_lo
and candle_action296_plan_hi_list =
  dest_list candle_action296_plan_hi;;
let candle_action296_plan_named_bounds =
  zip candle_action296_analytic_variable_names
    (zip candle_action296_plan_lo_list candle_action296_plan_hi_list);;
let candle_action296_plan_ordered_bounds =
  itlist
    (fun name result ->
      assoc name candle_action296_plan_named_bounds :: result)
    candle_action296_plan_sorted_variable_names [];;
let candle_action296_plan_xx0,candle_action296_plan_zz0 =
  unzip candle_action296_plan_ordered_bounds;;
let candle_action296_plan_xx = mk_real_list candle_action296_plan_xx0
and candle_action296_plan_zz = mk_real_list candle_action296_plan_zz0;;
let candle_action296_plan_domain_subset,
    (candle_action296_plan_xx1,candle_action296_plan_zz1) =
  M_verifier_main.mk_float_domain 6
    (candle_action296_plan_xx,candle_action296_plan_zz);;
let candle_action296_plan_dimension =
  (get_dim o fst o dest_abs) candle_action296_analytic_function;;
let candle_action296_plan_xx2 =
  Informal_taylor.convert_to_float_list 6 true candle_action296_plan_xx
and candle_action296_plan_zz2 =
  Informal_taylor.convert_to_float_list 6 false candle_action296_plan_zz;;

let candle_action296_plan_params =
  ref
    {M_verifier_main.default_params with
       mono_pass_flag = false;
       convex_flag = false;
       allow_derivatives = false;
       eps = 1e-10};;

let candle_action296_plan_build_started = Unix.gettimeofday ();;
let candle_action296_plan_formal_functions,
    candle_action296_plan_informal_functions =
  unzip
    (map
      (M_verifier_main.mk_verification_functions
        candle_action296_plan_params 6)
      candle_action296_analytic_functions);;
let candle_action296_plan_build_seconds =
  Unix.gettimeofday () -. candle_action296_plan_build_started;;

let candle_action296_plan_search_options =
  Candle_informal_search_options.make
    !candle_action296_plan_params.raw_intervals0 1e-10 200 6 0;;
let candle_action296_plan_search_functions =
  map
    (fun f -> Candle_informal_verifier_record.f f,
      Candle_informal_verifier_record.taylor f)
    candle_action296_plan_informal_functions;;
let candle_action296_plan_informal_domain =
  Informal_taylor.mk_m_center_domain
    6 candle_action296_plan_xx2 candle_action296_plan_zz2;;

let candle_action296_plan_search_started = Unix.gettimeofday ();;
let candle_action296_plan_certificate =
  Informal_search.construct_certificate
    candle_action296_plan_search_options
    candle_action296_plan_informal_domain
    candle_action296_plan_search_functions;;
let candle_action296_plan_search_seconds =
  Unix.gettimeofday () -. candle_action296_plan_search_started;;
let candle_action296_plan_stats =
  Certificate.result_stats candle_action296_plan_certificate;;

if candle_action296_plan_stats.pass <> 1061 ||
   candle_action296_plan_stats.pass_raw <> 0 ||
   candle_action296_plan_stats.pass_mono <> 0 ||
   candle_action296_plan_stats.mono <> 0 ||
   candle_action296_plan_stats.glue <> 1060 ||
   candle_action296_plan_stats.glue_convex <> 0 then
  failwith "action296 analytic plan: certificate shape drift";;

let candle_action296_plan_adaptive_started = Unix.gettimeofday ();;
let candle_action296_plan_precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 candle_action296_plan_informal_functions
    candle_action296_plan_certificate
    candle_action296_plan_xx2 candle_action296_plan_zz2;;
let candle_action296_plan_adaptive_seconds =
  Unix.gettimeofday () -. candle_action296_plan_adaptive_started;;

let candle_action296_plan_vector,_ =
  dest_abs candle_action296_analytic_function;;
let candle_action296_plan_variables =
  Candle_cv_polynomial_expr_flyspeck_reify.candle_poly_vector_components
    candle_action296_plan_vector 6;;
let candle_action296_plan_sqrt_variables =
  map (fun variable -> mk_comb (`sqrt:real->real`,variable))
    candle_action296_plan_variables;;
let candle_action296_plan_variable_sqrt_count = ref 0;;
let candle_action296_plan_nested_sqrt_count = ref 0;;

let candle_action296_plan_sqrt_interval tm =
  if exists (aconv tm) candle_action296_plan_sqrt_variables then
    (candle_action296_plan_variable_sqrt_count :=
       !candle_action296_plan_variable_sqrt_count + 1;
     `((((2,0),0),((3,0),0)):
        ((num#num)#num)#((num#num)#num))`)
  else
    (candle_action296_plan_nested_sqrt_count :=
       !candle_action296_plan_nested_sqrt_count + 1;
     `((((50,0),0),((100,0),0)):
        ((num#num)#num)#((num#num)#num))`);;

let candle_action296_plan_prepare_started = Unix.gettimeofday ();;
let candle_action296_plan_prepared =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_action296_plan_sqrt_interval
    candle_action296_analytic_function;;
let candle_action296_plan_prepare_seconds =
  Unix.gettimeofday () -. candle_action296_plan_prepare_started;;
let candle_action296_plan_instruction_count =
  length (dest_list candle_action296_plan_prepared.program_term);;
let candle_action296_plan_total_seconds =
  Unix.gettimeofday () -. candle_action296_plan_started;;

if candle_action296_plan_dimension <> 6 ||
   !candle_action296_plan_variable_sqrt_count <> 6 ||
   !candle_action296_plan_nested_sqrt_count <> 1 ||
   candle_action296_plan_instruction_count <> 54 ||
   hyp candle_action296_plan_domain_subset <> [] ||
   hyp candle_action296_plan_prepared.valid_theorem <> [] ||
   hyp candle_action296_plan_prepared.source_theorem <> [] then
  failwith "action296 analytic plan: authenticated state mismatch";;

let candle_action296_plan_axioms_after = axioms ();;
if length candle_action296_plan_axioms_after <>
     length candle_action296_plan_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_action296_plan_axioms_before)
       candle_action296_plan_axioms_after) then
  failwith "action296 analytic plan changed the global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_ANALYTIC_PLAN_RESULT leaves=1061 glues=1060 " ^
   "instructions=54 build_seconds=" ^
   string_of_float candle_action296_plan_build_seconds ^
   " search_seconds=" ^
   string_of_float candle_action296_plan_search_seconds ^
   " adaptive_seconds=" ^
   string_of_float candle_action296_plan_adaptive_seconds ^
   " prepare_seconds=" ^
   string_of_float candle_action296_plan_prepare_seconds ^
   " total_seconds=" ^ string_of_float candle_action296_plan_total_seconds);
print_endline "CANDLE_CV_ACTION296_ANALYTIC_PLAN_OK";;

end;;
