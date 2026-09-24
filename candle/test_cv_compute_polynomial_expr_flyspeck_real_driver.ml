(* ========================================================================== *)
(* Replay one genuine Flyspeck nonlinear certificate with reflected leaves.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The real-functions checkpoint supplies the     *)
(* authenticated source bridge and legacy verifier records.  This test builds *)
(* the genuine adaptive certificate, derives every reflected box from its live *)
(* domain theorem, and preserves the legacy split/glue and final assembly.     *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;

open Candle_cv_polynomial_expr_dim_jet_prove;;
open Candle_cv_flyspeck_nonlinear_driver;;

let candle_reflected_real_axioms_before = axioms ();;
let candle_reflected_real_search_options =
  Candle_informal_search_options.make
    !candle_nl_capture_params.raw_intervals0 1e-10 200 6 0;;

let candle_reflected_real_search_functions =
  map
    (fun f -> Candle_informal_verifier_record.f f,
      Candle_informal_verifier_record.taylor f)
    candle_nl_capture_informal_functions;;

let candle_reflected_real_informal_domain =
  Informal_taylor.mk_m_center_domain
    6 candle_nl_capture_xx2 candle_nl_capture_zz2;;

let candle_reflected_real_certificate =
  Informal_search.construct_certificate
    candle_reflected_real_search_options
    candle_reflected_real_informal_domain
    candle_reflected_real_search_functions;;
let _ =
  print_endline "CANDLE_CV_REAL_FLYSPECK_DRIVER_PHASE search-complete";;

let candle_reflected_real_stats =
  Certificate.result_stats candle_reflected_real_certificate;;

if candle_reflected_real_stats.pass <> 16 ||
   candle_reflected_real_stats.pass_raw <> 0 ||
   candle_reflected_real_stats.pass_mono <> 0 ||
   candle_reflected_real_stats.mono <> 0 ||
   candle_reflected_real_stats.glue <> 15 ||
   candle_reflected_real_stats.glue_convex <> 0 then
  failwith "reflected real driver: certificate shape drift";;

let candle_reflected_real_precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 candle_nl_capture_informal_functions
    candle_reflected_real_certificate
    candle_nl_capture_xx2 candle_nl_capture_zz2;;
let _ =
  print_endline "CANDLE_CV_REAL_FLYSPECK_DRIVER_PHASE adaptive-complete";;

let candle_reflected_real_function_index = 1;;
let candle_reflected_real_function =
  List.nth candle_nl_capture_functions candle_reflected_real_function_index;;

let candle_reflected_real_prepared =
  candle_q_dim_poly_jet_prepare_six candle_reflected_real_function;;

let _ =
  print_endline "CANDLE_CV_REAL_FLYSPECK_DRIVER_PHASE prepare-complete";;

if length (dest_list candle_reflected_real_prepared.program_term) <> 87 then
  failwith "reflected real driver: compiled program drift";;

let candle_reflected_real_leaf_count = ref 0;;
let candle_reflected_real_precisions = ref ([]:int list);;

let _ =
  candle_reflected_nl_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CV_REAL_FLYSPECK_DRIVER_PROFILE leaf=" ^
         string_of_int (!candle_reflected_real_leaf_count + 1) ^
         " event=" ^ event));;

let candle_reflected_real_leaf_callback
    status function_index raw_flag _ domain_th =
  if raw_flag then
    failwith "reflected real driver: raw pass is unsupported";
  if function_index <> candle_reflected_real_function_index then
    failwith "reflected real driver: unexpected selected function";
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_DRIVER_PROFILE leaf=" ^
     string_of_int (!candle_reflected_real_leaf_count + 1) ^
     " event=begin");
  let theorem =
    candle_reflected_nl_source_pass candle_reflected_real_prepared domain_th in
  candle_reflected_real_leaf_count := !candle_reflected_real_leaf_count + 1;
  candle_reflected_real_precisions :=
    status.pp :: !candle_reflected_real_precisions;
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_DRIVER_PROFILE leaf=" ^
     string_of_int !candle_reflected_real_leaf_count ^
     " event=end");
  theorem;;

let candle_reflected_real_full_pass =
  candle_reflected_nl_verify_disj_raw0
    candle_nl_capture_dimension 6 candle_nl_capture_formal_functions
    candle_reflected_real_leaf_callback candle_reflected_real_precision_tree
    candle_nl_capture_xx1 candle_nl_capture_zz1;;
let _ =
  print_endline "CANDLE_CV_REAL_FLYSPECK_DRIVER_PHASE replay-complete";;

let candle_reflected_real_expanded_general =
  M_verifier_main.normalize_disj_result
    true candle_nl_capture_functions candle_nl_capture_variable_vector
    candle_nl_capture_standard candle_nl_capture_domain_subset
    candle_reflected_real_full_pass;;

let candle_reflected_real_expanded_specific =
  let th = SPEC_ALL candle_reflected_real_expanded_general in
  let bridge =
    TAUT (mk_imp (concl th,candle_nl_capture_converted)) in
  MP bridge th;;

let candle_reflected_real_case_theorem =
  REWRITE_RULE[GSYM candle_nl_capture_expansion]
    candle_reflected_real_expanded_specific;;

let candle_reflected_real_final_theorem =
  (SPEC_ALL o REWRITE_RULE[GSYM candle_nl_capture_reconstruction])
    candle_reflected_real_case_theorem;;
let _ =
  print_endline "CANDLE_CV_REAL_FLYSPECK_DRIVER_PHASE assembly-complete";;

let candle_reflected_real_pass_functions,
    candle_reflected_real_pass_domain =
  M_verifier.dest_m_cell_list_pass (concl candle_reflected_real_full_pass);;

let candle_reflected_real_root_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl
      (M_taylor.mk_m_center_domain
        candle_nl_capture_dimension 6
        candle_nl_capture_xx1 candle_nl_capture_zz1));;

if !candle_reflected_real_leaf_count <> 16 ||
   length !candle_reflected_real_precisions <> 16 ||
   length (filter (fun pp -> pp = 2) !candle_reflected_real_precisions) <> 12 ||
   length (filter (fun pp -> pp = 3) !candle_reflected_real_precisions) <> 4 ||
   candle_reflected_real_pass_functions <>
     [candle_reflected_real_function] ||
   not (aconv candle_reflected_real_pass_domain
          candle_reflected_real_root_domain) ||
   hyp candle_reflected_real_full_pass <> [] ||
   hyp candle_reflected_real_final_theorem <> [] ||
   concl candle_reflected_real_final_theorem <>
     candle_nonlinear_first_leaf_target then
  failwith "reflected real driver: final theorem interface mismatch";;

let candle_reflected_real_axioms_after = axioms ();;
if length candle_reflected_real_axioms_after <>
     length candle_reflected_real_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_reflected_real_axioms_before)
       candle_reflected_real_axioms_after) then
  failwith "reflected real driver: changed the global axiom set";;

let _ =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_DRIVER_RESULT programs=1 instructions=87 " ^
     "leaves=" ^ string_of_int !candle_reflected_real_leaf_count ^
     " glues=15 theorem_md5=" ^
     Digest.to_hex
       (Digest.string (string_of_thm candle_reflected_real_final_theorem)));;

let _ = print_endline "CANDLE_CV_REAL_FLYSPECK_DRIVER_OK";;
