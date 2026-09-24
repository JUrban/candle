(* ========================================================================== *)
(* Colocate legacy and reflected proofs of one genuine nonlinear certificate. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The checkpoint supplies one authenticated,    *)
(* already-built certificate and its live Flyspeck source functions.  This    *)
(* test reruns legacy and reflected formal verification from that same state, *)
(* assembles both public theorems, and requires exact theorem equality.        *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;

open Candle_cv_polynomial_expr_dim_jet_prove;;
open Candle_cv_flyspeck_nonlinear_driver;;

let candle_reflected_matched_axioms_before = axioms ();;

let _ = print_endline "CANDLE_CV_REAL_MATCHED_BEGIN phase=shared-plan";;
let candle_reflected_matched_search_options =
  Candle_informal_search_options.make
    !candle_nl_capture_params.raw_intervals0 1e-10 200 6 0;;
let candle_reflected_matched_search_functions =
  map
    (fun f -> Candle_informal_verifier_record.f f,
      Candle_informal_verifier_record.taylor f)
    candle_nl_capture_informal_functions;;
let candle_reflected_matched_informal_domain =
  Informal_taylor.mk_m_center_domain
    6 candle_nl_capture_xx2 candle_nl_capture_zz2;;
let candle_reflected_matched_certificate =
  Informal_search.construct_certificate
    candle_reflected_matched_search_options
    candle_reflected_matched_informal_domain
    candle_reflected_matched_search_functions;;
let candle_reflected_matched_stats =
  Certificate.result_stats candle_reflected_matched_certificate;;
if candle_reflected_matched_stats.pass <> 16 ||
   candle_reflected_matched_stats.pass_raw <> 0 ||
   candle_reflected_matched_stats.pass_mono <> 0 ||
   candle_reflected_matched_stats.mono <> 0 ||
   candle_reflected_matched_stats.glue <> 15 ||
   candle_reflected_matched_stats.glue_convex <> 0 then
  failwith "matched real driver: certificate shape drift";;
let candle_reflected_matched_precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 candle_nl_capture_informal_functions
    candle_reflected_matched_certificate
    candle_nl_capture_xx2 candle_nl_capture_zz2;;
let _ = print_endline "CANDLE_CV_REAL_MATCHED_END phase=shared-plan";;

let candle_reflected_matched_function_index = 1;;
let candle_reflected_matched_function =
  List.nth candle_nl_capture_functions
    candle_reflected_matched_function_index;;
let candle_reflected_matched_prepared =
  candle_q_dim_poly_jet_prepare_six candle_reflected_matched_function;;

let candle_reflected_matched_leaf_count = ref 0;;
let candle_reflected_matched_leaf_callback
    _ function_index raw_flag _ domain_th =
  if raw_flag then
    failwith "matched real driver: raw pass is unsupported";
  if function_index <> candle_reflected_matched_function_index then
    failwith "matched real driver: unexpected selected function";
  let theorem =
    candle_reflected_nl_source_pass
      candle_reflected_matched_prepared domain_th in
  candle_reflected_matched_leaf_count :=
    !candle_reflected_matched_leaf_count + 1;
  theorem;;

let _ = print_endline "CANDLE_CV_REAL_MATCHED_BEGIN phase=reflected-proof";;
let candle_reflected_matched_reflected_pass =
  candle_reflected_nl_verify_disj_raw0
    candle_nl_capture_dimension 6 candle_nl_capture_formal_functions
    candle_reflected_matched_leaf_callback
    candle_reflected_matched_precision_tree
    candle_nl_capture_xx1 candle_nl_capture_zz1;;
let _ = print_endline "CANDLE_CV_REAL_MATCHED_END phase=reflected-proof";;

let _ = print_endline "CANDLE_CV_REAL_MATCHED_BEGIN phase=legacy-proof";;
let candle_reflected_matched_legacy_pass =
  M_verifier.m_p_verify_disj_raw0
    candle_nl_capture_dimension 6 candle_nl_capture_formal_functions
    candle_reflected_matched_precision_tree
    candle_nl_capture_xx1 candle_nl_capture_zz1;;
let _ = print_endline "CANDLE_CV_REAL_MATCHED_END phase=legacy-proof";;

let candle_reflected_matched_assemble full_pass =
  let expanded_general =
    M_verifier_main.normalize_disj_result
      true candle_nl_capture_functions candle_nl_capture_variable_vector
      candle_nl_capture_standard candle_nl_capture_domain_subset full_pass in
  let expanded_specific =
    let th = SPEC_ALL expanded_general in
    let bridge = TAUT (mk_imp (concl th,candle_nl_capture_converted)) in
    MP bridge th in
  let case_theorem =
    REWRITE_RULE[GSYM candle_nl_capture_expansion] expanded_specific in
  (SPEC_ALL o REWRITE_RULE[GSYM candle_nl_capture_reconstruction])
    case_theorem;;

let _ = print_endline "CANDLE_CV_REAL_MATCHED_BEGIN phase=legacy-assembly";;
let candle_reflected_matched_legacy_theorem =
  candle_reflected_matched_assemble candle_reflected_matched_legacy_pass;;
let _ = print_endline "CANDLE_CV_REAL_MATCHED_END phase=legacy-assembly";;

let _ = print_endline "CANDLE_CV_REAL_MATCHED_BEGIN phase=reflected-assembly";;
let candle_reflected_matched_reflected_theorem =
  candle_reflected_matched_assemble candle_reflected_matched_reflected_pass;;
let _ = print_endline "CANDLE_CV_REAL_MATCHED_END phase=reflected-assembly";;

let candle_reflected_matched_pass_functions,
    candle_reflected_matched_pass_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_reflected_matched_reflected_pass);;

let candle_reflected_matched_root_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl
      (M_taylor.mk_m_center_domain
        candle_nl_capture_dimension 6
        candle_nl_capture_xx1 candle_nl_capture_zz1));;

if !candle_reflected_matched_leaf_count <> 16 ||
   candle_reflected_matched_pass_functions <>
     [candle_reflected_matched_function] ||
   not (aconv candle_reflected_matched_pass_domain
          candle_reflected_matched_root_domain) ||
   hyp candle_reflected_matched_legacy_pass <> [] ||
   hyp candle_reflected_matched_reflected_pass <> [] ||
   hyp candle_reflected_matched_legacy_theorem <> [] ||
   hyp candle_reflected_matched_reflected_theorem <> [] ||
   concl candle_reflected_matched_legacy_theorem <>
     candle_nonlinear_first_leaf_target ||
   concl candle_reflected_matched_reflected_theorem <>
     candle_nonlinear_first_leaf_target ||
   not
     (equals_thm
       candle_reflected_matched_legacy_theorem
       candle_reflected_matched_reflected_theorem) then
  failwith "matched real driver: theorem interface mismatch";;

let candle_reflected_matched_axioms_after = axioms ();;
if length candle_reflected_matched_axioms_after <>
     length candle_reflected_matched_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_reflected_matched_axioms_before)
       candle_reflected_matched_axioms_after) then
  failwith "matched real driver: changed the global axiom set";;

let _ =
  print_endline
    ("CANDLE_CV_REAL_MATCHED_RESULT programs=1 instructions=" ^
     string_of_int
       (length (dest_list candle_reflected_matched_prepared.program_term)) ^
     " leaves=" ^ string_of_int !candle_reflected_matched_leaf_count ^
     " glues=15 theorem_md5=" ^
     Digest.to_hex
       (Digest.string
         (string_of_thm candle_reflected_matched_reflected_theorem)));;
let _ = print_endline "CANDLE_CV_REAL_MATCHED_OK";;
