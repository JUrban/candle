(* ========================================================================== *)
(* Finish one genuine Flyspeck nonlinear inequality from prepared functions.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The real-functions checkpoint has already      *)
(* authenticated the source, reconstructed its three scalar functions, and    *)
(* built their formal and informal verifier records.  This continuation does   *)
(* certificate search, a complete leaf proof, full certificate replay, and     *)
(* final source-theorem assembly without repeating that preparation.            *)
(* ========================================================================== *)

let candle_nl_capture_search_options =
  Candle_informal_search_options.make
    !candle_nl_capture_params.raw_intervals0 1e-10 200 6 0;;

let candle_nl_capture_search_functions =
  map
    (fun f -> Candle_informal_verifier_record.f f,
      Candle_informal_verifier_record.taylor f)
    candle_nl_capture_informal_functions;;

let candle_nl_capture_informal_domain =
  Informal_taylor.mk_m_center_domain
    6 candle_nl_capture_xx2 candle_nl_capture_zz2;;

let candle_nl_capture_search_started = Unix.gettimeofday ();;
let candle_nl_capture_certificate =
  Informal_search.construct_certificate
    candle_nl_capture_search_options
    candle_nl_capture_informal_domain
    candle_nl_capture_search_functions;;
let candle_nl_capture_search_seconds =
  Unix.gettimeofday () -. candle_nl_capture_search_started;;

let candle_nl_capture_stats =
  Certificate.result_stats candle_nl_capture_certificate;;

if candle_nl_capture_stats.pass <> 16 ||
   candle_nl_capture_stats.pass_raw <> 0 ||
   candle_nl_capture_stats.pass_mono <> 0 ||
   candle_nl_capture_stats.mono <> 0 ||
   candle_nl_capture_stats.glue <> 15 ||
   candle_nl_capture_stats.glue_convex <> 0 then
  failwith "real-leaf certificate shape drift";;

let candle_nl_capture_adaptive_started = Unix.gettimeofday ();;
let candle_nl_capture_precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 candle_nl_capture_informal_functions
    candle_nl_capture_certificate
    candle_nl_capture_xx2 candle_nl_capture_zz2;;
let candle_nl_capture_adaptive_seconds =
  Unix.gettimeofday () -. candle_nl_capture_adaptive_started;;

let candle_nl_capture_root_domain =
  M_taylor.mk_m_center_domain
    candle_nl_capture_dimension 6
    candle_nl_capture_xx1 candle_nl_capture_zz1;;

let rec candle_nl_capture_first_leaf path domain_th tree =
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      if raw_flag then failwith "unexpected raw first nonlinear leaf"
      else rev path,status,function_index,domain_th
  | P_result_glue (status,split_index,convex_flag,left,_) ->
      if convex_flag then failwith "unexpected convex first nonlinear branch"
      else
        let left_domain,_ =
          M_verifier.split_domain
            candle_nl_capture_dimension 6 (split_index + 1) domain_th in
        candle_nl_capture_first_leaf
          ((status.pp,split_index + 1) :: path) left_domain left
  | P_result_mono _ ->
      failwith "unexpected monotonicity node in first nonlinear branch"
  | P_result_ref _ ->
      failwith "unexpected reference node in first nonlinear branch";;

let candle_nl_capture_path,
    candle_nl_capture_status,
    candle_nl_capture_function_index,
    candle_nl_capture_leaf_domain =
  candle_nl_capture_first_leaf [] candle_nl_capture_root_domain
    candle_nl_capture_precision_tree;;

let candle_nl_capture_selected_function =
  List.nth candle_nl_capture_functions candle_nl_capture_function_index;;

let candle_nl_capture_selected_scalar_source =
  List.nth candle_nl_capture_lhs_terms candle_nl_capture_function_index;;

let candle_nl_capture_selected_verifier =
  List.nth candle_nl_capture_formal_functions
    candle_nl_capture_function_index;;

let candle_nl_capture_taylor_started = Unix.gettimeofday ();;
let candle_nl_capture_taylor =
  candle_nl_capture_selected_verifier.taylor
    candle_nl_capture_status.pp candle_nl_capture_status.pp
    candle_nl_capture_leaf_domain;;
let candle_nl_capture_taylor_seconds =
  Unix.gettimeofday () -. candle_nl_capture_taylor_started;;

let candle_nl_capture_pass_started = Unix.gettimeofday ();;
let candle_nl_capture_pass =
  M_verifier.m_taylor_cell_list_pass
    candle_nl_capture_dimension candle_nl_capture_status.pp
    candle_nl_capture_taylor;;
let candle_nl_capture_pass_seconds =
  Unix.gettimeofday () -. candle_nl_capture_pass_started;;

let candle_nl_capture_full_formal_started = Unix.gettimeofday ();;
let candle_nl_capture_full_pass =
  M_verifier.m_p_verify_disj_raw0
    candle_nl_capture_dimension 6
    candle_nl_capture_formal_functions
    candle_nl_capture_precision_tree
    candle_nl_capture_xx1 candle_nl_capture_zz1;;
let candle_nl_capture_full_formal_seconds =
  Unix.gettimeofday () -. candle_nl_capture_full_formal_started;;

let candle_nl_capture_assembly_started = Unix.gettimeofday ();;
let candle_nl_capture_expanded_general =
  M_verifier_main.normalize_disj_result
    true candle_nl_capture_functions candle_nl_capture_variable_vector
    candle_nl_capture_standard candle_nl_capture_domain_subset
    candle_nl_capture_full_pass;;

(* This is Azure main_verifier.hl's exact theorem assembly, made fail-closed:
   specialize the verifier result to the source's variable presentation, then
   discharge the definition expansion and Break_case reconstruction in turn. *)
let candle_nl_capture_expanded_specific =
  let th = SPEC_ALL candle_nl_capture_expanded_general in
  let bridge =
    TAUT
      (mk_imp
        (concl th,candle_nl_capture_converted)) in
  MP bridge th;;

let candle_nl_capture_case_theorem =
  REWRITE_RULE[GSYM candle_nl_capture_expansion]
    candle_nl_capture_expanded_specific;;

let candle_nl_capture_final_theorem =
  (SPEC_ALL o REWRITE_RULE[GSYM candle_nl_capture_reconstruction])
    candle_nl_capture_case_theorem;;
let candle_nl_capture_assembly_seconds =
  Unix.gettimeofday () -. candle_nl_capture_assembly_started;;

let candle_nl_capture_function,
    candle_nl_capture_taylor_domain,
    candle_nl_capture_center,
    candle_nl_capture_radius,
    candle_nl_capture_value_bounds,
    candle_nl_capture_derivative_bounds,
    candle_nl_capture_second_derivative_bounds =
  M_taylor.dest_m_taylor (concl candle_nl_capture_taylor);;

let candle_nl_capture_leaf_box,_,_ =
  M_taylor.dest_m_cell_domain (concl candle_nl_capture_leaf_domain);;
let candle_nl_capture_leaf_lower,candle_nl_capture_leaf_upper =
  dest_pair candle_nl_capture_leaf_box;;
let candle_nl_capture_leaf_lower_list =
  mk_real_list (dest_vector candle_nl_capture_leaf_lower);;
let candle_nl_capture_leaf_upper_list =
  mk_real_list (dest_vector candle_nl_capture_leaf_upper);;
let candle_nl_capture_pass_functions,candle_nl_capture_pass_domain =
  M_verifier.dest_m_cell_list_pass (concl candle_nl_capture_pass);;

if candle_nl_capture_function <> candle_nl_capture_selected_function ||
   candle_nl_capture_taylor_domain <> candle_nl_capture_leaf_box ||
   candle_nl_capture_pass_functions <>
     [candle_nl_capture_selected_function] ||
   candle_nl_capture_pass_domain <> candle_nl_capture_leaf_box ||
   hyp candle_nl_capture_domain_subset <> [] ||
   hyp candle_nl_capture_leaf_domain <> [] ||
   hyp candle_nl_capture_taylor <> [] ||
   hyp candle_nl_capture_pass <> [] ||
   hyp candle_nl_capture_full_pass <> [] ||
   hyp candle_nl_capture_final_theorem <> [] ||
   concl candle_nl_capture_final_theorem <>
     candle_nonlinear_first_leaf_target then
  failwith "real-leaf theorem interface mismatch";;

let candle_nl_capture_axioms_after = axioms ();;
if length candle_nl_capture_axioms_after <>
     length candle_nl_capture_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_nl_capture_axioms_before)
       candle_nl_capture_axioms_after) then
  failwith "real-leaf capture changed the global axiom set";;

let candle_nl_capture_path_string =
  String.concat ","
    (map
      (fun (precision,index) ->
        string_of_int precision ^ ":" ^ string_of_int index)
      candle_nl_capture_path);;

let _ =
  print_endline
    ("CANDLE_NL_REAL_LEAF_META function_index=" ^
     string_of_int candle_nl_capture_function_index ^
     " pp=" ^ string_of_int candle_nl_capture_status.pp ^
     " path=" ^ candle_nl_capture_path_string ^
     " search_seconds=" ^ string_of_float candle_nl_capture_search_seconds ^
     " adaptive_seconds=" ^
       string_of_float candle_nl_capture_adaptive_seconds ^
     " taylor_seconds=" ^ string_of_float candle_nl_capture_taylor_seconds ^
     " pass_seconds=" ^ string_of_float candle_nl_capture_pass_seconds ^
     " full_formal_seconds=" ^
       string_of_float candle_nl_capture_full_formal_seconds ^
     " assembly_seconds=" ^
       string_of_float candle_nl_capture_assembly_seconds ^
     " total_seconds=" ^
       string_of_float
         (Unix.gettimeofday () -. candle_nl_capture_started));;

let _ =
  print_endline
    ("CANDLE_NL_REAL_LEAF_VARIABLE_ORDER " ^
     String.concat "," candle_nl_capture_sorted_variable_names);;

let _ =
  print_endline
    ("CANDLE_NL_REAL_CERTIFICATE pass=" ^
     string_of_int candle_nl_capture_stats.pass ^
     " pass_raw=" ^ string_of_int candle_nl_capture_stats.pass_raw ^
     " pass_mono=" ^ string_of_int candle_nl_capture_stats.pass_mono ^
     " mono=" ^ string_of_int candle_nl_capture_stats.mono ^
     " glue=" ^ string_of_int candle_nl_capture_stats.glue ^
     " glue_convex=" ^
       string_of_int candle_nl_capture_stats.glue_convex);;

let _ =
  print_endline
    ("CANDLE_NL_REAL_FINAL_THEOREM_TEXT_MD5 " ^
     Digest.to_hex
       (Digest.string
         (string_of_thm candle_nl_capture_final_theorem)));;

let _ = candle_nl_capture_print_term
  "selected_function" candle_nl_capture_selected_function;;
let _ = candle_nl_capture_print_term
  "selected_scalar_source" candle_nl_capture_selected_scalar_source;;
let _ = candle_nl_capture_print_term
  "leaf_lower" candle_nl_capture_leaf_lower;;
let _ = candle_nl_capture_print_term
  "leaf_upper" candle_nl_capture_leaf_upper;;
let _ = candle_nl_capture_print_term
  "leaf_lower_list" candle_nl_capture_leaf_lower_list;;
let _ = candle_nl_capture_print_term
  "leaf_upper_list" candle_nl_capture_leaf_upper_list;;
let _ = candle_nl_capture_print_term
  "center" candle_nl_capture_center;;
let _ = candle_nl_capture_print_term
  "radius" candle_nl_capture_radius;;
let _ = candle_nl_capture_print_term
  "value_bounds" candle_nl_capture_value_bounds;;
let _ = candle_nl_capture_print_term
  "derivative_bounds" candle_nl_capture_derivative_bounds;;
let _ = candle_nl_capture_print_term
  "second_derivative_bounds"
  candle_nl_capture_second_derivative_bounds;;
let _ = candle_nl_capture_print_term
  "leaf_domain_theorem" (concl candle_nl_capture_leaf_domain);;
let _ = candle_nl_capture_print_term
  "taylor_theorem" (concl candle_nl_capture_taylor);;
let _ = candle_nl_capture_print_term
  "pass_theorem" (concl candle_nl_capture_pass);;

let _ = print_endline "CANDLE_NL_REAL_INEQUALITY_COMPLETE_OK";;
let _ = print_endline "CANDLE_NL_REAL_LEAF_CAPTURE_OK";;
