(* ========================================================================== *)
(* Read-only coverage scan for the direct Flyspeck nonlinear source corpus.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This deliberately performs no certificate     *)
(* computation and proves no inequality.  It applies the same source          *)
(* normalization used by the reflected fixtures, then checks whether every   *)
(* resulting real expression is structurally accepted by the current proved  *)
(* analytic expression language.  Unsupported heads are reported explicitly. *)
(* ========================================================================== *)

(* The scan is an injected late-state diagnostic.  Its driver must load the
   direct-source compatibility module and analytic reifier first.  Keeping
   that boundary explicit avoids asking the authenticated loader to replace
   a logical source ID already present in an older sealed checkpoint. *)

module Candle_cv_analytic_expr_corpus_support_scan = struct

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_analytic_expr_reify;;
open Candle_cv_exact_interval_reify;;

let rec candle_nl_corpus_scan_string_mem needle values =
  match values with
  | [] -> false
  | value :: rest ->
      needle = value || candle_nl_corpus_scan_string_mem needle rest;;

let candle_nl_corpus_scan_union left right =
  itlist
    (fun value result ->
      if candle_nl_corpus_scan_string_mem value result then result
      else value :: result)
    left right;;

let candle_nl_corpus_scan_head tm =
  let head,_ = strip_comb tm in
  try fst (dest_const head)
  with Failure _ ->
    if is_var head then "VARIABLE_HEAD" else "NONCONSTANT_HEAD";;

let rec candle_nl_corpus_scan_expression variables tm =
  if candle_analytic_is_pi_half tm ||
     candle_analytic_is_pi_half_expanded tm ||
     candle_analytic_is_pi tm ||
     candle_analytic_is_acs_third tm then []
  else if candle_q_is_unary `(--):real->real` tm ||
          candle_q_is_unary `inv:real->real` tm ||
          candle_q_is_unary `sqrt:real->real` tm ||
          candle_q_is_unary `atn:real->real` tm then
    candle_nl_corpus_scan_expression variables
      (rand tm)
  else if candle_q_is_binary `(+):real->real->real` tm then
    let left,right = candle_q_dest_binary `(+):real->real->real` tm in
    candle_nl_corpus_scan_union
      (candle_nl_corpus_scan_expression variables left)
      (candle_nl_corpus_scan_expression variables right)
  else if candle_q_is_binary `(-):real->real->real` tm then
    let left,right = candle_q_dest_binary `(-):real->real->real` tm in
    candle_nl_corpus_scan_union
      (candle_nl_corpus_scan_expression variables left)
      (candle_nl_corpus_scan_expression variables right)
  else if candle_q_is_binary `(*):real->real->real` tm then
    let left,right = candle_q_dest_binary `(*):real->real->real` tm in
    candle_nl_corpus_scan_union
      (candle_nl_corpus_scan_expression variables left)
      (candle_nl_corpus_scan_expression variables right)
  else if candle_q_is_binary `(/):real->real->real` tm then
    let left,right = candle_q_dest_binary `(/):real->real->real` tm in
    candle_nl_corpus_scan_union
      (candle_nl_corpus_scan_expression variables left)
      (candle_nl_corpus_scan_expression variables right)
  else if candle_q_is_binary `(pow):real->num->real` tm then
    let base,exponent = candle_q_dest_binary `(pow):real->num->real` tm in
    if is_numeral exponent && dest_small_numeral exponent = 2 then
      candle_nl_corpus_scan_expression variables base
    else ["UNSUPPORTED_POWER"]
  else if candle_analytic_polynomial_candidate variables tm then []
  else [candle_nl_corpus_scan_head tm];;

let candle_nl_corpus_scan_join separator values =
  match values with
  | [] -> ""
  | first :: rest ->
      itlist (fun value result -> value ^ separator ^ result) rest first;;

(* Reject only source-level heads that the current direct compatibility
   conversion certainly does not expand and the analytic language does not
   consume directly.  This is an acceleration, not an acceptance test: every
   source that survives it still goes through authenticated reconstruction,
   standardization, and the exact structural scan below. *)
let candle_nl_corpus_scan_raw_allowed =
  ["!"; ","; "BIT0"; "BIT1"; "CONS"; "DECIMAL"; "NIL";
   "NUMERAL"; "\\/"; "_0"; "ineq";
   "real_add"; "real_div"; "real_le"; "real_lt"; "real_mul";
   "real_neg"; "real_of_num"; "real_sub"; "pow";
   "delta_x"; "delta_x4"; "delta4_squared_x"; "x1_delta_x";
   "unit6"; "rho";
   "sqrt_x1"; "sqrt_x2"; "sqrt_x3"; "sqrt_x4"; "sqrt_x5";
   "sqrt_x6";
   "dihatn_x"; "dih2atn_x"; "dih3atn_x";
   "rhazimatn_x"; "rhazim2atn_x"; "rhazim3atn_x";
   "sol0"; "const1"; "rotate2"; "rotate3";
   "pi"; "acs"; "atn"; "inv"; "sqrt"];;

let candle_nl_corpus_scan_raw_unsupported source =
  candle_nl_corpus_scan_union
    (filter
      (fun name ->
        not (candle_nl_corpus_scan_string_mem
               name candle_nl_corpus_scan_raw_allowed))
      (Break_case_exec.get_const_names source)) [];;

let candle_nl_corpus_scan_source source_id =
  let source = Break_case_exec.get_ineq source_id in
  let raw_unsupported =
    candle_nl_corpus_scan_raw_unsupported source in
  if not (raw_unsupported = []) then
    0,0,map (fun name -> "RAW_" ^ name) raw_unsupported
  else
  let _,_,source_case = Break_case_exec.simple_dest_ineq source in
  let expansion =
    (REWRITE_CONV
       [TAUT `(P ==> Q) <=> (~P \/ Q)`;
        REAL_ARITH `~(a > b:real) <=> a <= b`;
        REAL_ARITH `~(a < b:real) <=> b <= a`;
        REAL_ARITH `~(a >= b:real) <=> a < b`;
        REAL_ARITH `~(a <= b:real) <=> b < a`]
     THENC candle_direct_expand_ineq_case)
      source_case in
  let inequality = rand (concl expansion) in
  let standard =
    M_verifier_main.mk_standard_ineq
      [REAL_POW_1; real_pow] inequality in
  let disjuncts =
    striplist dest_disj ((lhand o concl) standard) in
  let expressions = map lhand disjuncts in
  let functions,_ = candle_direct_exprs_to_vector_fun expressions in
  let dimension = length (unions (map frees expressions)) in
  let function_vector =
    match functions with
    | [] -> failwith "empty standardized expression list"
    | first :: _ -> fst (dest_abs first) in
  let variables =
    Candle_cv_polynomial_expr_flyspeck_reify.candle_poly_vector_components
      function_vector dimension in
  let unsupported =
    itlist
      (fun function_term result ->
        let _,body = dest_abs function_term in
        candle_nl_corpus_scan_union
          (candle_nl_corpus_scan_expression variables body) result)
      functions [] in
  dimension,length disjuncts,unsupported;;

let candle_nl_corpus_scan_started = Unix.gettimeofday ();;
let candle_nl_corpus_scan_ok = ref 0;;
let candle_nl_corpus_scan_failed = ref 0;;
let candle_nl_corpus_scan_dim6 = ref 0;;
let candle_nl_corpus_scan_dim9 = ref 0;;
let candle_nl_corpus_scan_other_dim = ref 0;;

let candle_nl_corpus_scan_emit source_id =
  try
    let dimension,disjuncts,unsupported =
      candle_nl_corpus_scan_source source_id in
    if dimension = 0 then ()
    else if dimension = 6 then
      candle_nl_corpus_scan_dim6 := !candle_nl_corpus_scan_dim6 + 1
    else if dimension = 9 then
      candle_nl_corpus_scan_dim9 := !candle_nl_corpus_scan_dim9 + 1
    else
      candle_nl_corpus_scan_other_dim :=
        !candle_nl_corpus_scan_other_dim + 1;
    if unsupported = [] then begin
      candle_nl_corpus_scan_ok := !candle_nl_corpus_scan_ok + 1;
      print_endline
        ("CANDLE_NL_CORPUS_SUPPORT|OK|" ^ source_id ^ "|" ^
         string_of_int dimension ^ "|" ^ string_of_int disjuncts ^ "|")
    end else begin
      candle_nl_corpus_scan_failed := !candle_nl_corpus_scan_failed + 1;
      print_endline
        ("CANDLE_NL_CORPUS_SUPPORT|UNSUPPORTED|" ^ source_id ^ "|" ^
         string_of_int dimension ^ "|" ^ string_of_int disjuncts ^ "|" ^
         candle_nl_corpus_scan_join "," unsupported)
    end
  with Failure message -> begin
    candle_nl_corpus_scan_failed := !candle_nl_corpus_scan_failed + 1;
    print_endline
      ("CANDLE_NL_CORPUS_SUPPORT|ERROR|" ^ source_id ^ "|0|0|" ^ message)
  end;;

let _ =
  do_list candle_nl_corpus_scan_emit Break_case_exec.all_idv;;

let candle_nl_corpus_scan_elapsed =
  Unix.gettimeofday () -. candle_nl_corpus_scan_started;;

print_endline
  ("CANDLE_NL_CORPUS_SUPPORT_SUMMARY DEVELOPMENT_NON_RELEASE" ^
   " sources=" ^ string_of_int (length Break_case_exec.all_idv) ^
   " supported=" ^ string_of_int !candle_nl_corpus_scan_ok ^
   " unsupported_or_error=" ^ string_of_int !candle_nl_corpus_scan_failed ^
   " dim6=" ^ string_of_int !candle_nl_corpus_scan_dim6 ^
   " dim9=" ^ string_of_int !candle_nl_corpus_scan_dim9 ^
   " other_dim=" ^ string_of_int !candle_nl_corpus_scan_other_dim ^
   " elapsed_seconds=" ^ string_of_float candle_nl_corpus_scan_elapsed);;

end;;
