(* ========================================================================== *)
(* Focused structural probe: treat Flyspeck's opaque [hminus] as an extra    *)
(* authenticated interval parameter.                                         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This performs no numerical certificate work.  *)
(* It tests the source-language part of the proposed general bridge: prove a  *)
(* checker result uniformly over a narrow interval parameter, then specialize *)
(* that parameter to [hminus] using Flyspeck's proved interval enclosure.     *)
(* ========================================================================== *)

module Candle_cv_analytic_expr_hminus_parameter_support_probe = struct

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_analytic_expr_reify;;
open Candle_cv_exact_interval_reify;;

let rec candle_nl_hminus_parameter_string_mem needle values =
  match values with
  | [] -> false
  | value :: rest ->
      needle = value ||
      candle_nl_hminus_parameter_string_mem needle rest;;

let candle_nl_hminus_parameter_union left right =
  itlist
    (fun value result ->
      if candle_nl_hminus_parameter_string_mem value result then result
      else value :: result)
    left right;;

let candle_nl_hminus_parameter_head tm =
  let head,_ = strip_comb tm in
  try fst (dest_const head)
  with Failure _ ->
    if is_var head then "VARIABLE_HEAD" else "NONCONSTANT_HEAD";;

let rec candle_nl_hminus_parameter_scan_expression variables tm =
  if candle_analytic_is_pi_half tm ||
     candle_analytic_is_pi_half_expanded tm ||
     candle_analytic_is_pi tm ||
     candle_analytic_is_acs_third tm then []
  else if candle_q_is_unary `(--):real->real` tm ||
          candle_q_is_unary `inv:real->real` tm ||
          candle_q_is_unary `sqrt:real->real` tm ||
          candle_q_is_unary `atn:real->real` tm then
    candle_nl_hminus_parameter_scan_expression variables (rand tm)
  else if candle_q_is_binary `(+):real->real->real` tm then
    let left,right = candle_q_dest_binary `(+):real->real->real` tm in
    candle_nl_hminus_parameter_union
      (candle_nl_hminus_parameter_scan_expression variables left)
      (candle_nl_hminus_parameter_scan_expression variables right)
  else if candle_q_is_binary `(-):real->real->real` tm then
    let left,right = candle_q_dest_binary `(-):real->real->real` tm in
    candle_nl_hminus_parameter_union
      (candle_nl_hminus_parameter_scan_expression variables left)
      (candle_nl_hminus_parameter_scan_expression variables right)
  else if candle_q_is_binary `(*):real->real->real` tm then
    let left,right = candle_q_dest_binary `(*):real->real->real` tm in
    candle_nl_hminus_parameter_union
      (candle_nl_hminus_parameter_scan_expression variables left)
      (candle_nl_hminus_parameter_scan_expression variables right)
  else if candle_q_is_binary `(/):real->real->real` tm then
    let left,right = candle_q_dest_binary `(/):real->real->real` tm in
    candle_nl_hminus_parameter_union
      (candle_nl_hminus_parameter_scan_expression variables left)
      (candle_nl_hminus_parameter_scan_expression variables right)
  else if candle_q_is_binary `(pow):real->num->real` tm then
    let base,exponent =
      candle_q_dest_binary `(pow):real->num->real` tm in
    if is_numeral exponent && dest_small_numeral exponent = 2 then
      candle_nl_hminus_parameter_scan_expression variables base
    else ["UNSUPPORTED_POWER"]
  else if candle_analytic_polynomial_candidate variables tm then []
  else [candle_nl_hminus_parameter_head tm];;

let candle_nl_hminus_parameter_join separator values =
  match values with
  | [] -> ""
  | first :: rest ->
      itlist (fun value result -> value ^ separator ^ result) rest first;;

let candle_nl_hminus_parameter_formula target =
  let stripped = snd (strip_forall target) in
  let head,arguments = strip_comb stripped in
  if is_const head then
    match fst (dest_const head),arguments with
    | "ineqm",[_;_;formula] -> formula
    | "ineq",[_;formula] -> formula
    | _ -> stripped
  else stripped;;

let candle_nl_hminus_parameter_defs =
  candle_direct_flyspeck_defs @
  Break_case_exec.nonlin_rewrites @
  map snd Break_case_exec.trig_expansions1 @
  [Sphere.sqrt8;
   Sphere.sqrt2;
   Sphere.sqrt3;
   Sphere.tau0;
   Sphere.mm1;
   Sphere.mm2;
   Sphere.h0;
   Sphere.hplus;
   Sphere.rh0;
   Sphere.rotate4;
   Sphere.rotate5;
   Sphere.rotate6];;

let candle_nl_hminus_parameter = `candle_hminus_parameter:real`;;

let candle_nl_hminus_parameter_source_fixture source_id =
  let _,preparation,needs_delta = Break_case_exec.get_case source_id in
  let target =
    Break_case_exec.run_generic
      (fun selected -> preparation selected) needs_delta source_id in
  let reconstruction = candle_direct_ineqm_conv target in
  if not (aconv (lhand (concl reconstruction)) target) then
    failwith "hminus parameter fixture: reconstruction source mismatch";
  let case_term = rand (concl reconstruction) in
  let expansion =
    (REWRITE_CONV
       [TAUT `(P ==> Q) <=> (~P \/ Q)`;
        REAL_ARITH `~(a > b:real) <=> a <= b`;
        REAL_ARITH `~(a < b:real) <=> b <= a`;
        REAL_ARITH `~(a >= b:real) <=> a < b`;
        REAL_ARITH `~(a <= b:real) <=> b < a`]
     THENC candle_direct_expand_ineq_case
     THENC REWRITE_CONV candle_nl_hminus_parameter_defs
     THENC DEPTH_CONV let_CONV)
      case_term in
  let converted = rand (concl expansion) in
  let inequality,variable_names,bounds =
    M_verifier_main.dest_ineq converted in
  let standard =
    M_verifier_main.mk_standard_ineq
      [REAL_POW_1; real_pow] inequality in
  let disjuncts = striplist dest_disj ((lhand o concl) standard) in
  target,reconstruction,expansion,converted,variable_names,bounds,standard,
  map lhand disjuncts;;

let candle_nl_hminus_parameter_source_expressions source_id =
  let _,_,_,_,_,_,_,expressions =
    candle_nl_hminus_parameter_source_fixture source_id in
  expressions;;

let candle_nl_hminus_parameter_scan_source source_id =
  let expressions =
    candle_nl_hminus_parameter_source_expressions source_id in
  let parameterized =
    map
      (subst [candle_nl_hminus_parameter,`hminus:real`])
      expressions in
  let functions,_ = candle_direct_exprs_to_vector_fun parameterized in
  let dimension = length (unions (map frees parameterized)) in
  let function_vector =
    match functions with
    | [] -> failwith "empty hminus-parameter expression list"
    | first :: _ -> fst (dest_abs first) in
  let variables =
    Candle_cv_polynomial_expr_flyspeck_reify.candle_poly_vector_components
      function_vector dimension in
  let unsupported =
    itlist
      (fun function_term result ->
        let _,body = dest_abs function_term in
        candle_nl_hminus_parameter_union
          (candle_nl_hminus_parameter_scan_expression variables body)
          result)
      functions [] in
  dimension,length expressions,unsupported;;

let candle_nl_hminus_parameter_probe_ids =
  ["prep-GLFVCVK4 2477216213 split(23/64)";
   "prep-GLFVCVK4 2477216213 split(24/64)";
   "prep-GLFVCVK4 2477216213 split(25/64)"];;

let candle_nl_hminus_parameter_probe_emit source_id =
  let started = Unix.gettimeofday () in
  try
    let dimension,disjuncts,unsupported =
      candle_nl_hminus_parameter_scan_source source_id in
    print_endline
      ("CANDLE_NL_HMINUS_PARAMETER_SUPPORT_PROBE" ^
       " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
       " dimension=" ^ string_of_int dimension ^
       " disjuncts=" ^ string_of_int disjuncts ^
       " unsupported=" ^
         candle_nl_hminus_parameter_join "," unsupported ^
       " elapsed_seconds=" ^
         string_of_float (Unix.gettimeofday () -. started))
  with Failure message ->
    print_endline
      ("CANDLE_NL_HMINUS_PARAMETER_SUPPORT_PROBE_ERROR" ^
       " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
       " message=" ^ message);;

let _ =
  do_list candle_nl_hminus_parameter_probe_emit
    candle_nl_hminus_parameter_probe_ids;;

end;;
