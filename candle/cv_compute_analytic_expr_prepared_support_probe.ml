(* ========================================================================== *)
(* Focused proved-preparation coverage probe for Flyspeck NL source terms.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This applies Flyspeck's existing preparation  *)
(* tactic to a source goal and inspects the resulting goal expression.  It   *)
(* neither runs a numerical certificate nor treats the tactic as an oracle:  *)
(* every goal transformation is performed by the ordinary HOL tactic stack.  *)
(* ========================================================================== *)

(* Injected into a sealed late state.  Its driver loads the direct-source
   compatibility and corpus-scan support modules explicitly before this
   fragment, so the authenticated loader never substitutes a source node. *)

module Candle_cv_analytic_expr_prepared_support_probe = struct

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_analytic_expr_corpus_support_scan;;

let candle_nl_prepared_formula target =
  let stripped = snd (strip_forall target) in
  let head,arguments = strip_comb stripped in
  if is_const head then
    match fst (dest_const head),arguments with
    | "ineqm",[_;_;formula] -> formula
    | "ineq",[_;formula] -> formula
    | _ -> stripped
  else stripped;;

let candle_nl_prepared_scan_source source_id =
  let _,preparation,needs_delta = Break_case_exec.get_case source_id in
  let target =
    Break_case_exec.run_generic
      (fun selected -> preparation selected) needs_delta source_id in
  let formula = candle_nl_prepared_formula target in
  let expansion =
    (REWRITE_CONV
       [TAUT `(P ==> Q) <=> (~P \/ Q)`;
        REAL_ARITH `~(a > b:real) <=> a <= b`;
        REAL_ARITH `~(a < b:real) <=> b <= a`;
        REAL_ARITH `~(a >= b:real) <=> a < b`;
        REAL_ARITH `~(a <= b:real) <=> b < a`]
     THENC candle_direct_expand_ineq_case)
      formula in
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
    | [] -> failwith "empty prepared expression list"
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
  dimension,length disjuncts,unsupported,target;;

let candle_nl_prepared_probe_id = "prep-8657368829";;
let candle_nl_prepared_probe_started = Unix.gettimeofday ();;
let candle_nl_prepared_probe_dimension,
    candle_nl_prepared_probe_disjuncts,
    candle_nl_prepared_probe_unsupported,
    candle_nl_prepared_probe_target =
  candle_nl_prepared_scan_source candle_nl_prepared_probe_id;;
let candle_nl_prepared_probe_seconds =
  Unix.gettimeofday () -. candle_nl_prepared_probe_started;;

print_endline
  ("CANDLE_NL_PREPARED_SUPPORT_PROBE DEVELOPMENT_NON_RELEASE" ^
   " source_id=" ^ candle_nl_prepared_probe_id ^
   " dimension=" ^ string_of_int candle_nl_prepared_probe_dimension ^
   " disjuncts=" ^ string_of_int candle_nl_prepared_probe_disjuncts ^
   " unsupported=" ^
     candle_nl_corpus_scan_join "," candle_nl_prepared_probe_unsupported ^
   " elapsed_seconds=" ^ string_of_float candle_nl_prepared_probe_seconds);;

end;;
