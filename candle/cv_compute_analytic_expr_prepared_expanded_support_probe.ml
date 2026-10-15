(* ========================================================================== *)
(* Proved-preparation coverage probe with Flyspeck's exported expansions.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This differs from the strict prepared scan    *)
(* only by applying existing proved Flyspeck definition theorems before the  *)
(* structural language check.  It performs no numerical certificate work.   *)
(* ========================================================================== *)

module Candle_cv_analytic_expr_prepared_expanded_support_probe = struct

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_analytic_expr_corpus_support_scan;;

let candle_nl_prepared_expanded_formula target =
  let stripped = snd (strip_forall target) in
  let head,arguments = strip_comb stripped in
  if is_const head then
    match fst (dest_const head),arguments with
    | "ineqm",[_;_;formula] -> formula
    | "ineq",[_;formula] -> formula
    | _ -> stripped
  else stripped;;

let candle_nl_prepared_expanded_defs =
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

let candle_nl_prepared_expanded_scan_source source_id =
  let _,preparation,needs_delta = Break_case_exec.get_case source_id in
  let target =
    Break_case_exec.run_generic
      (fun selected -> preparation selected) needs_delta source_id in
  let formula = candle_nl_prepared_expanded_formula target in
  let expansion =
    (REWRITE_CONV
       [TAUT `(P ==> Q) <=> (~P \/ Q)`;
        REAL_ARITH `~(a > b:real) <=> a <= b`;
        REAL_ARITH `~(a < b:real) <=> b <= a`;
        REAL_ARITH `~(a >= b:real) <=> a < b`;
        REAL_ARITH `~(a <= b:real) <=> b < a`]
     THENC candle_direct_expand_ineq_case
     THENC REWRITE_CONV candle_nl_prepared_expanded_defs
     THENC DEPTH_CONV let_CONV)
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
    | [] -> failwith "empty expanded prepared expression list"
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

let candle_nl_prepared_expanded_probe_ids = Break_case_exec.all_idv;;

let candle_nl_prepared_expanded_probe_emit source_id =
  let started = Unix.gettimeofday () in
  try
    let dimension,disjuncts,unsupported =
      candle_nl_prepared_expanded_scan_source source_id in
    let elapsed = Unix.gettimeofday () -. started in
    print_endline
      ("CANDLE_NL_PREPARED_EXPANDED_SUPPORT_PROBE" ^
       " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
       " dimension=" ^ string_of_int dimension ^
       " disjuncts=" ^ string_of_int disjuncts ^
       " unsupported=" ^
         candle_nl_corpus_scan_join "," unsupported ^
       " elapsed_seconds=" ^ string_of_float elapsed)
  with Failure message ->
    print_endline
      ("CANDLE_NL_PREPARED_EXPANDED_SUPPORT_PROBE_ERROR" ^
       " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
       " message=" ^ message);;

let _ =
  do_list candle_nl_prepared_expanded_probe_emit
    candle_nl_prepared_expanded_probe_ids;;

end;;
