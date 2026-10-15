(* ========================================================================== *)
(* Bind the lightweight selected-leaf fixture to the reconstructed real plan. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hminus_iarg0_plan_probe.ml";;
needs "candle/cv_compute_analytic_expr_hminus_iarg0_selected_leaf_fixture.ml";;

module Test_cv_compute_analytic_expr_hminus_iarg0_selected_leaf_fixture = struct

open Certificate;;
open M_verifier_build;;
open Candle_cv_analytic_expr_hminus_iarg0_plan_probe;;

let rec first_leaf path domain tree =
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      if raw_flag then
        failwith "hminus selected fixture: unexpected raw leaf";
      rev path,status,function_index,domain
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "hminus selected fixture: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain 6 6 (split_index + 1) domain in
      first_leaf ((split_index + 1) :: path) left_domain left
  | P_result_mono _ ->
      failwith "hminus selected fixture: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "hminus selected fixture: unexpected reference node";;

let planned_path,planned_status,planned_function,planned_domain =
  first_leaf [] root_domain precision_tree;;

let fixture =
  Candle_cv_analytic_expr_hminus_iarg0_selected_leaf_fixture.selected_path,
  Candle_cv_analytic_expr_hminus_iarg0_selected_leaf_fixture.function0,
  Candle_cv_analytic_expr_hminus_iarg0_selected_leaf_fixture.leaf_domain;;
let fixture_path,fixture_function,fixture_domain = fixture;;

if planned_path <> fixture_path ||
   planned_status.pp <> 3 ||
   planned_function <> 0 ||
   not (aconv function0 fixture_function) ||
   not (aconv (concl planned_domain) (concl fixture_domain)) then
  failwith "hminus selected fixture: reconstructed plan drift";;

(* [mk_verification_functions] prepares constants at the verifier's global
   precision, while the adaptive certificate selects [planned_status.pp] for
   the two recurring Taylor precisions.  Preserve that distinction here: in
   particular, rebuilding constants at the leaf precision changes this real
   leaf's bound. *)
let legacy_taylor_function,_ =
  M_verifier_main.mk_funs 6 6 function0;;
let _ =
  print_endline
    "CANDLE_NL_HMINUS_IARG0_SELECTED_LEAF_LEGACY phase=begin";;
let legacy_taylor =
  legacy_taylor_function
    planned_status.pp planned_status.pp planned_domain;;
let legacy_upper_theorem =
  M_taylor.eval_m_taylor_upper_bound
    6 planned_status.pp legacy_taylor;;
let _ =
  print_endline
    "CANDLE_NL_HMINUS_IARG0_SELECTED_LEAF_LEGACY phase=end";;
let legacy_upper_term =
  let body = snd (dest_forall (concl legacy_upper_theorem)) in
  let _,consequent = dest_comb body in
  let _,upper = dest_comb consequent in
  upper;;
let legacy_upper =
  More_float.float_of_float_tm legacy_upper_term;;
let legacy_upper_sign =
  Arith_float.float_lt0 legacy_upper_term;;
let legacy_pass =
  M_verifier.m_taylor_cell_pass
    6 planned_status.pp legacy_taylor;;

if hyp legacy_taylor <> [] ||
   hyp legacy_upper_theorem <> [] ||
   hyp legacy_upper_sign <> [] ||
   hyp legacy_pass <> [] then
  failwith "hminus selected fixture: legacy theorem has assumptions";;

if (fst o dest_const o rand o concl) legacy_upper_sign <> "T" then
  failwith "hminus selected fixture: legacy upper is not negative";;

print_endline
  ("CANDLE_NL_HMINUS_IARG0_SELECTED_LEAF_FIXTURE_PLAN_OK" ^
   " DEVELOPMENT_NON_RELEASE path_length=" ^
   string_of_int (length planned_path) ^
   " precision=" ^ string_of_int planned_status.pp ^
   " function=" ^ string_of_int planned_function ^
   " legacy_upper_term=" ^ string_of_term legacy_upper_term ^
   " legacy_upper=" ^ string_of_float legacy_upper ^
   " domain_digest=" ^
   Digest.to_hex (Digest.string (string_of_term (concl planned_domain))));;

end;;
