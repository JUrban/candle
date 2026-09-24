(* ========================================================================== *)
(* Inventory the first authenticated action-296 source expression in Candle. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The external wrapper first revalidates the     *)
(* pinned target against the frozen Flyspeck closure.  This file reconstructs *)
(* and normalizes only its source formula.  It performs no certificate search,*)
(* leaf proof, action proof, S2/S3 claim, qualification, or release step.      *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

open Candle_cv_polynomial_expr_dim_jet_prove;;
open Candle_cv_exact_interval_reify;;

let candle_action296_inventory_axioms_before = axioms ();;

let candle_action296_inventory_target =
 `ineqm [x1; x2; x3; x4; x5; x6]
   (frac_right 0 #0.5000
   [#4.7524,#6.3504; #4.0,#4.7524; #4.0,#4.7524; #4.0,#2.25 * #2.25;
   #4.0,
   #2.25 * #2.25; #4.0,#2.25 * #2.25])
   (unit6 x1 x2 x3 x4 x5 x6 * #1.277 +
    sqrt_x1 x1 x2 x3 x4 x5 x6 * #0.273298 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.273298 * -- #2.18 +
    sqrt_x2 x1 x2 x3 x4 x5 x6 * -- #0.273853 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.273853 * #2.0 +
    sqrt_x3 x1 x2 x3 x4 x5 x6 * -- #0.273853 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.273853 * #2.0 +
    sqrt_x4 x1 x2 x3 x4 x5 x6 * #0.708818 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.708818 * -- #2.0 +
    sqrt_x5 x1 x2 x3 x4 x5 x6 * -- #0.313988 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.313988 * #2.0 +
    sqrt_x6 x1 x2 x3 x4 x5 x6 * -- #0.313988 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.313988 * #2.0 +
    dihatn_x x1 x2 x3 x4 x5 x6 * -- &1 <
    &0)`;;

let candle_action296_inventory_reconstruction =
  Break_case.ineqm_conv candle_action296_inventory_target;;
if lhand (concl candle_action296_inventory_reconstruction) <>
     candle_action296_inventory_target then
  failwith "action296 inventory: reconstruction source mismatch";;

let candle_action296_inventory_case =
  rand (concl candle_action296_inventory_reconstruction);;
let candle_action296_inventory_expansion =
  (REWRITE_CONV
     [TAUT `(P ==> Q) <=> (~P \/ Q)`;
      REAL_ARITH `~(a > b:real) <=> a <= b`;
      REAL_ARITH `~(a < b:real) <=> b <= a`;
      REAL_ARITH `~(a >= b:real) <=> a < b`;
      REAL_ARITH `~(a <= b:real) <=> b < a`]
   THENC
   REWRITE_CONV
     ([Definitions.ineq; IMP_IMP; REAL_MUL_LZERO; REAL_MUL_RZERO] @
      Definitions.flyspeck_defs)
   THENC DEPTH_CONV let_CONV)
    candle_action296_inventory_case;;
let candle_action296_inventory_converted =
  rand (concl candle_action296_inventory_expansion);;
let candle_action296_inventory_ineq,_,_ =
  M_verifier_main.dest_ineq candle_action296_inventory_converted;;
let candle_action296_inventory_standard =
  M_verifier_main.mk_standard_ineq
    [REAL_POW_1; real_pow] candle_action296_inventory_ineq;;
let candle_action296_inventory_terms =
  striplist dest_disj
    ((lhand o concl) candle_action296_inventory_standard);;
if length candle_action296_inventory_terms <> 1 then
  failwith "action296 inventory: source disjunction cardinality drift";;
let candle_action296_inventory_lhs =
  lhand (hd candle_action296_inventory_terms);;
let candle_action296_inventory_functions,
    candle_action296_inventory_variable_vector =
  M_verifier_main.exprs_to_vector_fun [candle_action296_inventory_lhs];;
if length candle_action296_inventory_functions <> 1 then
  failwith "action296 inventory: vector-function cardinality drift";;
let candle_action296_inventory_function =
  hd candle_action296_inventory_functions;;
let candle_action296_inventory_vector,
    candle_action296_inventory_body =
  dest_abs candle_action296_inventory_function;;
let candle_action296_inventory_variables =
  Candle_cv_polynomial_expr_flyspeck_reify.candle_poly_vector_components
    candle_action296_inventory_vector 6;;

let rec candle_action296_inventory_unsupported variables tm =
  match candle_q_variable_index variables tm with
  | Some _ -> []
  | None ->
      if is_ratconst tm || candle_q_is_binary `DECIMAL` tm then []
      else if candle_q_is_unary `(--):real->real` tm then
        candle_action296_inventory_unsupported variables
          (candle_q_dest_unary `(--):real->real` tm)
      else if candle_q_is_binary `(+):real->real->real` tm ||
              candle_q_is_binary `(-):real->real->real` tm ||
              candle_q_is_binary `(*):real->real->real` tm then
        let left,right =
          if candle_q_is_binary `(+):real->real->real` tm then
            candle_q_dest_binary `(+):real->real->real` tm
          else if candle_q_is_binary `(-):real->real->real` tm then
            candle_q_dest_binary `(-):real->real->real` tm
          else candle_q_dest_binary `(*):real->real->real` tm in
        candle_action296_inventory_unsupported variables left @
        candle_action296_inventory_unsupported variables right
      else if candle_q_is_binary `(pow):real->num->real` tm then
        let base,_ = candle_q_dest_binary `(pow):real->num->real` tm in
        candle_action296_inventory_unsupported variables base
      else [tm];;

let candle_action296_inventory_unsupported_terms =
  candle_action296_inventory_unsupported
    candle_action296_inventory_variables candle_action296_inventory_body;;

let candle_action296_inventory_head_name tm =
  let head,_ = strip_comb tm in
  if is_const head then fst (dest_const head)
  else if is_var head then fst (dest_var head)
  else "<non-atomic-head>";;

let candle_action296_inventory_unsupported_names =
  setify (fun left right -> String.compare left right <= 0)
    (map candle_action296_inventory_head_name
      candle_action296_inventory_unsupported_terms);;

let rec candle_action296_inventory_print index terms =
  match terms with
  | [] -> ()
  | tm :: rest ->
      print_endline
        ("CANDLE_CV_ACTION296_UNSUPPORTED index=" ^ string_of_int index ^
         " head=" ^ candle_action296_inventory_head_name tm ^
         " term_md5=" ^
         Digest.to_hex (Digest.string (string_of_term tm)) ^
         " term=" ^ string_of_term tm);
      candle_action296_inventory_print (index + 1) rest;;

let candle_action296_inventory_reifier_status =
  try
    let _ =
      candle_q_dim_poly_jet_prepare_six
        candle_action296_inventory_function in
    "unexpectedly-supported"
  with Failure message -> message;;

if candle_action296_inventory_unsupported_terms = [] ||
   candle_action296_inventory_reifier_status <>
     "candle polynomial reifier: unsupported real expression" then
  failwith "action296 inventory: expected support boundary not observed";;

let candle_action296_inventory_axioms_after = axioms ();;
if length candle_action296_inventory_axioms_after <>
     length candle_action296_inventory_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_action296_inventory_axioms_before)
       candle_action296_inventory_axioms_after) then
  failwith "action296 inventory: changed the global axiom set";;

let _ = candle_action296_inventory_print
  0 candle_action296_inventory_unsupported_terms;;
let _ =
  print_endline
    ("CANDLE_CV_ACTION296_SOURCE_INVENTORY_RESULT functions=1 " ^
     "unsupported_terms=" ^
     string_of_int (length candle_action296_inventory_unsupported_terms) ^
     " unsupported_heads=" ^
     String.concat "," candle_action296_inventory_unsupported_names ^
     " function_md5=" ^
     Digest.to_hex
       (Digest.string
         (string_of_term candle_action296_inventory_function)));;
let _ = print_endline "CANDLE_CV_ACTION296_SOURCE_INVENTORY_OK";;
