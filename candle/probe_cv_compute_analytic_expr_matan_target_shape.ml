(* ========================================================================== *)
(* Exact source-shape inventory for the first reflected [matan] target.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This probe selects no proof result.  It emits *)
(* the authenticated target and its definitionally expanded Boolean formula  *)
(* so that the next certificate adapter can be chosen from evidence.          *)
(* ========================================================================== *)

needs "candle/cv_compute_flyspeck_direct_source_compat.ml";;
needs "candle/cv_compute_analytic_expr_matan_domain_probe.ml";;

open Candle_cv_analytic_expr_matan_domain_probe;;

module Candle_cv_analytic_expr_matan_target_shape_probe = struct

let candle_matan_shape_source_id = "prep-TSKAJXY-GXSABWC DIV";;
let candle_matan_shape_target =
  candle_nl_matan_target candle_matan_shape_source_id;;
let candle_matan_shape_variables,
    candle_matan_shape_bounds,
    candle_matan_shape_formula =
  candle_nl_matan_target_parts candle_matan_shape_target;;
let candle_matan_shape_expanded =
  candle_nl_matan_expand candle_matan_shape_formula;;

let candle_matan_shape_head tm =
  let head,arguments = strip_comb tm in
  let name =
    if is_const head then fst (dest_const head)
    else if is_var head then fst (dest_var head)
    else if is_abs head then "<lambda>"
    else "<compound>" in
  name,length arguments;;

let rec candle_matan_shape_relations tm =
  let head,arguments = strip_comb tm in
  let here =
    if is_const head && length arguments = 2 then
      let name = fst (dest_const head) in
      if List.mem name ["real_lt";"real_le";"real_gt";"real_ge";"="] &&
         type_of (hd arguments) = `:real` then
        [tm]
      else []
    else [] in
  if not (here = []) then here
  else if is_comb tm then
    candle_matan_shape_relations (rator tm) @
    candle_matan_shape_relations (rand tm)
  else if is_abs tm then candle_matan_shape_relations (body tm)
  else [];;

let rec candle_matan_shape_sqrts tm =
  let here =
    if is_comb tm &&
       candle_nl_matan_is_unary `sqrt:real->real` tm then [tm]
    else [] in
  let below =
    if is_comb tm then
      candle_matan_shape_sqrts (rator tm) @
      candle_matan_shape_sqrts (rand tm)
    else if is_abs tm then candle_matan_shape_sqrts (body tm)
    else [] in
  here @ below;;

let candle_matan_shape_exact_bound tm =
  let expanded = rand (concl (REWRITE_CONV candle_nl_matan_defs tm)) in
  let lower,upper = candle_nl_matan_interval_eval [] expanded in
  if not (Num.eq_num lower upper) then
    failwith "matan target shape: source bound is not exact";
  lower;;

let candle_matan_shape_environment =
  zip candle_matan_shape_variables
    (map
      (fun (lower,upper) ->
        candle_matan_shape_exact_bound lower,
        candle_matan_shape_exact_bound upper)
      candle_matan_shape_bounds);;

let candle_matan_shape_formula_head,
    candle_matan_shape_formula_arity =
  candle_matan_shape_head candle_matan_shape_formula;;
let candle_matan_shape_expanded_head,
    candle_matan_shape_expanded_arity =
  candle_matan_shape_head candle_matan_shape_expanded;;
let candle_matan_shape_relations_found =
  candle_matan_shape_relations candle_matan_shape_expanded;;
let candle_matan_shape_sqrts_found =
  setify aconv (candle_matan_shape_sqrts candle_matan_shape_expanded);;

let _ = print_endline
  ("CANDLE_CV_MATAN_TARGET_SHAPE_RESULT source_id=" ^
   candle_matan_shape_source_id ^
   " variables=" ^ string_of_int (length candle_matan_shape_variables) ^
   " bounds=" ^ string_of_int (length candle_matan_shape_bounds) ^
   " formula_head=" ^ candle_matan_shape_formula_head ^
   " formula_arity=" ^ string_of_int candle_matan_shape_formula_arity ^
   " expanded_head=" ^ candle_matan_shape_expanded_head ^
   " expanded_arity=" ^ string_of_int candle_matan_shape_expanded_arity ^
   " relations=" ^
   string_of_int (length candle_matan_shape_relations_found) ^
   " sqrts=" ^ string_of_int (length candle_matan_shape_sqrts_found) ^
   " formula_chars=" ^
   string_of_int (String.length (string_of_term candle_matan_shape_formula)) ^
   " expanded_chars=" ^
   string_of_int (String.length (string_of_term candle_matan_shape_expanded)));

let _ = print_endline
  ("CANDLE_CV_MATAN_TARGET_SHAPE_FORMULA " ^
   string_of_term candle_matan_shape_formula);;
let _ = print_endline
  ("CANDLE_CV_MATAN_TARGET_SHAPE_EXPANDED " ^
   string_of_term candle_matan_shape_expanded);;
let _ = do_list
  (fun (index,relation) ->
    print_endline
      ("CANDLE_CV_MATAN_TARGET_SHAPE_RELATION index=" ^
       string_of_int index ^ " term=" ^ string_of_term relation))
  (zip (0--(length candle_matan_shape_relations_found - 1))
       candle_matan_shape_relations_found);;
let _ = do_list
  (fun (index,sqrt_term) ->
    let child = rand sqrt_term in
    try
      let lower,upper =
        candle_nl_matan_interval_eval candle_matan_shape_environment child in
      print_endline
        ("CANDLE_CV_MATAN_TARGET_SHAPE_SQRT index=" ^
         string_of_int index ^
         " lower=" ^ Num.string_of_num lower ^
         " upper=" ^ Num.string_of_num upper ^
         " term=" ^ string_of_term sqrt_term)
    with Failure message ->
      print_endline
        ("CANDLE_CV_MATAN_TARGET_SHAPE_SQRT_ERROR index=" ^
         string_of_int index ^ " message=" ^ message ^
         " term=" ^ string_of_term sqrt_term))
  (zip (0--(length candle_matan_shape_sqrts_found - 1))
       candle_matan_shape_sqrts_found);;
let _ = print_endline "CANDLE_CV_MATAN_TARGET_SHAPE_OK";;

end;;
