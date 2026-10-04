(* Reproduce and repair the mixed-function merge boundary on actual terms. *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch_forest_plan.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_term_order_compat.ml";;

module Test_cv_compute_flyspeck_nonlinear_term_order_compat = struct

open M_verifier;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch;;
open Candle_cv_flyspeck_nonlinear_term_order_compat;;

let candle_nonlinear_term_order_function0 =
  List.nth candle_disjunctive_case16582_functions 0;;
let candle_nonlinear_term_order_function1 =
  List.nth candle_disjunctive_case16582_functions 1;;
let candle_nonlinear_term_order_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_disjunctive_case16582_root_domain);;
let candle_nonlinear_term_order_function_type =
  type_of candle_nonlinear_term_order_function0;;
let candle_nonlinear_term_order_left =
  mk_list
    ([candle_nonlinear_term_order_function0],
     candle_nonlinear_term_order_function_type);;
let candle_nonlinear_term_order_right =
  mk_list
    ([candle_nonlinear_term_order_function1],
     candle_nonlinear_term_order_function_type);;
let candle_nonlinear_term_order_append =
  list_mk_comb
    (`APPEND:(real^6->real)list->(real^6->real)list->
             (real^6->real)list`,
     [candle_nonlinear_term_order_left;candle_nonlinear_term_order_right]);;
let candle_nonlinear_term_order_assumption_term =
  list_mk_comb
    (`m_cell_list_pass:(real^6->real)list->(real^6#real^6)->bool`,
     [candle_nonlinear_term_order_append;candle_nonlinear_term_order_domain]);;
let candle_nonlinear_term_order_assumption =
  ASSUME candle_nonlinear_term_order_assumption_term;;

let candle_nonlinear_term_order_legacy_rejected =
  try
    let _ =
      M_verifier.merge_m_cell_list_pass
        6 candle_nonlinear_term_order_assumption in
    false
  with Failure message ->
    message =
      "Stdlib.compare: polymorphic ordering is unavailable; use an explicit comparator";;
let candle_nonlinear_term_order_axioms_before = axioms ();;
let candle_nonlinear_term_order_result =
  candle_nonlinear_merge_m_cell_list_pass
    6 candle_nonlinear_term_order_assumption;;
let candle_nonlinear_term_order_functions,
    candle_nonlinear_term_order_result_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_nonlinear_term_order_result);;
let candle_nonlinear_term_order_axioms_after = axioms ();;

if not candle_nonlinear_term_order_legacy_rejected ||
   length candle_nonlinear_term_order_functions <> 2 ||
   not
     (List.exists
       (aconv candle_nonlinear_term_order_function0)
       candle_nonlinear_term_order_functions) ||
   not
     (List.exists
       (aconv candle_nonlinear_term_order_function1)
       candle_nonlinear_term_order_functions) ||
   not
     (aconv candle_nonlinear_term_order_result_domain
       candle_nonlinear_term_order_domain) ||
   hyp candle_nonlinear_term_order_result <>
     [candle_nonlinear_term_order_assumption_term] ||
   length candle_nonlinear_term_order_axioms_after <>
     length candle_nonlinear_term_order_axioms_before ||
   not
     (List.for_all
       (fun axiom -> List.mem axiom candle_nonlinear_term_order_axioms_before)
       candle_nonlinear_term_order_axioms_after) then
  failwith "nonlinear term-order compatibility: validation failed";;

print_endline
  ("CANDLE_CV_NONLINEAR_TERM_ORDER_COMPAT_TEST_OK DEVELOPMENT_NON_RELEASE" ^
   " legacy_compare_rejected=true explicit_term_compare_passed=true" ^
   " functions=2 axiom_growth=0");;

end;;
