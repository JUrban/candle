(* ========================================================================== *)
(* Untrusted preparation of tight square-root certificates at exact points.  *)
(*                                                                            *)
(* Floating point is used only to propose rational endpoints.  The reflected *)
(* analytic checker verifies every proposed endpoint against the exact source *)
(* argument before any theorem is produced.                                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;

module Candle_cv_analytic_expr_point_certificate_prepare = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_analytic_expr_jet_prove;;

let candle_q_point_sqrt_scale = 100000;;
let candle_q_point_sqrt_margin = 2;;

let candle_q_point_sqrt_interval rational =
  if rational <=/ Num.num_of_int 0 then
    failwith "analytic point certificate: nonpositive square-root argument";
  let scale = candle_q_point_sqrt_scale in
  let approximate = Float.sqrt (Num.float_of_num rational) in
  let truncated = int_of_float (approximate *. float_of_int scale) in
  let lower_candidate = truncated - candle_q_point_sqrt_margin in
  let lower_integer = if lower_candidate < 0 then 0 else lower_candidate in
  let upper_integer = truncated + candle_q_point_sqrt_margin + 1 in
  let denominator = Num.num_of_int scale in
  mk_pair
    (candle_q_term
      (Num.div_num (Num.num_of_int lower_integer) denominator),
     candle_q_term
      (Num.div_num (Num.num_of_int upper_integer) denominator));;

let candle_q_point_sqrt_callback variables values tm =
  if length variables <> length values then
    failwith "analytic point certificate: substitution shape";
  let operator,argument = dest_comb tm in
  if not (aconv operator `sqrt:real->real`) then
    failwith "analytic point certificate: expected square root";
  let instantiated =
    subst (map2 (fun variable value -> value,variable) variables values)
      argument in
  let reduced = rand (concl (REAL_RAT_REDUCE_CONV instantiated)) in
  candle_q_point_sqrt_interval (rat_of_term reduced);;

let candle_q_point_centers lower upper =
  if length lower <> length upper then
    failwith "analytic point certificate: box shape";
  map2
    (fun lower_term upper_term ->
      term_of_rat
        (Num.div_num
          (Num.add_num (rat_of_term lower_term) (rat_of_term upper_term))
          (Num.num_of_int 2)))
    lower upper;;

let candle_q_dim_analytic_jet_prepare_point_six function_term lower upper =
  let vector,_ = dest_abs function_term in
  let variables = candle_poly_vector_components vector 6 in
  let values = candle_q_point_centers lower upper in
  candle_q_dim_analytic_jet_prepare_six_with
    (candle_q_point_sqrt_callback variables values) function_term;;

end;;
