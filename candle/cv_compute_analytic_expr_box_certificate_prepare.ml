(* ========================================================================== *)
(* Untrusted whole-box square-root certificate preparation.                  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Exact rational interval arithmetic proposes  *)
(* one enclosure for every square-root argument over a source box.  Floating *)
(* point is used only to turn the exact argument endpoints into convenient   *)
(* square-root endpoints.  The reflected checker authenticates every proposal *)
(* before it can contribute to a theorem.                                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_analytic_expr_point_certificate_prepare.ml";;

module Candle_cv_analytic_expr_box_certificate_prepare = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_analytic_expr_reify;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_point_certificate_prepare;;

let candle_q_box_interval_neg (lower,upper) =
  Num.minus_num upper,Num.minus_num lower;;

let candle_q_box_interval_add (left_lower,left_upper)
    (right_lower,right_upper) =
  Num.add_num left_lower right_lower,
  Num.add_num left_upper right_upper;;

let candle_q_box_interval_mul (left_lower,left_upper)
    (right_lower,right_upper) =
  let products =
    [Num.mul_num left_lower right_lower;
     Num.mul_num left_lower right_upper;
     Num.mul_num left_upper right_lower;
     Num.mul_num left_upper right_upper] in
  itlist Num.min_num (tl products) (hd products),
  itlist Num.max_num (tl products) (hd products);;

(* Execute a source-only rational program over exact intervals.  The point  *)
(* certificate path already compiles every square-root argument once.  The  *)
(* same untrusted program can be reused for whole-box hint generation rather *)
(* than traversing and classifying the HOL source term for every box.  Keep  *)
(* the accepted fragment identical to [candle_q_box_interval_eval]: division *)
(* and inverse remain deliberately unsupported, and powers must be squares. *)

let candle_q_box_rational_program_interval bounds program =
  let rec lookup index = function
    | [] -> failwith "analytic box certificate: program bound shape"
    | bound :: remaining ->
        if index = 0 then bound else lookup (index - 1) remaining in
  let rec evaluate = function
    | Candle_q_point_rational_constant value -> value,value
    | Candle_q_point_rational_variable index -> lookup index bounds
    | Candle_q_point_rational_neg child ->
        candle_q_box_interval_neg (evaluate child)
    | Candle_q_point_rational_add (left,right) ->
        candle_q_box_interval_add (evaluate left) (evaluate right)
    | Candle_q_point_rational_sub (left,right) ->
        candle_q_box_interval_add
          (evaluate left) (candle_q_box_interval_neg (evaluate right))
    | Candle_q_point_rational_mul (left,right) ->
        candle_q_box_interval_mul (evaluate left) (evaluate right)
    | Candle_q_point_rational_div _ ->
        failwith "analytic box certificate: unsupported program division"
    | Candle_q_point_rational_inv _ ->
        failwith "analytic box certificate: unsupported program inverse"
    | Candle_q_point_rational_pow (base,exponent) ->
        if not (Num.eq_num exponent (Num.num_of_int 2)) then
          failwith "analytic box certificate: unsupported program power";
        let base_interval = evaluate base in
        candle_q_box_interval_mul base_interval base_interval in
  evaluate program;;

let rec candle_q_box_interval_eval variables bounds tm =
  try assoc tm (zip variables bounds) with Failure _ ->
  if is_ratconst tm then
    let value = rat_of_term tm in value,value
  else if candle_q_is_unary `(--):real->real` tm then
    candle_q_box_interval_neg
      (candle_q_box_interval_eval variables bounds
        (candle_q_dest_unary `(--):real->real` tm))
  else if candle_q_is_binary `(+):real->real->real` tm then
    let left,right = candle_q_dest_binary `(+):real->real->real` tm in
    candle_q_box_interval_add
      (candle_q_box_interval_eval variables bounds left)
      (candle_q_box_interval_eval variables bounds right)
  else if candle_q_is_binary `(-):real->real->real` tm then
    let left,right = candle_q_dest_binary `(-):real->real->real` tm in
    candle_q_box_interval_add
      (candle_q_box_interval_eval variables bounds left)
      (candle_q_box_interval_neg
        (candle_q_box_interval_eval variables bounds right))
  else if candle_q_is_binary `(*):real->real->real` tm then
    let left,right = candle_q_dest_binary `(*):real->real->real` tm in
    candle_q_box_interval_mul
      (candle_q_box_interval_eval variables bounds left)
      (candle_q_box_interval_eval variables bounds right)
  else if candle_q_is_binary `(pow):real->num->real` tm then
    let base,exponent = candle_q_dest_binary `(pow):real->num->real` tm in
    if dest_small_numeral exponent <> 2 then
      failwith "analytic box certificate: unsupported polynomial power";
    let base_interval =
      candle_q_box_interval_eval variables bounds base in
    candle_q_box_interval_mul base_interval base_interval
  else
    failwith "analytic box certificate: non-polynomial square-root argument";;

let candle_q_box_sqrt_scale = 1000000;;
let candle_q_box_sqrt_margin = 4;;

let candle_q_box_sqrt_interval (lower,upper) =
  if Num.le_num lower (Num.num_of_int 0) || Num.lt_num upper lower then
    failwith "analytic box certificate: nonpositive square-root range";
  let scale = candle_q_box_sqrt_scale in
  (* Flyspeck also defines a theorem module named [Float].  Keep this
     untrusted hint calculation on the OCaml runtime binding explicitly. *)
  let lower_approximate = Stdlib.sqrt (Num.float_of_num lower) and
      upper_approximate = Stdlib.sqrt (Num.float_of_num upper) in
  let lower_truncated =
    int_of_float (lower_approximate *. float_of_int scale) and
      upper_truncated =
        int_of_float (upper_approximate *. float_of_int scale) in
  let lower_candidate = lower_truncated - candle_q_box_sqrt_margin in
  let lower_integer = if lower_candidate < 0 then 0 else lower_candidate in
  let upper_integer =
    upper_truncated + candle_q_box_sqrt_margin + 1 in
  let denominator = Num.num_of_int scale in
  mk_pair
    (candle_q_term
      (Num.div_num (Num.num_of_int lower_integer) denominator),
     candle_q_term
      (Num.div_num (Num.num_of_int upper_integer) denominator));;

let candle_q_box_rational_program_intervals_six programs lower upper =
  if length lower <> 6 || length upper <> 6 then
    failwith "analytic box certificate: expected six box coordinates";
  let bounds =
    map2
      (fun lower_term upper_term ->
        rat_of_term lower_term,rat_of_term upper_term)
      lower upper in
  map
    (fun program ->
      candle_q_box_sqrt_interval
        (candle_q_box_rational_program_interval bounds program))
    programs;;

let candle_q_box_sqrt_callback variables bounds tm =
  let argument = candle_q_dest_unary `sqrt:real->real` tm in
  candle_q_box_sqrt_interval
    (candle_q_box_interval_eval variables bounds argument);;

let candle_q_dim_analytic_jet_prepare_box_six function_term lower upper =
  if length lower <> 6 || length upper <> 6 then
    failwith "analytic box certificate: expected six coordinates";
  let vector,_ = dest_abs function_term in
  let variables = candle_poly_vector_components vector 6 in
  let bounds =
    map2
      (fun lower_term upper_term ->
        rat_of_term lower_term,rat_of_term upper_term)
      lower upper in
  candle_q_dim_analytic_jet_prepare_six_with
    (candle_q_box_sqrt_callback variables bounds) function_term;;

end;;
