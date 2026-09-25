(* ========================================================================== *)
(* Untrusted fixed-scale diagnostic for centered polynomial Taylor models.   *)
(*                                                                            *)
(* DEVELOPMENT / DIAGNOSTIC ONLY.  This ordinary-ML evaluator mirrors the    *)
(* polynomial fragment of                                                    *)
(* [cv_compute_analytic_expr_taylor_model_program_compute.ml] after every    *)
(* completed stack node has been rounded to denominator 10^12.  It constructs *)
(* no theorem and must never authorize a proof result.  Its purpose is to    *)
(* measure whether a signed-scaled-integer backend is worth proving.          *)
(*                                                                            *)
(* Every benchmark using this module must compare the complete concrete      *)
(* result with Kernel.compute.                                                *)
(* ========================================================================== *)

module Candle_cv_analytic_expr_fixed_scale_diagnostic = struct

let candle_cv_fixed_scale = Num.num_of_string "1000000000000";;
let candle_cv_fixed_zero = Num.num_of_int 0;;
let candle_cv_fixed_one = Num.num_of_int 1;;
let candle_cv_fixed_two = Num.num_of_int 2;;

let candle_cv_fixed_num_min x y = if Num.le_num x y then x else y;;
let candle_cv_fixed_num_max x y = if Num.le_num x y then y else x;;
let candle_cv_fixed_num_abs x =
  if Num.lt_num x candle_cv_fixed_zero then Num.minus_num x else x;;

let candle_cv_fixed_floor_div numerator denominator =
  if Num.lt_num numerator candle_cv_fixed_zero then
    Num.minus_num
      (Num.quo_num
        (Num.add_num (Num.minus_num numerator)
          (Num.sub_num denominator candle_cv_fixed_one))
        denominator)
  else Num.quo_num numerator denominator;;

let candle_cv_fixed_ceil_div numerator denominator =
  if Num.lt_num numerator candle_cv_fixed_zero then
    Num.minus_num (Num.quo_num (Num.minus_num numerator) denominator)
  else
    Num.quo_num
      (Num.add_num numerator (Num.sub_num denominator candle_cv_fixed_one))
      denominator;;

let rec candle_cv_fixed_num_power base exponent =
  if exponent <= 0 then candle_cv_fixed_one
  else if exponent mod 2 = 0 then
    let half = candle_cv_fixed_num_power base (exponent / 2) in
    Num.mul_num half half
  else Num.mul_num base (candle_cv_fixed_num_power base (exponent - 1));;

(* A raw exact value is numerator / (scale^scale_power * 2^half_power).       *)
(* Polynomial composition only introduces products, sums, and the Taylor     *)
(* factor 1/2, so these denominators form a divisibility lattice.             *)

type candle_cv_fixed_raw = {
  candle_cv_fixed_raw_numerator: Num.num;
  candle_cv_fixed_raw_scale_power: int;
  candle_cv_fixed_raw_half_power: int
};;

let candle_cv_fixed_raw_make numerator scale_power half_power =
  {candle_cv_fixed_raw_numerator = numerator;
   candle_cv_fixed_raw_scale_power = scale_power;
   candle_cv_fixed_raw_half_power = half_power};;

let candle_cv_fixed_raw_of_scaled numerator =
  candle_cv_fixed_raw_make numerator 1 0;;

let candle_cv_fixed_raw_zero =
  candle_cv_fixed_raw_make candle_cv_fixed_zero 0 0;;

let candle_cv_fixed_raw_scale_to value scale_power half_power =
  let scale_delta = scale_power - value.candle_cv_fixed_raw_scale_power and
      half_delta = half_power - value.candle_cv_fixed_raw_half_power in
  if scale_delta < 0 || half_delta < 0 then
    failwith "fixed-scale diagnostic: invalid denominator alignment";
  let scale_factor =
    candle_cv_fixed_num_power candle_cv_fixed_scale scale_delta and
      half_factor =
        candle_cv_fixed_num_power candle_cv_fixed_two half_delta in
  Num.mul_num value.candle_cv_fixed_raw_numerator
    (Num.mul_num scale_factor half_factor);;

let candle_cv_fixed_raw_add left right =
  let scale_power =
    max left.candle_cv_fixed_raw_scale_power
      right.candle_cv_fixed_raw_scale_power and
      half_power =
        max left.candle_cv_fixed_raw_half_power
          right.candle_cv_fixed_raw_half_power in
  candle_cv_fixed_raw_make
    (Num.add_num
      (candle_cv_fixed_raw_scale_to left scale_power half_power)
      (candle_cv_fixed_raw_scale_to right scale_power half_power))
    scale_power half_power;;

let candle_cv_fixed_raw_neg value =
  {value with candle_cv_fixed_raw_numerator =
    Num.minus_num value.candle_cv_fixed_raw_numerator};;

let candle_cv_fixed_raw_sub left right =
  candle_cv_fixed_raw_add left (candle_cv_fixed_raw_neg right);;

let candle_cv_fixed_raw_mul left right =
  candle_cv_fixed_raw_make
    (Num.mul_num left.candle_cv_fixed_raw_numerator
      right.candle_cv_fixed_raw_numerator)
    (left.candle_cv_fixed_raw_scale_power +
      right.candle_cv_fixed_raw_scale_power)
    (left.candle_cv_fixed_raw_half_power +
      right.candle_cv_fixed_raw_half_power);;

let candle_cv_fixed_raw_half value =
  {value with candle_cv_fixed_raw_half_power =
    value.candle_cv_fixed_raw_half_power + 1};;

let candle_cv_fixed_raw_compare left right =
  let scale_power =
    max left.candle_cv_fixed_raw_scale_power
      right.candle_cv_fixed_raw_scale_power and
      half_power =
        max left.candle_cv_fixed_raw_half_power
          right.candle_cv_fixed_raw_half_power in
  let left_value =
    candle_cv_fixed_raw_scale_to left scale_power half_power and
      right_value =
        candle_cv_fixed_raw_scale_to right scale_power half_power in
  if Num.lt_num left_value right_value then -1
  else if Num.eq_num left_value right_value then 0
  else 1;;

let candle_cv_fixed_raw_min left right =
  if candle_cv_fixed_raw_compare left right <= 0 then left else right;;

let candle_cv_fixed_raw_max left right =
  if candle_cv_fixed_raw_compare left right <= 0 then right else left;;

let candle_cv_fixed_raw_round_lower value =
  let denominator =
    Num.mul_num
      (candle_cv_fixed_num_power candle_cv_fixed_scale
        value.candle_cv_fixed_raw_scale_power)
      (candle_cv_fixed_num_power candle_cv_fixed_two
        value.candle_cv_fixed_raw_half_power) in
  candle_cv_fixed_floor_div
    (Num.mul_num value.candle_cv_fixed_raw_numerator candle_cv_fixed_scale)
    denominator;;

let candle_cv_fixed_raw_round_upper value =
  let denominator =
    Num.mul_num
      (candle_cv_fixed_num_power candle_cv_fixed_scale
        value.candle_cv_fixed_raw_scale_power)
      (candle_cv_fixed_num_power candle_cv_fixed_two
        value.candle_cv_fixed_raw_half_power) in
  candle_cv_fixed_ceil_div
    (Num.mul_num value.candle_cv_fixed_raw_numerator candle_cv_fixed_scale)
    denominator;;

type candle_cv_fixed_interval = Num.num * Num.num;;
type candle_cv_fixed_raw_interval =
  candle_cv_fixed_raw * candle_cv_fixed_raw;;

let candle_cv_fixed_interval_zero =
  candle_cv_fixed_zero,candle_cv_fixed_zero;;

let candle_cv_fixed_interval_one =
  candle_cv_fixed_scale,candle_cv_fixed_scale;;

let candle_cv_fixed_interval_raw (lower,upper) =
  candle_cv_fixed_raw_of_scaled lower,candle_cv_fixed_raw_of_scaled upper;;

let candle_cv_fixed_raw_interval_round (lower,upper) =
  candle_cv_fixed_raw_round_lower lower,
  candle_cv_fixed_raw_round_upper upper;;

let candle_cv_fixed_raw_interval_neg (lower,upper) =
  candle_cv_fixed_raw_neg upper,candle_cv_fixed_raw_neg lower;;

let candle_cv_fixed_raw_interval_add (ll,lu) (rl,ru) =
  candle_cv_fixed_raw_add ll rl,candle_cv_fixed_raw_add lu ru;;

let candle_cv_fixed_raw_interval_mul (ll,lu) (rl,ru) =
  let llrl = candle_cv_fixed_raw_mul ll rl and
      llru = candle_cv_fixed_raw_mul ll ru and
      lurl = candle_cv_fixed_raw_mul lu rl and
      luru = candle_cv_fixed_raw_mul lu ru in
  candle_cv_fixed_raw_min
    (candle_cv_fixed_raw_min llrl llru)
    (candle_cv_fixed_raw_min lurl luru),
  candle_cv_fixed_raw_max
    (candle_cv_fixed_raw_max llrl llru)
    (candle_cv_fixed_raw_max lurl luru);;

let candle_cv_fixed_raw_interval_symmetric radius =
  candle_cv_fixed_raw_neg radius,radius;;

let candle_cv_fixed_interval_neg (lower,upper) =
  Num.minus_num upper,Num.minus_num lower;;

let candle_cv_fixed_interval_abs_upper (lower,upper) =
  candle_cv_fixed_num_max
    (candle_cv_fixed_num_abs lower) (candle_cv_fixed_num_abs upper);;

type candle_cv_fixed_first_jet = {
  candle_cv_fixed_first_value: candle_cv_fixed_interval;
  candle_cv_fixed_first_gradient: candle_cv_fixed_interval array
};;

type candle_cv_fixed_raw_first_jet = {
  candle_cv_fixed_raw_first_value: candle_cv_fixed_raw_interval;
  candle_cv_fixed_raw_first_gradient: candle_cv_fixed_raw_interval array
};;

type candle_cv_fixed_result = {
  candle_cv_fixed_result_center: candle_cv_fixed_first_jet;
  candle_cv_fixed_result_value_bound: candle_cv_fixed_interval;
  candle_cv_fixed_result_gradient_bounds: candle_cv_fixed_interval array;
  candle_cv_fixed_result_hessian: candle_cv_fixed_interval array array
};;

let candle_cv_fixed_array_map2 operation left right =
  let count = Array.length left in
  if Array.length right <> count then
    failwith "fixed-scale diagnostic: vector cardinality mismatch";
  Array.init count (fun index -> operation left.(index) right.(index));;

let candle_cv_fixed_array_mapi operation items =
  let rec build index =
    if index >= Array.length items then []
    else operation index items.(index) :: build (index + 1) in
  Array.of_list (build 0);;

let candle_cv_fixed_array_fold_right operation items initial =
  let rec fold index result =
    if index < 0 then result
    else fold (index - 1) (operation items.(index) result) in
  fold (Array.length items - 1) initial;;

let candle_cv_fixed_matrix_map2 operation left right =
  candle_cv_fixed_array_map2
    (fun left_row right_row ->
      candle_cv_fixed_array_map2 operation left_row right_row)
    left right;;

let candle_cv_fixed_dot_abs_upper radii intervals =
  let count = Array.length radii in
  if Array.length intervals <> count then
    failwith "fixed-scale diagnostic: dot cardinality mismatch";
  let total = ref candle_cv_fixed_raw_zero in
  for index = 0 to count - 1 do
    total := candle_cv_fixed_raw_add
      (candle_cv_fixed_raw_mul
        (candle_cv_fixed_raw_of_scaled radii.(index))
        (candle_cv_fixed_raw_of_scaled
          (candle_cv_fixed_interval_abs_upper intervals.(index))))
      !total
  done;
  !total;;

let candle_cv_fixed_weighted_rows_abs_upper radii hessian =
  let count = Array.length radii in
  if Array.length hessian <> count then
    failwith "fixed-scale diagnostic: matrix cardinality mismatch";
  let total = ref candle_cv_fixed_raw_zero in
  for index = 0 to count - 1 do
    total := candle_cv_fixed_raw_add
      (candle_cv_fixed_raw_mul
        (candle_cv_fixed_raw_of_scaled radii.(index))
        (candle_cv_fixed_dot_abs_upper radii hessian.(index)))
      !total
  done;
  !total;;

let candle_cv_fixed_complete_rounded radii center hessian =
  let error =
    candle_cv_fixed_raw_add
      (candle_cv_fixed_dot_abs_upper radii
        center.candle_cv_fixed_first_gradient)
      (candle_cv_fixed_raw_half
        (candle_cv_fixed_weighted_rows_abs_upper radii hessian)) in
  let value_bound =
    candle_cv_fixed_raw_interval_round
      (candle_cv_fixed_raw_interval_add
        (candle_cv_fixed_interval_raw center.candle_cv_fixed_first_value)
        (candle_cv_fixed_raw_interval_symmetric error)) in
  let gradient_bounds =
    candle_cv_fixed_array_mapi
      (fun index gradient_interval ->
        candle_cv_fixed_raw_interval_round
          (candle_cv_fixed_raw_interval_add
            (candle_cv_fixed_interval_raw gradient_interval)
            (candle_cv_fixed_raw_interval_symmetric
              (candle_cv_fixed_dot_abs_upper radii hessian.(index)))))
      center.candle_cv_fixed_first_gradient in
  {candle_cv_fixed_result_center = center;
   candle_cv_fixed_result_value_bound = value_bound;
   candle_cv_fixed_result_gradient_bounds = gradient_bounds;
   candle_cv_fixed_result_hessian = hessian};;

let candle_cv_fixed_complete radii raw_center raw_hessian =
  let center =
    {candle_cv_fixed_first_value =
       candle_cv_fixed_raw_interval_round
         raw_center.candle_cv_fixed_raw_first_value;
     candle_cv_fixed_first_gradient =
       Array.map candle_cv_fixed_raw_interval_round
         raw_center.candle_cv_fixed_raw_first_gradient} and
      hessian =
        Array.map (Array.map candle_cv_fixed_raw_interval_round) raw_hessian in
  candle_cv_fixed_complete_rounded radii center hessian;;

let candle_cv_fixed_result_neg radii value =
  candle_cv_fixed_complete radii
    {candle_cv_fixed_raw_first_value =
       candle_cv_fixed_raw_interval_neg
         (candle_cv_fixed_interval_raw
           value.candle_cv_fixed_result_center.candle_cv_fixed_first_value);
     candle_cv_fixed_raw_first_gradient =
       Array.map
         (fun interval ->
           candle_cv_fixed_raw_interval_neg
             (candle_cv_fixed_interval_raw interval))
         value.candle_cv_fixed_result_center.candle_cv_fixed_first_gradient}
    (Array.map
      (Array.map
        (fun interval ->
          candle_cv_fixed_raw_interval_neg
            (candle_cv_fixed_interval_raw interval)))
      value.candle_cv_fixed_result_hessian);;

let candle_cv_fixed_result_add radii left right =
  candle_cv_fixed_complete radii
    {candle_cv_fixed_raw_first_value =
       candle_cv_fixed_raw_interval_add
         (candle_cv_fixed_interval_raw
           left.candle_cv_fixed_result_center.candle_cv_fixed_first_value)
         (candle_cv_fixed_interval_raw
           right.candle_cv_fixed_result_center.candle_cv_fixed_first_value);
     candle_cv_fixed_raw_first_gradient =
       candle_cv_fixed_array_map2
         (fun left_interval right_interval ->
           candle_cv_fixed_raw_interval_add
             (candle_cv_fixed_interval_raw left_interval)
             (candle_cv_fixed_interval_raw right_interval))
         left.candle_cv_fixed_result_center.candle_cv_fixed_first_gradient
         right.candle_cv_fixed_result_center.candle_cv_fixed_first_gradient}
    (candle_cv_fixed_matrix_map2
      (fun left_interval right_interval ->
        candle_cv_fixed_raw_interval_add
          (candle_cv_fixed_interval_raw left_interval)
          (candle_cv_fixed_interval_raw right_interval))
      left.candle_cv_fixed_result_hessian
      right.candle_cv_fixed_result_hessian);;

let candle_cv_fixed_interval_matrix_scale scalar matrix =
  Array.map
    (Array.map
      (fun interval ->
        candle_cv_fixed_raw_interval_mul
          (candle_cv_fixed_interval_raw scalar)
          (candle_cv_fixed_interval_raw interval)))
    matrix;;

let candle_cv_fixed_interval_outer left right =
  Array.map
    (fun left_interval ->
      Array.map
        (fun right_interval ->
          candle_cv_fixed_raw_interval_mul
            (candle_cv_fixed_interval_raw left_interval)
            (candle_cv_fixed_interval_raw right_interval))
        right)
    left;;

let candle_cv_fixed_raw_matrix_add left right =
  candle_cv_fixed_matrix_map2 candle_cv_fixed_raw_interval_add left right;;

let candle_cv_fixed_result_mul radii left right =
  let left_center = left.candle_cv_fixed_result_center and
      right_center = right.candle_cv_fixed_result_center in
  let raw_center =
    {candle_cv_fixed_raw_first_value =
       candle_cv_fixed_raw_interval_mul
         (candle_cv_fixed_interval_raw left_center.candle_cv_fixed_first_value)
         (candle_cv_fixed_interval_raw right_center.candle_cv_fixed_first_value);
     candle_cv_fixed_raw_first_gradient =
       candle_cv_fixed_array_map2
         (fun left_gradient right_gradient ->
           candle_cv_fixed_raw_interval_add
             (candle_cv_fixed_raw_interval_mul
               (candle_cv_fixed_interval_raw
                 right_center.candle_cv_fixed_first_value)
               (candle_cv_fixed_interval_raw left_gradient))
             (candle_cv_fixed_raw_interval_mul
               (candle_cv_fixed_interval_raw
                 left_center.candle_cv_fixed_first_value)
               (candle_cv_fixed_interval_raw right_gradient)))
         left_center.candle_cv_fixed_first_gradient
         right_center.candle_cv_fixed_first_gradient} in
  let raw_hessian =
    candle_cv_fixed_raw_matrix_add
      (candle_cv_fixed_raw_matrix_add
        (candle_cv_fixed_interval_matrix_scale
          right.candle_cv_fixed_result_value_bound
          left.candle_cv_fixed_result_hessian)
        (candle_cv_fixed_interval_outer
          left.candle_cv_fixed_result_gradient_bounds
          right.candle_cv_fixed_result_gradient_bounds))
      (candle_cv_fixed_raw_matrix_add
        (candle_cv_fixed_interval_outer
          right.candle_cv_fixed_result_gradient_bounds
          left.candle_cv_fixed_result_gradient_bounds)
        (candle_cv_fixed_interval_matrix_scale
          left.candle_cv_fixed_result_value_bound
          right.candle_cv_fixed_result_hessian)) in
  candle_cv_fixed_complete radii raw_center raw_hessian;;

type candle_cv_fixed_term_view =
  | Candle_cv_fixed_term_num of Num.num
  | Candle_cv_fixed_term_pair of term * term;;

let candle_cv_fixed_term_view tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then
    match arguments with
    | [argument] -> Candle_cv_fixed_term_num (dest_numeral argument)
    | _ -> failwith "fixed-scale diagnostic: malformed Cexp_num"
  else if aconv operator `Cexp_pair` then
    match arguments with
    | [left;right] -> Candle_cv_fixed_term_pair (left,right)
    | _ -> failwith "fixed-scale diagnostic: malformed Cexp_pair"
  else failwith "fixed-scale diagnostic: non-concrete cval";;

let candle_cv_fixed_term_num tm =
  match candle_cv_fixed_term_view tm with
  | Candle_cv_fixed_term_num value -> value
  | Candle_cv_fixed_term_pair _ ->
      failwith "fixed-scale diagnostic: expected numeral";;

let candle_cv_fixed_term_int tm =
  int_of_string (Num.string_of_num (candle_cv_fixed_term_num tm));;

let candle_cv_fixed_term_pair tm =
  match candle_cv_fixed_term_view tm with
  | Candle_cv_fixed_term_pair pair -> pair
  | Candle_cv_fixed_term_num _ ->
      failwith "fixed-scale diagnostic: expected pair";;

let rec candle_cv_fixed_term_list tm =
  match candle_cv_fixed_term_view tm with
  | Candle_cv_fixed_term_num value ->
      if Num.eq_num value candle_cv_fixed_zero then []
      else failwith "fixed-scale diagnostic: malformed list tail"
  | Candle_cv_fixed_term_pair (head,tail) ->
      head :: candle_cv_fixed_term_list tail;;

let candle_cv_fixed_term_rational tm =
  let signed,denominator_predecessor = candle_cv_fixed_term_pair tm in
  let positive,negative = candle_cv_fixed_term_pair signed in
  Num.sub_num (candle_cv_fixed_term_num positive)
    (candle_cv_fixed_term_num negative),
  Num.add_num (candle_cv_fixed_term_num denominator_predecessor)
    candle_cv_fixed_one;;

let candle_cv_fixed_rational_round_lower (numerator,denominator) =
  candle_cv_fixed_floor_div
    (Num.mul_num numerator candle_cv_fixed_scale) denominator;;

let candle_cv_fixed_rational_round_upper (numerator,denominator) =
  candle_cv_fixed_ceil_div
    (Num.mul_num numerator candle_cv_fixed_scale) denominator;;

let candle_cv_fixed_term_interval tm =
  let lower,upper = candle_cv_fixed_term_pair tm in
  candle_cv_fixed_term_rational lower,candle_cv_fixed_term_rational upper;;

let candle_cv_fixed_term_scaled_rational tm =
  let numerator,denominator = candle_cv_fixed_term_rational tm in
  if not (Num.eq_num denominator candle_cv_fixed_scale) then
    failwith "fixed-scale diagnostic: non-scale denominator";
  numerator;;

let candle_cv_fixed_term_scaled_rational_list tm =
  Array.of_list
    (List.map candle_cv_fixed_term_scaled_rational
      (candle_cv_fixed_term_list tm));;

let candle_cv_fixed_term_center_boxes tm =
  Array.of_list
    (List.map
      (fun interval_tm ->
        let lower,upper = candle_cv_fixed_term_interval interval_tm in
        candle_cv_fixed_rational_round_lower lower,
        candle_cv_fixed_rational_round_upper upper)
      (candle_cv_fixed_term_list tm));;

type candle_cv_fixed_polynomial_instruction =
  | Candle_cv_fixed_polynomial_constant of Num.num * Num.num
  | Candle_cv_fixed_polynomial_variable of int
  | Candle_cv_fixed_polynomial_neg
  | Candle_cv_fixed_polynomial_add
  | Candle_cv_fixed_polynomial_mul
  | Candle_cv_fixed_polynomial_square;;

let candle_cv_fixed_polynomial_instruction tm =
  match candle_cv_fixed_term_view tm with
  | Candle_cv_fixed_term_pair (tag,payload) ->
      if candle_cv_fixed_term_int tag = 0 then
        Candle_cv_fixed_polynomial_constant
          (candle_cv_fixed_term_rational payload)
      else
        Candle_cv_fixed_polynomial_variable
          (candle_cv_fixed_term_int payload)
  | Candle_cv_fixed_term_num opcode ->
      let opcode = int_of_string (Num.string_of_num opcode) in
      if opcode = 2 then Candle_cv_fixed_polynomial_neg
      else if opcode = 3 then Candle_cv_fixed_polynomial_add
      else if opcode = 4 then Candle_cv_fixed_polynomial_mul
      else Candle_cv_fixed_polynomial_square;;

let candle_cv_fixed_polynomial_compile program =
  Array.of_list
    (List.map candle_cv_fixed_polynomial_instruction
      (candle_cv_fixed_term_list program));;

let candle_cv_fixed_zero_matrix dimension =
  Array.init dimension
    (fun _ -> Array.make dimension candle_cv_fixed_interval_zero);;

let candle_cv_fixed_constant radii center_boxes rational =
  let dimension = Array.length center_boxes in
  let center_value =
    candle_cv_fixed_rational_round_lower rational,
    candle_cv_fixed_rational_round_upper rational in
  candle_cv_fixed_complete_rounded radii
    {candle_cv_fixed_first_value = center_value;
     candle_cv_fixed_first_gradient =
       Array.make dimension candle_cv_fixed_interval_zero}
    (candle_cv_fixed_zero_matrix dimension);;

let candle_cv_fixed_variable radii center_boxes variable =
  let dimension = Array.length center_boxes in
  if variable < 0 || variable >= dimension then
    failwith "fixed-scale diagnostic: variable outside dimension";
  candle_cv_fixed_complete_rounded radii
    {candle_cv_fixed_first_value = center_boxes.(variable);
     candle_cv_fixed_first_gradient =
       Array.init dimension
         (fun index ->
           if index = variable then candle_cv_fixed_interval_one
           else candle_cv_fixed_interval_zero)}
    (candle_cv_fixed_zero_matrix dimension);;

let candle_cv_fixed_polynomial_execute radii center_boxes program =
  let stack = ref [] in
  let pop () =
    match !stack with
    | head :: tail -> stack := tail; head
    | [] -> failwith "fixed-scale diagnostic: polynomial stack underflow" in
  let apply instruction =
      match instruction with
      | Candle_cv_fixed_polynomial_constant rational ->
          stack := candle_cv_fixed_constant radii center_boxes rational :: !stack
      | Candle_cv_fixed_polynomial_variable variable ->
          stack := candle_cv_fixed_variable radii center_boxes variable :: !stack
      | Candle_cv_fixed_polynomial_neg ->
          let value = pop () in
          stack := candle_cv_fixed_result_neg radii value :: !stack
      | Candle_cv_fixed_polynomial_add ->
          let right = pop () and left = pop () in
          stack := candle_cv_fixed_result_add radii left right :: !stack
      | Candle_cv_fixed_polynomial_mul ->
          let right = pop () and left = pop () in
          stack := candle_cv_fixed_result_mul radii left right :: !stack
      | Candle_cv_fixed_polynomial_square ->
          let value = pop () in
          stack := candle_cv_fixed_result_mul radii value value :: !stack in
  for index = 0 to Array.length program - 1 do
    apply program.(index)
  done;
  match !stack with
  | [result] -> result
  | remaining ->
      failwith
        ("fixed-scale diagnostic: non-singleton polynomial stack depth=" ^
         string_of_int (List.length remaining));;

let candle_cv_fixed_term_num_make value =
  mk_comb (`Cexp_num`,mk_numeral value);;

let candle_cv_fixed_term_pair_make left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_cv_fixed_term_scaled_rational_make value =
  let positive,negative =
    if Num.lt_num value candle_cv_fixed_zero then
      candle_cv_fixed_zero,Num.minus_num value
    else value,candle_cv_fixed_zero in
  candle_cv_fixed_term_pair_make
    (candle_cv_fixed_term_pair_make
      (candle_cv_fixed_term_num_make positive)
      (candle_cv_fixed_term_num_make negative))
    (candle_cv_fixed_term_num_make
      (Num.sub_num candle_cv_fixed_scale candle_cv_fixed_one));;

let candle_cv_fixed_term_interval_make (lower,upper) =
  candle_cv_fixed_term_pair_make
    (candle_cv_fixed_term_scaled_rational_make lower)
    (candle_cv_fixed_term_scaled_rational_make upper);;

let candle_cv_fixed_term_list_make item_make items =
  candle_cv_fixed_array_fold_right
    (fun item tail -> candle_cv_fixed_term_pair_make (item_make item) tail)
    items (candle_cv_fixed_term_num_make candle_cv_fixed_zero);;

let candle_cv_fixed_term_interval_list_make items =
  candle_cv_fixed_term_list_make candle_cv_fixed_term_interval_make items;;

let candle_cv_fixed_term_interval_matrix_make rows =
  candle_cv_fixed_term_list_make candle_cv_fixed_term_interval_list_make rows;;

let candle_cv_fixed_result_term result =
  let center_term =
    candle_cv_fixed_term_pair_make
      (candle_cv_fixed_term_interval_make
        result.candle_cv_fixed_result_center.candle_cv_fixed_first_value)
      (candle_cv_fixed_term_interval_list_make
        result.candle_cv_fixed_result_center.candle_cv_fixed_first_gradient) in
  candle_cv_fixed_term_pair_make
    (candle_cv_fixed_term_num_make candle_cv_fixed_one)
    (candle_cv_fixed_term_pair_make center_term
      (candle_cv_fixed_term_pair_make
        (candle_cv_fixed_term_interval_make
          result.candle_cv_fixed_result_value_bound)
        (candle_cv_fixed_term_pair_make
          (candle_cv_fixed_term_interval_list_make
            result.candle_cv_fixed_result_gradient_bounds)
          (candle_cv_fixed_term_interval_matrix_make
            result.candle_cv_fixed_result_hessian))));;

end;;
