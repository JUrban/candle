(* Compare exact-Num and float-only untrusted point-certificate preparation. *)

needs "candle/cv_compute_analytic_expr_disjunctive_third_sibling_batch.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan;;
open Candle_cv_analytic_expr_disjunctive_third_sibling_batch;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let rec candle_disjunctive_float_point_take count values =
  if count <= 0 then []
  else
    match values with
    | [] -> []
    | head::tail ->
        head :: candle_disjunctive_float_point_take (count - 1) tail;;

let candle_disjunctive_float_point_tagged =
  candle_disjunctive_next_batch_tag 16480 0
    candle_disjunctive_case16480_leaves @
  candle_disjunctive_next_batch_tag 16339 0
    candle_disjunctive_case16339_leaves @
  candle_disjunctive_next_batch_tag 16595 0
    candle_disjunctive_case16595_leaves;;
let candle_disjunctive_float_point_function0 =
  List.filter
    (fun (_,_,selected,_) -> selected = 0)
    candle_disjunctive_float_point_tagged;;
let candle_disjunctive_float_point_function1 =
  List.filter
    (fun (_,_,selected,_) -> selected = 1)
    candle_disjunctive_float_point_tagged;;
let candle_disjunctive_float_point_sample0 =
  candle_disjunctive_float_point_take 59
    candle_disjunctive_float_point_function0;;
let candle_disjunctive_float_point_sample1 =
  candle_disjunctive_float_point_take 1024
    candle_disjunctive_float_point_function1;;

let rec candle_disjunctive_float_point_lookup index = function
  | [] -> failwith "float point plan benchmark: program value shape"
  | value::remaining ->
      if index = 0 then value
      else candle_disjunctive_float_point_lookup (index - 1) remaining;;

let candle_disjunctive_float_point_power base exponent =
  if exponent < 0 then
    failwith "float point plan benchmark: negative exponent";
  let rec power accumulator base exponent =
    if exponent = 0 then accumulator
    else if exponent mod 2 = 0 then power accumulator (base *. base) (exponent / 2)
    else power (accumulator *. base) (base *. base) (exponent / 2) in
  power 1.0 base exponent;;

let candle_disjunctive_float_point_program_value values program =
  let rec evaluate = function
    | Candle_q_point_rational_constant value -> Num.float_of_num value
    | Candle_q_point_rational_variable index ->
        candle_disjunctive_float_point_lookup index values
    | Candle_q_point_rational_neg child -> -. (evaluate child)
    | Candle_q_point_rational_add (left,right) ->
        evaluate left +. evaluate right
    | Candle_q_point_rational_sub (left,right) ->
        evaluate left -. evaluate right
    | Candle_q_point_rational_mul (left,right) ->
        evaluate left *. evaluate right
    | Candle_q_point_rational_div (left,right) ->
        evaluate left /. evaluate right
    | Candle_q_point_rational_inv child -> 1.0 /. evaluate child
    | Candle_q_point_rational_pow (base,exponent) ->
        candle_disjunctive_float_point_power
          (evaluate base) (Num.int_of_num exponent) in
  evaluate program;;

let candle_disjunctive_float_point_centers lower upper =
  if length lower <> length upper then
    failwith "float point plan benchmark: box shape";
  map2
    (fun lower_term upper_term ->
      (Num.float_of_num (rat_of_term lower_term) +.
       Num.float_of_num (rat_of_term upper_term)) /. 2.0)
    lower upper;;

let candle_disjunctive_float_point_sqrt_interval argument =
  if Stdlib.Float.compare argument 0.0 <> 1 then
    failwith "float point plan benchmark: nonpositive square-root argument";
  let scale = candle_q_point_sqrt_scale in
  let approximate = Stdlib.sqrt argument in
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

let candle_disjunctive_float_point_intervals plan lower upper =
  if length lower <> 6 || length upper <> 6 then
    failwith "float point plan benchmark: expected six coordinates";
  let values = candle_disjunctive_float_point_centers lower upper in
  map
    (fun program ->
      candle_disjunctive_float_point_sqrt_interval
        (candle_disjunctive_float_point_program_value values program))
    plan.point_plan_programs;;

let candle_disjunctive_float_point_prepare_exact plan jobs =
  map
    (fun (_,_,_,domain) ->
      let lower,upper =
        candle_disjunctive_fixed_outer_domain_bounds domain in
      candle_q_dim_taylor_model_point_plan_intervals_six plan lower upper)
    jobs;;

let candle_disjunctive_float_point_prepare_float plan jobs =
  map
    (fun (_,_,_,domain) ->
      let lower,upper =
        candle_disjunctive_fixed_outer_domain_bounds domain in
      candle_disjunctive_float_point_intervals plan lower upper)
    jobs;;

let rec candle_disjunctive_float_point_equal_terms left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_float_point_equal_terms left_tail right_tail
  | _ -> false;;

let rec candle_disjunctive_float_point_equal_batches left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      candle_disjunctive_float_point_equal_terms left_head right_head &&
      candle_disjunctive_float_point_equal_batches left_tail right_tail
  | _ -> false;;

let candle_disjunctive_float_point_mismatches left right =
  let rec collect index left right =
    match left,right with
    | [],[] -> []
    | left_head::left_tail,right_head::right_tail ->
        let remaining = collect (index + 1) left_tail right_tail in
        if candle_disjunctive_float_point_equal_terms left_head right_head
        then remaining else index::remaining
    | _ -> failwith "float point plan benchmark: result cardinality" in
  collect 0 left right;;

let candle_disjunctive_float_point_axioms_before = axioms ();;

print_endline
  "CANDLE_CV_FLOAT_POINT_PLAN_EXACT_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_disjunctive_float_point_exact0 =
  candle_disjunctive_float_point_prepare_exact
    candle_disjunctive_next_batch_point_plan0
    candle_disjunctive_float_point_sample0;;
let candle_disjunctive_float_point_exact1 =
  candle_disjunctive_float_point_prepare_exact
    candle_disjunctive_next_batch_point_plan1
    candle_disjunctive_float_point_sample1;;
print_endline
  "CANDLE_CV_FLOAT_POINT_PLAN_EXACT_END DEVELOPMENT_NON_RELEASE";;

print_endline
  "CANDLE_CV_FLOAT_POINT_PLAN_FLOAT_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_disjunctive_float_point_float0 =
  candle_disjunctive_float_point_prepare_float
    candle_disjunctive_next_batch_point_plan0
    candle_disjunctive_float_point_sample0;;
let candle_disjunctive_float_point_float1 =
  candle_disjunctive_float_point_prepare_float
    candle_disjunctive_next_batch_point_plan1
    candle_disjunctive_float_point_sample1;;
print_endline
  "CANDLE_CV_FLOAT_POINT_PLAN_FLOAT_END DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_float_point_mismatches0 =
  candle_disjunctive_float_point_mismatches
    candle_disjunctive_float_point_exact0
    candle_disjunctive_float_point_float0;;
let candle_disjunctive_float_point_mismatches1 =
  candle_disjunctive_float_point_mismatches
    candle_disjunctive_float_point_exact1
    candle_disjunctive_float_point_float1;;
let _ =
  if candle_disjunctive_float_point_mismatches0 <> [] ||
     candle_disjunctive_float_point_mismatches1 <> [] then
    print_endline
      ("CANDLE_CV_FLOAT_POINT_PLAN_MISMATCH DEVELOPMENT_NON_RELEASE" ^
       " function0_indices=" ^
       candle_cv_fso_variable_jobs_scan_indices_string
         candle_disjunctive_float_point_mismatches0 ^
       " function1_indices=" ^
       candle_cv_fso_variable_jobs_scan_indices_string
         candle_disjunctive_float_point_mismatches1);;

let candle_disjunctive_float_point_axioms_after = axioms ();;
if length candle_disjunctive_float_point_sample0 <> 59 ||
   length candle_disjunctive_float_point_sample1 <> 1024 ||
   candle_disjunctive_float_point_mismatches0 <> [] ||
   candle_disjunctive_float_point_mismatches1 <> [] ||
   length candle_disjunctive_float_point_axioms_after <>
     length candle_disjunctive_float_point_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_float_point_axioms_before)
       candle_disjunctive_float_point_axioms_after) then
  failwith "float point plan benchmark: exact/float mismatch";;

print_endline
  "CANDLE_CV_FLOAT_POINT_PLAN_EQUIVALENCE_OK DEVELOPMENT_NON_RELEASE jobs=1083 function0=59 function1=1024 exact_interval_terms_equal=true assumptions=0 axiom_growth=0";;

end;;
