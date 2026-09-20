needs "candle/cv_compute_exact_interval_reify.ml";;

open Candle_cv_exact_interval_reify;;

let candle_q_taylor_variables =
  [`x1:real`;`x2:real`;`x3:real`;`x4:real`;`x5:real`;`x6:real`];;

let candle_q_taylor_add = `(+):real->real->real`;;
let candle_q_taylor_mul = `(*):real->real->real`;;

let candle_q_taylor_coefficient numerator =
  term_of_rat
    (Num.num_of_int numerator // Num.num_of_int 16);;

let rec candle_q_taylor_first_terms index =
  if index = 6 then []
  else
    mk_binop candle_q_taylor_mul
      (candle_q_taylor_coefficient (index + 2))
      (List.nth candle_q_taylor_variables index)::
    candle_q_taylor_first_terms (index + 1);;

let rec candle_q_taylor_second_terms row column =
  if row = 6 then []
  else if column = 6 then candle_q_taylor_second_terms (row + 1) (row + 1)
  else
    let product =
      mk_binop candle_q_taylor_mul
        (List.nth candle_q_taylor_variables row)
        (List.nth candle_q_taylor_variables column) in
    mk_binop candle_q_taylor_mul
      (candle_q_taylor_coefficient (17 + row * 6 + column)) product::
    candle_q_taylor_second_terms row (column + 1);;

let candle_q_taylor_terms =
  candle_q_taylor_first_terms 0 @ candle_q_taylor_second_terms 0 0;;

let candle_q_taylor_expression =
  end_itlist
    (fun term rest -> mk_binop candle_q_taylor_add term rest)
    candle_q_taylor_terms;;

let candle_q_taylor_q numerator denominator =
  mk_pair
    (mk_pair
      (mk_numeral (Num.num_of_int numerator),mk_numeral (Num.num_of_int 0)),
     mk_numeral (Num.num_of_int (denominator - 1)));;

let rec candle_q_taylor_intervals_from index =
  if index = 6 then []
  else
    mk_pair
      (candle_q_taylor_q (index + 1) 8,
       candle_q_taylor_q (index + 2) 8)::
    candle_q_taylor_intervals_from (index + 1);;

let candle_q_taylor_intervals =
  mk_list
    (candle_q_taylor_intervals_from 0,candle_q_interval_type);;

print_endline "CANDLE_CV_TAYLOR_PROFILE stage=reify event=begin";;

let candle_q_taylor_program,candle_q_taylor_real_th =
  candle_q_reify_real_expression
    candle_q_taylor_variables candle_q_taylor_expression;;

print_endline
  ("CANDLE_CV_TAYLOR_PROFILE stage=reify event=end instructions=" ^
   string_of_int (length (dest_list candle_q_taylor_program)));;

print_endline "CANDLE_CV_TAYLOR_PROFILE stage=compute event=begin";;

let _,_,candle_q_taylor_result,_,candle_q_taylor_compute_th,
    candle_q_taylor_result_th =
  candle_q_compute_interval_program
    candle_q_taylor_variables candle_q_taylor_intervals
    candle_q_taylor_expression candle_q_taylor_program
    candle_q_taylor_real_th;;

let rec candle_q_num_bits value count =
  if value =/ Num.num_of_int 0 then count
  else candle_q_num_bits
    (Num.quo_num (Num.abs_num value) (Num.num_of_int 2)) (count + 1);;

let candle_q_taylor_interval = hd (dest_list candle_q_taylor_result);;
let candle_q_taylor_lo,candle_q_taylor_hi =
  dest_pair candle_q_taylor_interval;;
let candle_q_taylor_lo_z,candle_q_taylor_lo_d =
  dest_pair candle_q_taylor_lo;;
let candle_q_taylor_hi_z,candle_q_taylor_hi_d =
  dest_pair candle_q_taylor_hi;;
let candle_q_taylor_lo_p,candle_q_taylor_lo_n =
  dest_pair candle_q_taylor_lo_z;;
let candle_q_taylor_hi_p,candle_q_taylor_hi_n =
  dest_pair candle_q_taylor_hi_z;;

let candle_q_taylor_stat name tm =
  let value = dest_numeral tm in
  name ^ "=" ^ string_of_int (candle_q_num_bits value 0);;

print_endline
  (String.concat " "
    ["CANDLE_CV_TAYLOR_PROFILE stage=compute event=end";
     "terms=" ^ string_of_int (length candle_q_taylor_terms);
     candle_q_taylor_stat "lo_positive_bits" candle_q_taylor_lo_p;
     candle_q_taylor_stat "lo_negative_bits" candle_q_taylor_lo_n;
     candle_q_taylor_stat "lo_denominator_predecessor_bits"
       candle_q_taylor_lo_d;
     candle_q_taylor_stat "hi_positive_bits" candle_q_taylor_hi_p;
     candle_q_taylor_stat "hi_negative_bits" candle_q_taylor_hi_n;
     candle_q_taylor_stat "hi_denominator_predecessor_bits"
       candle_q_taylor_hi_d]);;

if hyp candle_q_taylor_real_th <> [] ||
   hyp candle_q_taylor_compute_th <> [] ||
   hyp candle_q_taylor_result_th <> []
then failwith "Taylor profile theorem has assumptions";;

print_endline "CANDLE_CV_TAYLOR_PROFILE_OK";;
