let candle_big_int_num_inputs =
  ["0";
   "9223372036854775807";
   "-9223372036854775808";
   "18446744073709551615";
   "-18446744073709551615"];;

let candle_big_int_num_render s =
  Num.string_of_num
    (Num.num_of_big_int (Big_int.big_int_of_string s));;

let candle_big_int_num_render_int64 n =
  Num.string_of_num
    (Num.num_of_big_int
      (Big_int.big_int_of_string (Int64.to_string n)));;

let candle_big_int_num_min_int64 =
  Int64.shift_left (Int64.of_int 32768) 48;;

let candle_big_int_sqrt_inputs =
  [("0","0");
   ("1","1");
   ("2","1");
   ("3","1");
   ("4","2");
   ("15","3");
   ("16","4");
   ("17","4");
   ("340282366920938463463374607431768211455",
    "18446744073709551615")];;

let candle_big_int_render value =
  Num.string_of_num (Num.num_of_big_int value);;

let candle_big_int_sqrt_ok (input,expected) =
  candle_big_int_render
    (Big_int.sqrt_big_int (Big_int.big_int_of_string input)) = expected;;

let candle_big_int_negative_sqrt_rejected =
  try
    let _ = Big_int.sqrt_big_int (Big_int.big_int_of_string "-1") in false
  with _ -> true;;

let candle_big_int_product =
  Big_int.mult_big_int
    (Big_int.big_int_of_string "18446744073709551615")
    (Big_int.big_int_of_string "18446744073709551615");;

let candle_big_int_num_compat_ok =
  List.map candle_big_int_num_render candle_big_int_num_inputs =
  candle_big_int_num_inputs &&
  candle_big_int_num_render_int64 (Int64.of_int (-17)) = "-17" &&
  candle_big_int_num_render_int64 candle_big_int_num_min_int64 =
  "-9223372036854775808" &&
  List.for_all candle_big_int_sqrt_ok candle_big_int_sqrt_inputs &&
  candle_big_int_negative_sqrt_rejected &&
  candle_big_int_render candle_big_int_product =
  "340282366920938463426481119284349108225" &&
  Big_int.eq_big_int candle_big_int_product candle_big_int_product &&
  not (Big_int.eq_big_int candle_big_int_product
         (Big_int.big_int_of_string "0"));;

if candle_big_int_num_compat_ok then
  print_string "CANDLE_BIG_INT_NUM_COMPAT_OK\n"
else
  failwith "Big_int/Num compatibility mismatch";;
