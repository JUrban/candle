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

let candle_big_int_num_compat_ok =
  List.map candle_big_int_num_render candle_big_int_num_inputs =
  candle_big_int_num_inputs &&
  candle_big_int_num_render_int64 (Int64.of_int (-17)) = "-17" &&
  candle_big_int_num_render_int64 candle_big_int_num_min_int64 =
  "-9223372036854775808";;

if candle_big_int_num_compat_ok then
  print_string "CANDLE_BIG_INT_NUM_COMPAT_OK\n"
else
  failwith "Big_int/Num compatibility mismatch";;
