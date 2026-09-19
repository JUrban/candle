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

let candle_num_big_int_roundtrip s =
  Big_int.eq_big_int
    (Num.big_int_of_num
      (Num.num_of_big_int (Big_int.big_int_of_string s)))
    (Big_int.big_int_of_string s);;

let candle_num_noninteger_big_int_rejected =
  try
    let _ = Num.big_int_of_num
      (Num.div_num (Num.num_of_int 3) (Num.num_of_int 2)) in false
  with _ -> true;;

let candle_num_integer s =
  Num.num_of_big_int (Big_int.big_int_of_string s);;

let candle_num_ratio numerator denominator =
  Num.div_num (candle_num_integer numerator)
    (candle_num_integer denominator);;

let candle_num_approx_exp_inputs =
  [(6, candle_num_integer "0", "+0.000000e0");
   (6, candle_num_integer "1", "+0.100000e1");
   (6, candle_num_integer "-1", "-0.100000e1");
   (6, candle_num_ratio "3" "2", "+0.150000e1");
   (6, candle_num_ratio "1" "3", "+0.333333e0");
   (6, candle_num_integer "123456789", "+0.123457e9");
   (6, candle_num_integer "9999995", "+1.000000e7");
   (10, candle_num_ratio "1" "100000000000000000000",
    "+0.1000000000e-19");
   (30, candle_num_integer
      "340282366920938463463374607431768211455",
    "+0.340282366920938463463374607432e39")];;

let candle_num_approx_exp_ok (precision,value,expected) =
  Num.approx_num_exp precision value = expected;;

let candle_num_remaining_surface_ok =
  let half = candle_num_ratio "1" "2" and
      three_halves = candle_num_ratio "3" "2" in
  Num.string_of_num (Num.pred_num three_halves) = "1/2" &&
  Num.compare_num half three_halves = -1 &&
  Num.compare_num three_halves three_halves = 0 &&
  Num.compare_num three_halves half = 1 &&
  List.for_all candle_num_approx_exp_ok candle_num_approx_exp_inputs;;

let candle_num_approx_differential_observations =
  let precisions = [1;2;3;6;10] and
      numerators =
        [-9999; -995; -25; -15; -1; 0; 1; 3; 5;
         14; 15; 25; 95; 99; 995; 999; 9999] and
      denominators = [1;2;3;7;20;1001] in
  let render precision numerator denominator =
    let value =
      Num.div_num (Num.num_of_int numerator) (Num.num_of_int denominator) in
    string_of_int precision ^ ":" ^ string_of_int numerator ^ "/" ^
      string_of_int denominator ^ ":" ^ Num.approx_num_exp precision value in
  List.flatten
    (List.map
      (fun precision ->
        List.flatten
          (List.map
            (fun numerator ->
              List.map (render precision numerator) denominators)
            numerators))
      precisions);;

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

let candle_big_int_division_inputs =
  [("-17", "5", "-4", "3");
   ("17", "-5", "-3", "2");
   ("-17", "-5", "4", "3");
   ("17", "5", "3", "2")];;

let candle_big_int_division_ok (left,right,quotient,remainder) =
  let left = Big_int.big_int_of_string left and
      right = Big_int.big_int_of_string right in
  let observed_quotient,observed_remainder =
    Big_int.quomod_big_int left right in
  candle_big_int_render observed_quotient = quotient &&
  candle_big_int_render observed_remainder = remainder &&
  Big_int.eq_big_int (Big_int.div_big_int left right) observed_quotient &&
  Big_int.eq_big_int (Big_int.mod_big_int left right) observed_remainder;;

let candle_big_int_arithmetic_ok =
  let large = Big_int.big_int_of_string "18446744073709551615" and
      seventeen = Big_int.big_int_of_int 17 in
  Big_int.eq_big_int Big_int.zero_big_int (Big_int.big_int_of_int 0) &&
  Big_int.sign_big_int (Big_int.big_int_of_int (-17)) = -1 &&
  Big_int.sign_big_int Big_int.zero_big_int = 0 &&
  Big_int.sign_big_int seventeen = 1 &&
  candle_big_int_render
    (Big_int.abs_big_int (Big_int.big_int_of_string
      "-18446744073709551615")) = "18446744073709551615" &&
  candle_big_int_render
    (Big_int.add_big_int large seventeen) = "18446744073709551632" &&
  candle_big_int_render
    (Big_int.sub_big_int large seventeen) = "18446744073709551598" &&
  candle_big_int_render (Big_int.succ_big_int large) =
    "18446744073709551616" &&
  candle_big_int_render (Big_int.pred_big_int large) =
    "18446744073709551614" &&
  candle_big_int_render (Big_int.mult_int_big_int (-3) large) =
    "-55340232221128654845" &&
  candle_big_int_render (Big_int.power_int_positive_int 17 23) =
    "19967568900859523802559065713" &&
  Big_int.le_big_int seventeen large &&
  Big_int.lt_big_int seventeen large &&
  not (Big_int.lt_big_int large seventeen);;

let candle_big_int_negative_power_rejected =
  try
    let _ = Big_int.power_int_positive_int 2 (-1) in false
  with _ -> true;;

let candle_big_int_num_compat_ok =
  List.map candle_big_int_num_render candle_big_int_num_inputs =
  candle_big_int_num_inputs &&
  candle_big_int_num_render_int64 (Int64.of_int (-17)) = "-17" &&
  candle_big_int_num_render_int64 candle_big_int_num_min_int64 =
  "-9223372036854775808" &&
  List.for_all candle_num_big_int_roundtrip candle_big_int_num_inputs &&
  candle_num_noninteger_big_int_rejected &&
  candle_num_remaining_surface_ok &&
  List.for_all candle_big_int_sqrt_ok candle_big_int_sqrt_inputs &&
  candle_big_int_negative_sqrt_rejected &&
  candle_big_int_render candle_big_int_product =
  "340282366920938463426481119284349108225" &&
  Big_int.eq_big_int candle_big_int_product candle_big_int_product &&
  not (Big_int.eq_big_int candle_big_int_product
         (Big_int.big_int_of_string "0")) &&
  List.for_all candle_big_int_division_ok
    candle_big_int_division_inputs &&
  candle_big_int_arithmetic_ok &&
  candle_big_int_negative_power_rejected;;

if candle_big_int_num_compat_ok then
  (print_string "CANDLE_BIG_INT_NUM_COMPAT_OK\n";
   print_endline
     ("CANDLE_NUM_APPROX_OBSERVATIONS " ^
      String.concat "|" candle_num_approx_differential_observations))
else
  failwith "Big_int/Num compatibility mismatch";;
