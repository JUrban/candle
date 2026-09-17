let candle_int64_words =
  let low = Int64.of_int 65535 in
  let high = Int64.shift_left low 48 in
  let middle = Int64.shift_left (Int64.of_int 4660) 16 in
  Int64.logor high (Int64.logor middle low);;

let candle_int64_min =
  Int64.shift_left (Int64.of_int 32768) 48;;

let candle_int64_compat_ok =
  Int64.to_string (Int64.of_float 1234567890.75) = "1234567890" &&
  Int64.to_string (Int64.of_float (-1234567890.75)) = "-1234567890" &&
  Int64.to_string (Int64.of_int (-17)) = "-17" &&
  Int64.to_string candle_int64_words = "-281474671247361" &&
  Int64.to_string candle_int64_min = "-9223372036854775808" &&
  Int64.to_string
    (Int64.logor candle_int64_min (Int64.of_int 7)) =
    "-9223372036854775801";;

if candle_int64_compat_ok then
  print_string "CANDLE_INT64_COMPAT_OK\n"
else
  failwith "Int64 compatibility mismatch";;
