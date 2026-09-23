let candle_certificate_float_le_raw left right =
  itlist2 (fun a b c -> c && (a <= b)) left right true;;

let _ = candle_certificate_float_le_raw [0.0; 2.0] [1.0; 2.0];;
