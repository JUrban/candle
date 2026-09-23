let candle_certificate_float_le left right =
  itlist2 (fun a b c -> c && float_ieee_le a b) left right true;;

let candle_certificate_float_subdomain_ok =
  candle_certificate_float_le [0.0; 2.0] [1.0; 2.0] &&
  not (candle_certificate_float_le [0.0; 3.0] [1.0; 2.0]) &&
  not (candle_certificate_float_le [0.0 /. 0.0] [1.0]);;

if candle_certificate_float_subdomain_ok then
  print_string "CANDLE_CERTIFICATE_FLOAT_SUBDOMAIN_OK\n"
else
  failwith "explicit certificate float order changed subdomain semantics";;
