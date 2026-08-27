#use "hol.ml";;
needs "candle/flyspeck_source_digests.ml";;
needs "candle/flyspeck_source_integrity.ml";;

candle_flyspeck_verify_sources 398 "." candle_flyspeck_test_flyspeck_root
  candle_flyspeck_source_digests;;

let candle_flyspeck_digest_negative =
  try
    candle_flyspeck_verify_sources 1 "." candle_flyspeck_test_flyspeck_root
      [("candle","hol.ml","00000000000000000000000000000000")];
    false
  with Failure message ->
    message = "source digest mismatch before Flyspeck build: candle:hol.ml";;

if candle_flyspeck_digest_negative then
  print_endline "CANDLE_FLYSPECK_SOURCE_DIGESTS_OK"
else
  failwith "source digest corruption was not rejected";;
