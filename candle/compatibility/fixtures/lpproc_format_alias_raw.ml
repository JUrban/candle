(* DEVELOPMENT reproducer for Lpproc.ampl_of_bb's local sprintf alias. *)
let candle_lpproc_disabled_format _ =
  failwith "Candle Flyspeck: non-verification GLPK formatter is disabled";;

let candle_lpproc_format_alias_raw () =
  let p = candle_lpproc_disabled_format in
  let integer_call () = p "integer" 7 in
  let string_call () = p "string" "hypermap" in
  (integer_call,string_call);;
