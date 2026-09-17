(* Give the integer and string uses independent concrete aliases. *)
let candle_lpproc_disabled_format _ =
  failwith "Candle Flyspeck: non-verification GLPK formatter is disabled";;

let candle_lpproc_format_alias_normalized () =
  let p_int = candle_lpproc_disabled_format in
  let p = candle_lpproc_disabled_format in
  let integer_call () = p_int "integer" 7 in
  let string_call () = p "string" "hypermap" in
  (integer_call,string_call);;

let candle_lpproc_format_alias_ok =
  let integer_call,string_call = candle_lpproc_format_alias_normalized () in
  let expected thunk =
    try let _ = thunk () in false with Failure message ->
      message =
        "Candle Flyspeck: non-verification GLPK formatter is disabled" in
  expected integer_call && expected string_call;;
