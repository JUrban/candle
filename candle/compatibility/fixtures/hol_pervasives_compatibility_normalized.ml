let flyspeck_hol_pervasives_needs_fail_closed =
  try
    Hol_pervasives.needs "unselected-dynamic-source.hl";
    false
  with Failure message ->
    message =
      "Candle Flyspeck: dynamic Hol_pervasives.needs is disabled by the static manifest: unselected-dynamic-source.hl";;

let flyspeck_hol_pervasives_string_order =
  Hol_pervasives.sort
    (fun x y -> String.compare x y < 0)
    ["z"; "a"; "m"; "a"];;

let flyspeck_hol_pervasives_string_order_ok =
  flyspeck_hol_pervasives_string_order = ["a"; "a"; "m"; "z"];;

let flyspeck_hol_pervasives_compatibility_oracle_ok =
  flyspeck_hol_pervasives_needs_fail_closed &&
  flyspeck_hol_pervasives_string_order_ok;;
