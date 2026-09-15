let glpk_format_failure =
  "Candle Flyspeck: non-verification GLPK formatter is disabled";;

let sprintf _ = failwith glpk_format_failure;;

let glpk_format_int () = sprintf "%d" 7;;
let glpk_format_strings () = sprintf "%s%s" "left" "right";;
let glpk_format_float () = sprintf "%3.3f" 1.25;;
let glpk_format_mixed () = sprintf "%s%d%s%f" "a" 1 "b" 2.5;;

let glpk_expect_failure thunk =
  try
    let _ = thunk () in false
  with Failure msg -> msg = glpk_format_failure;;

let candle_glpk_fail_closed_sprintf_ok =
  glpk_expect_failure glpk_format_int &&
  glpk_expect_failure glpk_format_strings &&
  glpk_expect_failure glpk_format_float &&
  glpk_expect_failure glpk_format_mixed;;
