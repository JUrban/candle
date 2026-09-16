let lp_pair left right =
  string_of_int left ^ " / " ^ string_of_int right;;

let lp_processing name current total =
  "Processing: " ^ name ^ " (" ^ string_of_int current ^ " / " ^
    string_of_int total ^ ")";;

let lp_adding name current total =
  "Adding " ^ name ^ " (" ^ string_of_int current ^ " / " ^
    string_of_int total ^ ")";;

let lp_verify remaining current total =
  "(" ^ string_of_int remaining ^ ") " ^ string_of_int current ^ "/" ^
    string_of_int total;;

let candle_lp_fixed_format_normalized_ok =
  lp_pair (-1) 3 = "-1 / 3" &&
  lp_processing "ineq-name" (-7) 41 = "Processing: ineq-name (-7 / 41)" &&
  lp_adding "ineq-name" (-7) 41 = "Adding ineq-name (-7 / 41)" &&
  lp_verify 39 4 107 = "(39) 4/107" &&
  ("Problem: " ^ "alpha" ^ " (" ^ "beta" ^ ")") =
    "Problem: alpha (beta)" &&
  (string_of_int (-12) ^ " ") = "-12 " &&
  ("terminals = " ^ string_of_int 5 ^ ": ") = "terminals = 5: " &&
  ("Verifying " ^ "cert.dat") = "Verifying cert.dat";;
