let int_pairs =
  [(0,0); (1,2); (-1,3); (max_int,min_int)];;

let check_pair (left,right) =
  Printf.sprintf "%d / %d" left right =
    string_of_int left ^ " / " ^ string_of_int right;;

let check_named name current total =
  Printf.sprintf "Processing: %s (%d / %d)" name current total =
    "Processing: " ^ name ^ " (" ^ string_of_int current ^ " / " ^
      string_of_int total ^ ")" &&
  Printf.sprintf "Adding %s (%d / %d)" name current total =
    "Adding " ^ name ^ " (" ^ string_of_int current ^ " / " ^
      string_of_int total ^ ")";;

let check_verify remaining current total =
  Printf.sprintf "(%d) %d/%d" remaining current total =
    "(" ^ string_of_int remaining ^ ") " ^ string_of_int current ^ "/" ^
      string_of_int total;;

let candle_lp_fixed_format_ocaml_oracle_ok =
  List.for_all check_pair int_pairs &&
  check_named "ineq-name" (-7) 41 &&
  check_verify 39 4 107 &&
  Printf.sprintf "Problem: %s (%s)" "alpha" "beta" =
    "Problem: alpha (beta)" &&
  Printf.sprintf "%d " min_int = string_of_int min_int ^ " " &&
  Printf.sprintf "terminals = %d: " max_int =
    "terminals = " ^ string_of_int max_int ^ ": " &&
  Printf.sprintf "Verifying %s" "cert.dat" = "Verifying cert.dat";;

if candle_lp_fixed_format_ocaml_oracle_ok then
  print_endline "LP_FIXED_FORMAT_OCAML_ORACLE_OK"
else failwith "LP fixed-format OCaml oracle failed";;
