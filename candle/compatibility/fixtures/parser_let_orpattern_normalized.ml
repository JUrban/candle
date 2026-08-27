type flyspeck_parser_term =
    Varp of string * int
  | Combp of flyspeck_parser_term * flyspeck_parser_term
  | Leafp of int;;

let flyspeck_pdest_eq
    (Combp(Combp(Varp(opname,_),l),r)) =
  match opname with "=" | "<=>" -> l,r;;

let flyspeck_parser_input opname =
  Combp(Combp(Varp(opname,0),Leafp 1),Leafp 2);;

let flyspeck_parser_rejects input =
  try let _ = flyspeck_pdest_eq input in false
  with _ -> true;;

let flyspeck_parser_message n =
  "parse_pretype_verbose: mk_prefinty, n = " ^ n;;

let flyspeck_parser_trailing_semicolon x = (ignore x; x + 1);;

let flyspeck_parser_orpattern_oracle_ok =
  flyspeck_pdest_eq (flyspeck_parser_input "=") = (Leafp 1,Leafp 2) &&
  flyspeck_pdest_eq (flyspeck_parser_input "<=>") = (Leafp 1,Leafp 2) &&
  flyspeck_parser_rejects (flyspeck_parser_input "==>") &&
  flyspeck_parser_rejects (Leafp 3) &&
  flyspeck_parser_message "12/7" =
    "parse_pretype_verbose: mk_prefinty, n = 12/7" &&
  flyspeck_parser_trailing_semicolon 6 = 7;;

if flyspeck_parser_orpattern_oracle_ok then
  print "FLYSPECK_PARSER_ORPATTERN_ORACLE_OK\n"
else failwith "Flyspeck parser or-pattern oracle mismatch";;
