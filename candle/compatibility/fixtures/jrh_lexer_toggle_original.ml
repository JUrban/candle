unset_jrh_lexer

let flyspeck_jrh_toggle_value =
  String.length "tot";;

let flyspeck_jrh_toggle_oracle =
  flyspeck_jrh_toggle_value = 3;;

if flyspeck_jrh_toggle_oracle then
  print_endline "FLYSPECK_JRH_TOGGLE_ORACLE_OK"
else failwith "Flyspeck JRH toggle oracle mismatch";;

set_jrh_lexer
