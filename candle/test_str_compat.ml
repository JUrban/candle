#use "candle/build/insulate.ml";;
#use "candle/nums.ml";;
#use "candle/pretty.ml";;
#use "candle/ocaml.ml";;

let candle_str_emit label value =
  print_endline ("STR:" ^ label ^ "=" ^ value);;
let candle_str_emit_bool label value =
  candle_str_emit label (if value then "true" else "false");;
let candle_str_render strings = String.concat "," strings;;

candle_str_emit "first" (Str.first_chars "abcdef" 3);;
candle_str_emit "split_spaces"
  (candle_str_render (Str.split (Str.regexp " +") " a  b c "));;
candle_str_emit "split_negated"
  (candle_str_render (Str.split (Str.regexp "[^b]+") "aaabbbcc"));;
candle_str_emit "split_class"
  (candle_str_render (Str.split (Str.regexp "[ |=]+") " A|B = C "));;
candle_str_emit "split_literal"
  (candle_str_render (Str.split (Str.regexp " ") " x  y "));;
candle_str_emit_bool "match_version"
  (Str.string_match (Str.regexp "Ocaml 4.") "Ocaml 4.14.1" 0);;
candle_str_emit_bool "match_prefix_star"
  (Str.string_match (Str.regexp ".*ABC") "xxABC" 0);;
candle_str_emit_bool "match_class"
  (Str.string_match
     (Str.regexp "prep-OXLZLEZ 6346351218 [1234]")
     "prep-OXLZLEZ 6346351218 3" 0);;
candle_str_emit_bool "match_offset"
  (Str.string_match (Str.regexp "a+b?") "zaaab" 1);;
candle_str_emit_bool "match_negative"
  (Str.string_match (Str.regexp "a+b?") "zbbb" 1);;
candle_str_emit "replace_underscore"
  (Str.global_replace (Str.regexp "_") "" "a_b__c");;
candle_str_emit "replace_range"
  (Str.global_replace (Str.regexp "[a-c]+") "X" "0abc1ca2");;

let candle_str_rejects_grouping =
  try let _ = Str.regexp "\\(a\\)" in false
  with Invalid_argument _ -> true;;
candle_str_emit_bool "reject_grouping" candle_str_rejects_grouping;;

print_endline "CANDLE_STR_COMPAT_OK";;
