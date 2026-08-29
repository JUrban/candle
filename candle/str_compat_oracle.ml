let emit label value = print_endline ("STR:" ^ label ^ "=" ^ value)
let emit_bool label value = emit label (if value then "true" else "false")
let render strings = String.concat "," strings

let () =
  emit "first" (Str.first_chars "abcdef" 3);
  emit "split_spaces"
    (render (Str.split (Str.regexp " +") " a  b c "));
  emit "split_negated"
    (render (Str.split (Str.regexp "[^b]+") "aaabbbcc"));
  emit "split_class"
    (render (Str.split (Str.regexp "[ |=]+") " A|B = C "));
  emit "split_literal"
    (render (Str.split (Str.regexp " ") " x  y "));
  emit_bool "match_version"
    (Str.string_match (Str.regexp "Ocaml 4.") "Ocaml 4.14.1" 0);
  emit_bool "match_prefix_star"
    (Str.string_match (Str.regexp ".*ABC") "xxABC" 0);
  emit_bool "match_class"
    (Str.string_match
       (Str.regexp "prep-OXLZLEZ 6346351218 [1234]")
       "prep-OXLZLEZ 6346351218 3" 0);
  emit_bool "match_offset"
    (Str.string_match (Str.regexp "a+b?") "zaaab" 1);
  emit_bool "match_negative"
    (Str.string_match (Str.regexp "a+b?") "zbbb" 1);
  emit "replace_underscore"
    (Str.global_replace (Str.regexp "_") "" "a_b__c");
  emit "replace_range"
    (Str.global_replace (Str.regexp "[a-c]+") "X" "0abc1ca2")
