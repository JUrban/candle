let oracle_digest value =
  Digest.to_hex (Digest.string (Marshal.to_string value []));;

let oracle_left =
  (3 |-> 30) ((1 |-> 10) ((5 |-> 50) Empty));;

let oracle_right =
  (2 |-> 20) ((1 |-> (-10)) ((4 |-> 40) Empty));;

let oracle_replaced = (1 |-> 99) oracle_left;;

let oracle_merged =
  combine ( + ) (fun value -> value = 0) oracle_left oracle_right;;

let oracle_reverse_merged =
  combine ( - ) (fun value -> value = 0) oracle_right oracle_left;;

print_endline
  ("PAIR_SPLIT_ORACLE " ^
   oracle_digest oracle_left ^ " " ^
   oracle_digest oracle_right ^ " " ^
   oracle_digest oracle_replaced ^ " " ^
   oracle_digest oracle_merged ^ " " ^
   oracle_digest oracle_reverse_merged);;
