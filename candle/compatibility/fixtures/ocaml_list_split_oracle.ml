module Candle_ocaml_list_split = struct
  open List;;

  let empty_ok = split ([]:(int * string) list) = ([],[]);;
  let numbers,names =
    split [(3,"three"); (1,"one"); (4,"four"); (1,"one-again")];;
  let flags,counts = split [(true,7); (false,11)];;
end;;

let candle_ocaml_list_split_ok =
  Candle_ocaml_list_split.empty_ok &&
  Candle_ocaml_list_split.numbers = [3;1;4;1] &&
  Candle_ocaml_list_split.names = ["three";"one";"four";"one-again"] &&
  Candle_ocaml_list_split.flags = [true;false] &&
  Candle_ocaml_list_split.counts = [7;11];;

if candle_ocaml_list_split_ok then
  print_string "CANDLE_OCAML_LIST_SPLIT_OK\n"
else
  failwith "List.split compatibility mismatch";;
