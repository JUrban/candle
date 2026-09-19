(* Native OCaml oracle for Serialization's complete five-site string-sort
   normalization. This is compatibility evidence, not proof evidence. *)

let samples =
  [""; "0"; "00"; "09af"; "0a"; "63e9b5b016229a78bb720593f38b0b3e";
   "9e9bbb6556672ce154be3c9e28380e33"; "a"; "aa"; "bool"; "fun";
   "list_of_elements"; "z"];;

let all_pairs predicate values =
  List.for_all
    (fun left -> List.for_all (fun right -> predicate left right) values)
    values;;

let string_order_equivalent =
  all_pairs
    (fun left right ->
       (left < right) = (String.compare left right < 0))
    samples;;

let keyed_samples = List.map (fun key -> key,String.length key) samples;;

let keyed_order_equivalent =
  all_pairs
    (fun left right ->
       (fst left < fst right) =
       (String.compare (fst left) (fst right) < 0))
    keyed_samples;;

if not (string_order_equivalent && keyed_order_equivalent) then
  failwith "Serialization string comparator oracle mismatch";;

print_endline "CANDLE_SERIALIZATION_STRING_ORDER_OCAML_OK";;
