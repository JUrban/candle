(* Pinned OCaml 4.14.1 differential witness for the exact LP branch shape. *)
let samples =
  [min_int; min_int + 1; -1073741824; -2; -1; 0; 1; 2; 1073741823;
   max_int - 1; max_int];;

if List.for_all (fun n -> (n == 1) = (n = 1)) samples then
  print_endline "flyspeck-immediate-ocaml-oracle: ok"
else
  failwith "physical and value equality differ on a sampled OCaml int";;
