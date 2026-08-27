module Flyspeck_set_make_order = struct
  type t = string
  let compare = String.compare
end;;

module Flyspeck_set_make_reference = Set.Make(Flyspeck_set_make_order);;

module Flyspeck_set_make_replacement = struct
  type elt = string
  type t = string list
  let empty = []
  let rec mem value values =
    match values with
      [] -> false
    | head::tail -> value = head || mem value tail
  let add value values =
    if mem value values then values else value::values
end;;

let flyspeck_set_make_require condition =
  if condition then () else failwith "Flyspeck Set.Make replacement differs";;

let flyspeck_set_make_inputs =
  [[]; [""]; ["a"]; ["a";"a"]; ["b";"a"]; ["a";"b";"a"]];;

List.iter
  (fun input ->
    let reference = List.fold_right Flyspeck_set_make_reference.add input
      Flyspeck_set_make_reference.empty in
    let replacement = List.fold_right Flyspeck_set_make_replacement.add input
      Flyspeck_set_make_replacement.empty in
    List.iter
      (fun query ->
        flyspeck_set_make_require
          (Flyspeck_set_make_reference.mem query reference =
           Flyspeck_set_make_replacement.mem query replacement))
      ["";"a";"b";"c"])
  flyspeck_set_make_inputs;;

print_endline "flyspeck-set-make-ocaml-oracle: ok";;
