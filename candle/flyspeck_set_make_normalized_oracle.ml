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

let flyspeck_set_make_values =
  Flyspeck_set_make_replacement.add "b"
    (Flyspeck_set_make_replacement.add "a"
      (Flyspeck_set_make_replacement.add "a"
        Flyspeck_set_make_replacement.empty));;

let candle_flyspeck_set_make_normalized_oracle_ok =
  Flyspeck_set_make_replacement.mem "a" flyspeck_set_make_values &&
  Flyspeck_set_make_replacement.mem "b" flyspeck_set_make_values &&
  not (Flyspeck_set_make_replacement.mem "c" flyspeck_set_make_values);;
