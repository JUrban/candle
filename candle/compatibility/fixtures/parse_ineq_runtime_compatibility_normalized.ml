#use "candle/build/insulate.ml";;

type candle_parse_tag = Candle_parse_eps of double | Candle_parse_other;;

let rec candle_parse_geteps =
  let getepsf = function Candle_parse_eps value -> value | _ -> 0.0 in
  function
  | [] -> 0.0
  | head::tail ->
      let current = getepsf head
      and remaining = candle_parse_geteps tail in
      if Cake.Double.(>) current remaining
      then current else remaining;;

let candle_parse_acs = function
  | [value] -> "(acos(" ^ value ^ "))"
  | [] -> "(acos)"
  | _ -> failwith "ocaml:acs";;

let candle_parse_acs_outcome operation values =
  try Some (operation values) with Failure message -> Some message;;

let (candle_parse_counter,candle_parse_counter_reset) =
  let state = ref 0 in
  let counter () =
    let value = !state in
    let _ = state := value + 1 in
    value in
  let counter_reset () = state := 0 in
  (counter,counter_reset);;

let candle_parse_first_counter = candle_parse_counter();;
let candle_parse_second_counter = candle_parse_counter();;
let _ = candle_parse_counter_reset();;
let candle_parse_reset_counter = candle_parse_counter();;

let candle_parse_output = ref ([]:string list);;
module Candle_parse_initializers = struct
  let autogen = ref ([]:int list);;
  let _ = autogen := [1;2];;
  let macros = ref [0];;
  let _ = macros := [3;4];;
  let _ = candle_parse_output := "sphere_math"::!candle_parse_output;;
end;;

let candle_parse_ineq_runtime_compatibility_ok =
  candle_parse_geteps [] = 0.0 &&
  candle_parse_geteps [Candle_parse_other] = 0.0 &&
  candle_parse_geteps
    [Candle_parse_eps 0.5; Candle_parse_other; Candle_parse_eps 9.0] = 9.0 &&
  candle_parse_acs [] = "(acos)" &&
  candle_parse_acs ["x"] = "(acos(x))" &&
  candle_parse_acs_outcome candle_parse_acs ["x";"y"] = Some "ocaml:acs" &&
  candle_parse_first_counter = 0 &&
  candle_parse_second_counter = 1 &&
  candle_parse_reset_counter = 0 &&
  !Candle_parse_initializers.autogen = [1;2] &&
  !Candle_parse_initializers.macros = [3;4] &&
  !candle_parse_output = ["sphere_math"];;
