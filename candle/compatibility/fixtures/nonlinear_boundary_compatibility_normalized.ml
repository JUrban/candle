let rec candle_nonlinear_range first last =
  if first > last then []
  else first::candle_nonlinear_range (first + 1) last;;

let rec candle_nonlinear_do_list operation = function
  | [] -> ()
  | head::tail ->
      operation head;
      candle_nonlinear_do_list operation tail;;

let candle_nonlinear_rev values =
  let rec reverse accumulator = function
    | [] -> accumulator
    | head::tail -> reverse (head::accumulator) tail in
  reverse [] values;;

let rec candle_nonlinear_length = function
  | [] -> 0
  | _::tail -> 1 + candle_nonlinear_length tail;;

let candle_nonlinear_f4_order () =
  let visits = ref [] in
  candle_nonlinear_do_list
    (fun i3 ->
      candle_nonlinear_do_list
        (fun i4 ->
          candle_nonlinear_do_list
            (fun i5 ->
              candle_nonlinear_do_list
                (fun i6 -> visits := (i3,i4,i5,i6)::!visits)
                (candle_nonlinear_range 0 1))
            (candle_nonlinear_range 0 1))
        (candle_nonlinear_range 0 1))
    (candle_nonlinear_range 0 1);
  candle_nonlinear_rev !visits;;

let candle_nonlinear_hex_order () =
  let visits = ref [] in
  candle_nonlinear_do_list
    (fun i1 ->
      candle_nonlinear_do_list
        (fun i2 ->
          candle_nonlinear_do_list
            (fun i3 -> visits := (i1,i2,i3)::!visits)
            (candle_nonlinear_range i2 4))
        (candle_nonlinear_range i1 4))
    (candle_nonlinear_range 0 4);
  candle_nonlinear_rev !visits;;

let candle_nonlinear_f4_id i3 i4 i5 i6 =
  "ZTGIJCF4 " ^ string_of_int i3 ^ " " ^ string_of_int i4 ^
  " " ^ string_of_int i5 ^ " " ^ string_of_int i6 ^ " 1821661595";;

let candle_nonlinear_hex_id i234 i126 i135 =
  "7550003505 " ^ string_of_int i234 ^ " " ^
  string_of_int i126 ^ " " ^ string_of_int i135;;

let (candle_nonlinear_counter,candle_nonlinear_counter_reset) =
  let state = ref 0 in
  let counter () =
    let value = !state in
    state := value + 1;
    value in
  let counter_reset () = state := 0 in
  (counter,counter_reset);;

let candle_nonlinear_first_counter = candle_nonlinear_counter();;
let candle_nonlinear_second_counter = candle_nonlinear_counter();;
candle_nonlinear_counter_reset();;
let candle_nonlinear_reset_counter = candle_nonlinear_counter();;

type candle_nonlinear_structure_datum = {
  candle_nonlinear_structure_id : string;
  candle_nonlinear_structure_enabled : bool
};;

let candle_nonlinear_structure_trace = ref ([]:string list);;
let candle_nonlinear_structure_emit name =
  candle_nonlinear_structure_trace :=
    name::!candle_nonlinear_structure_trace;;

module Candle_nonlinear_structure_effects = struct
  let _ = candle_nonlinear_structure_emit "first";;
  let _ = candle_nonlinear_structure_emit "second";;
  let _ = {
    candle_nonlinear_structure_id = "discarded";
    candle_nonlinear_structure_enabled = false
  };;
end;;

let candle_nonlinear_boundary_compatibility_ok =
  candle_nonlinear_length (candle_nonlinear_f4_order()) = 16 &&
  candle_nonlinear_length (candle_nonlinear_hex_order()) = 35 &&
  candle_nonlinear_f4_id 0 1 1 0 =
    "ZTGIJCF4 0 1 1 0 1821661595" &&
  candle_nonlinear_hex_id 0 2 4 = "7550003505 0 2 4" &&
  candle_nonlinear_first_counter = 0 &&
  candle_nonlinear_second_counter = 1 &&
  candle_nonlinear_reset_counter = 0 &&
  !candle_nonlinear_structure_trace = ["second";"first"];;
