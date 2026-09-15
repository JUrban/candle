let loop_trace = ref [];;
let loop_push value = loop_trace := value :: !loop_trace;;
let loop_bound label value = loop_push label; value;;

for i = loop_bound "ascending-first" 0 to loop_bound "ascending-last" 2 do
  loop_push (string_of_int i)
done;;

for i = loop_bound "descending-first" 2 downto loop_bound "descending-last" 0 do
  loop_push (string_of_int i)
done;;

for i = loop_bound "empty-up-first" 1 to loop_bound "empty-up-last" 0 do
  loop_push ("unexpected-up-" ^ string_of_int i)
done;;

for i = loop_bound "empty-down-first" 0 downto loop_bound "empty-down-last" 1 do
  loop_push ("unexpected-down-" ^ string_of_int i)
done;;

let loop_shadowed_operators =
  let (+) _ _ = failwith "for used shadowed +" and
      (-) _ _ = failwith "for used shadowed -" and
      (=) _ _ = failwith "for used shadowed =" and
      (<) _ _ = failwith "for used shadowed <" and
      (>) _ _ = failwith "for used shadowed >" in
  let values = ref [] in
  for i = 0 to 2 do values := i :: !values done;
  for i = 2 downto 0 do values := i :: !values done;
  List.rev !values;;

let loop_endpoint_up = ref [];;
for i = max_int to max_int do loop_endpoint_up := i :: !loop_endpoint_up done;;

let loop_min_int = -max_int - 1;;
let loop_endpoint_down = ref [];;
for i = loop_min_int downto loop_min_int do
  loop_endpoint_down := i :: !loop_endpoint_down
done;;

let loop_exception_trace = ref [];;
let loop_exception_caught =
  try
    for i = 0 to 4 do
      loop_exception_trace := i :: !loop_exception_trace;
      if i = 2 then failwith "for-stop" else ()
    done;
    false
  with Failure "for-stop" -> true | _ -> false;;

module Loop_structure_effects = struct
  let effects = ref [];;
  effects := "effect" :: !effects;;
  7;;
  true;;
  let result = List.rev !effects;;
end;;

let candle_ocaml_for_structure_effects_ok =
  List.rev !loop_trace =
    ["ascending-first"; "ascending-last"; "0"; "1"; "2";
     "descending-first"; "descending-last"; "2"; "1"; "0";
     "empty-up-first"; "empty-up-last";
     "empty-down-first"; "empty-down-last"] &&
  loop_shadowed_operators = [0;1;2;2;1;0] &&
  !loop_endpoint_up = [max_int] &&
  !loop_endpoint_down = [loop_min_int] &&
  loop_exception_caught &&
  List.rev !loop_exception_trace = [0;1;2] &&
  Loop_structure_effects.result = ["effect"];;

let _ =
  if candle_ocaml_for_structure_effects_ok then
    print_endline "CANDLE_OCAML_FOR_STRUCTURE_EFFECTS_OK"
  else
    failwith "OCaml for/structure-effect semantics mismatch";;
