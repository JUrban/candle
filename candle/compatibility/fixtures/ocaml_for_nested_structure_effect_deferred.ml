(* Deferred frontend reproducer.  A bare [for] loop is a standalone structure
   expression inside the constrained module.  Native OCaml retains [values]
   in scope; the current compiled Candle frontend must not be credited unless
   it does the same. *)
module type Candle_for_nested_structure_effect_signature = sig
  val result : int list
end;;

module Candle_for_nested_structure_effect
  : Candle_for_nested_structure_effect_signature = struct
  let values : int list ref = ref [];;
  for i = 0 to 2 do
    values := i :: !values
  done;;
  let result = List.rev !values;;
end;;

let candle_for_nested_structure_effect_expected =
  Candle_for_nested_structure_effect.result = [0;1;2];;
