(* Minimal source-level control for the deferred nested-module structure
   effect: bind the loop's unit result explicitly while retaining the native
   [for] semantics and body unchanged. *)
module type Candle_for_nested_structure_effect_wrapped_signature = sig
  val result : int list
end;;

module Candle_for_nested_structure_effect_wrapped
  : Candle_for_nested_structure_effect_wrapped_signature = struct
  let values : int list ref = ref [];;
  let _ = for i = 0 to 2 do
    values := i :: !values
  done;;
  let result = List.rev !values;;
end;;

let candle_for_nested_structure_effect_wrapped_expected =
  Candle_for_nested_structure_effect_wrapped.result = [0;1;2];;
