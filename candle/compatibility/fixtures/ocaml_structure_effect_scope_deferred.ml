(* Deferred frontend reproducer. Native OCaml evaluates the effect and leaves
   [effects] in scope. The current compiled Candle frontend reports [effects]
   undefined at the standalone assignment. This file is evidence of an open
   compatibility defect, not a passing gate. *)
module Candle_structure_effect_scope = struct
  let effects : string list ref = ref [];;
  effects := "effect" :: !effects;;
  let result = List.rev !effects;;
end;;

let candle_structure_effect_scope_expected =
  Candle_structure_effect_scope.result = ["effect"];;
