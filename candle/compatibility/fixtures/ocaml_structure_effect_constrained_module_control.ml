(* Passing control. Native OCaml and the compiled Candle frontend both accept
   standalone effects between a module-type declaration and a constrained
   module declaration. This rules out the constraint syntax itself as the
   action-152 failure and leaves effects inside the large Arith_num module as
   the narrower compatibility class. *)
module type Candle_structure_effect_signature = sig
  val result : int
end;;

ignore 0;;
ignore 1;;

module Candle_structure_effect_constrained
  : Candle_structure_effect_signature = struct
  let result = 7;;
end;;

let candle_structure_effect_constrained_module_expected =
  Candle_structure_effect_constrained.result = 7;;
