(* ========================================================================== *)
(* Restore the ML [Num] module surface after the full Flyspeck namespace.     *)
(*                                                                            *)
(* The direct Flyspeck state retains the original [num] type, constructors,   *)
(* and unqualified arithmetic functions, but its later source namespace no    *)
(* longer exposes the module-qualified interface used by the reflected        *)
(* checker.  This is a pure ML alias layer: it creates no logical constants,  *)
(* theorems, axioms, or replacement numeric representation.                   *)
(* ========================================================================== *)

module Num = struct

type num = num;;

let num_of_int value = Int value;;

let int_of_num value =
  match value with
  | Int integer -> integer
  | Rat rational ->
      Cake.Rat.numerator rational / Cake.Rat.denominator rational;;

let float_of_num = float_of_num;;
let add_num = add_num;;
let sub_num = sub_num;;
let mul_num = mul_num;;
let div_num = div_num;;
let minus_num = minus_num;;
let power_num = power_num;;
let min_num = min_num;;
let max_num = max_num;;
let eq_num = eq_num;;
let lt_num = lt_num;;
let le_num = le_num;;

end;;

