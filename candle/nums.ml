(*
  This module attempts to provide a compatibility interface for the
  OCaml num library, which HOL Light uses.
 *)

module type NUM = sig

  val num_of_int : int -> num
  val num_of_string : string -> num
  val int_of_num : num -> int
  val string_of_num : num -> string
  val float_of_num : num -> double

  val denominator : num -> num
  val numerator : num -> num

  val abs_num : num -> num
  val floor_num : num -> num
  val round_num : num -> num
  val ceiling_num : num -> num

  val ( +/ ) : num -> num -> num
  val ( -/ ) : num -> num -> num
  val ( */ ) : num -> num -> num
  val ( // ) : num -> num -> num

  val add_num : num -> num -> num
  val sub_num : num -> num -> num
  val mul_num : num -> num -> num
  val div_num : num -> num -> num
  val minus_num : num -> num

  (* These operations are for integers (unit denominator) *)

  val quo_num : num -> num -> num
  val mod_num : num -> num -> num

  val ( </ ): num -> num -> bool
  val ( >/ ) : num -> num -> bool
  val ( <=/ ) : num -> num -> bool
  val ( >=/ ) : num -> num -> bool
  val ( =/ ) : num -> num -> bool
  val ( <>/ ) : num -> num -> bool
  val le_num : num -> num -> bool
  val lt_num : num -> num -> bool
  val ge_num : num -> num -> bool
  val gt_num : num -> num -> bool
  val eq_num : num -> num -> bool

  val min_num : num -> num -> num
  val max_num : num -> num -> num
  val compare : num -> num -> int
  val gcd_num : num -> num -> num

  val ( **/) : num -> num -> num
  val power_num : num -> num -> num

  val is_integer_num : num -> bool;;

end;;

(* OCaml's legacy [Big_int.big_int] is an arbitrary-precision integer.  CakeML
   integers already have that representation, so the selected Flyspeck
   conversion, arithmetic, comparison, division, power, and square-root
   operations need no truncating machine-word conversion or FFI. *)
module Big_int = struct
  type big_int = int

  let zero_big_int = 0

  let big_int_of_string s =
    match Cake.Int.fromString s with
    | None -> failwith "Big_int.big_int_of_string"
    | Some i -> i

  let big_int_of_int value = value

  let sign_big_int value =
    if value < 0 then ~-1 else if value > 0 then 1 else 0

  let abs_big_int value = abs value

  let add_big_int left right = left + right

  let succ_big_int value = value + 1

  let sub_big_int left right = left - right

  let pred_big_int value = value - 1

  let mult_big_int left right = left * right

  let mult_int_big_int left right = left * right

  let quomod_big_int dividend divisor =
    let quotient = dividend / divisor and remainder = dividend mod divisor in
    if remainder < 0 then quotient + 1, remainder - divisor
    else quotient, remainder

  let div_big_int dividend divisor =
    fst (quomod_big_int dividend divisor)

  let mod_big_int dividend divisor =
    snd (quomod_big_int dividend divisor)

  let power_int_positive_int base exponent =
    if exponent < 0 then failwith "Big_int.power_int_positive_int" else
    let rec power accumulator factor remaining =
      if remaining = 0 then accumulator
      else
        let square = factor * factor in
        if remaining mod 2 = 0 then
          power accumulator square (remaining / 2)
        else
          power (accumulator * factor) square (remaining / 2) in
    power 1 base exponent

  let eq_big_int left right = left = right

  let le_big_int left right = left <= right

  let lt_big_int left right = left < right

  (* [Big_int.sqrt_big_int] is floor square root on nonnegative arbitrary
     precision integers.  CakeML integers are already arbitrary precision, so
     Newton descent gives the same exact result without a representation
     conversion or floating-point approximation. *)
  let sqrt_big_int value =
    if value < 0 then failwith "Big_int.sqrt_big_int"
    else if value < 2 then value
    else
      let rec descend estimate =
        let next = (estimate + value / estimate) / 2 in
        if next >= estimate then estimate else descend next in
      descend value
end;;

type num =
  | Int of int
  | Rat of Cake.Rat.rat
;;

let pp_num n =
  match n with
  | Int i -> pp_int i
  | Rat r -> pp_rat r
;;

(* CANDLE_NUM_BIG_INT_BRIDGE_BEGIN *)
let num_of_big_int i = Int i
;;

let big_int_of_num n =
  match n with
  | Int i -> i
  | Rat r ->
      if Cake.Rat.denominator r = 1 then Cake.Rat.numerator r
      else failwith "big_int_of_ratio"
;;

let pred_num n =
  match n with
  | Int i -> Int (i - 1)
  | Rat r ->
      let result = Cake.Rat.(-) r (Cake.Rat.fromInt 1) in
      if Cake.Rat.denominator result = 1 then
        Int (Cake.Rat.numerator result)
      else Rat result
;;

let compare_num x y =
  let compare_rat left right =
    if Cake.Rat.(<) left right then -1
    else if Cake.Rat.(>) left right then 1
    else 0 in
  match x, y with
  | Int i, Int j -> if i < j then -1 else if i > j then 1 else 0
  | Int i, Rat r -> compare_rat (Cake.Rat.fromInt i) r
  | Rat r, Int j -> compare_rat r (Cake.Rat.fromInt j)
  | Rat i, Rat j -> compare_rat i j
;;

let approx_num_exp precision value =
  if precision <= 0 then failwith "approx_ratio_exp" else
  let numerator,denominator =
    match value with
    | Int i -> i,1
    | Rat r -> Cake.Rat.numerator r,Cake.Rat.denominator r in
  let negative = numerator < 0 in
  let numerator = abs numerator in
  let rec power accumulator factor exponent =
    if exponent = 0 then accumulator
    else
      let square = factor * factor in
      if exponent mod 2 = 0 then
        power accumulator square (exponent / 2)
      else
        power (accumulator * factor) square (exponent / 2) in
  let power10 exponent = power 1 10 exponent in
  let rec zeroes count result =
    if count <= 0 then result else zeroes (count - 1) ("0" ^ result) in
  let sign = if negative then "-" else "+" in
  if numerator = 0 then sign ^ "0." ^ zeroes precision "" ^ "e0"
  else
    let numerator_digits = Cake.String.size (string_of_int numerator) and
        denominator_digits = Cake.String.size (string_of_int denominator) in
    let candidate = numerator_digits - denominator_digits in
    let below_candidate_power =
      if candidate >= 0 then
        numerator < denominator * power10 candidate
      else
        numerator * power10 (~-candidate) < denominator in
    let exponent = if below_candidate_power then candidate else candidate + 1 in
    let shift = precision - exponent in
    let scaled_numerator,scaled_denominator =
      if shift >= 0 then numerator * power10 shift,denominator
      else numerator,denominator * power10 (~-shift) in
    let quotient = scaled_numerator / scaled_denominator and
        remainder = scaled_numerator mod scaled_denominator in
    let rounded =
      if 2 * remainder >= scaled_denominator then quotient + 1
      else quotient in
    let unit = power10 precision in
    let integer_part = rounded / unit and fraction = rounded mod unit in
    let fraction_string = string_of_int fraction in
    let fraction_string =
      zeroes (precision - Cake.String.size fraction_string) fraction_string in
    sign ^ string_of_int integer_part ^ "." ^ fraction_string ^
      "e" ^ string_of_int exponent
;;
(* CANDLE_NUM_BIG_INT_BRIDGE_END *)

module Num (* : NUM*) = struct

type num = num;;

let denominator n =
  match n with
  | Int i -> Int 1
  | Rat r -> Int (Cake.Rat.denominator r)
;;

let numerator n =
  match n with
  | Int i -> n
  | Rat r -> Int (Cake.Rat.numerator r)
;;

let num_fix n =
  match n with
  | Int i -> n
  | Rat r ->
      if Cake.Rat.denominator r = 1 then
        Int (Cake.Rat.numerator r)
      else if Cake.Rat.denominator r = 0 then
        failwith "num_fix: division by zero"
      else n
;;

let abs_num n =
  match n with
  | Int i -> Int (abs i)
  | Rat r -> Rat (Cake.Rat.(/) (Cake.Rat.fromInt (abs (Cake.Rat.numerator r)))
                          (Cake.Rat.fromInt (Cake.Rat.denominator r)))
;;

let sign_num n =
  let sign i = if i < 0 then ~-1 else if i > 0 then 1 else 0 in
  match n with
  | Int i -> sign i
  | Rat r -> sign (Cake.Rat.numerator r)
;;

(* The Rat type operations normalize results *)
let norm n = num_fix n
;;

let num_of_int i = Int i
;;

let num_of_big_int = num_of_big_int
;;

let big_int_of_num = big_int_of_num
;;

let pred_num = pred_num
;;

let compare_num = compare_num
;;

let approx_num_exp = approx_num_exp
;;

(* The Num compatibility operation accepts integer strings.  CakeML integers
   are unbounded, so the existing parser preserves the selected decimal SOS
   behavior without an FFI conversion. *)
let num_of_string s =
  if s = "" then Int 0 else
  if Cake.String.sub s 0 = '~' then failwith "num_of_string" else
    match Cake.Int.fromString s with
    | None -> failwith "num_of_string"
    | Some i -> Int i
;;

let int_of_num n =
  match n with
  | Int i -> i
  | Rat r -> Cake.Rat.numerator r / Cake.Rat.denominator r
;;

let string_of_num n =
  match n with
  | Int i -> string_of_int i
  | Rat r ->
      let n = Cake.Rat.numerator r in
      let d = Cake.Rat.denominator r in
      string_of_int n ^ "/" ^ string_of_int d
;;

(* Convert an arbitrary-precision rational directly to its nearest IEEE-754
   binary64 value.  [Cake.Double.fromInt] communicates through a word64 and
   therefore cannot be applied separately to an unbounded numerator and
   denominator: doing so truncates the large rational seeds used by
   Flyspeck's interval calculator. *)
let float_of_num n =
  let rec int_power base exponent =
    if exponent = 0 then 1 else
    let half = int_power base (exponent / 2) in
    let square = half * half in
    if exponent mod 2 = 0 then square else base * square in
  let power_two exponent = int_power 2 exponent in
  let rec bit_length value length =
    if value = 0 then length else bit_length (value / 2) (length + 1) in
  let round_quotient numerator denominator =
    let quotient = numerator / denominator in
    let remainder = numerator mod denominator in
    let twice_remainder = 2 * remainder in
    if twice_remainder > denominator ||
       (twice_remainder = denominator && quotient mod 2 = 1)
    then quotient + 1
    else quotient in
  let construct sign exponent significand =
    Cake.Double.construct
      (Cake.Word64.fromInt sign)
      (Cake.Word64.fromInt exponent)
      (Cake.Word64.fromInt significand) in
  let of_ratio numerator denominator =
    let sign = if numerator < 0 then 1 else 0 in
    let magnitude = abs numerator in
    if magnitude = 0 then construct sign 0 0 else
    let candidate =
      bit_length magnitude 0 - bit_length denominator 0 in
    let exponent =
      if candidate >= 0 then
        if magnitude < denominator * power_two candidate
        then candidate - 1 else candidate
      else
        if magnitude * power_two (~-candidate) < denominator
        then candidate - 1 else candidate in
    if exponent > 1023 then construct sign 2047 0
    else if exponent < ~-1022 then
      let significand =
        round_quotient (magnitude * power_two 1074) denominator in
      if significand = 0 then construct sign 0 0
      else if significand >= power_two 52 then construct sign 1 0
      else construct sign 0 significand
    else
      let shift = 52 - exponent in
      let scaled_numerator =
        if shift >= 0 then magnitude * power_two shift else magnitude in
      let scaled_denominator =
        if shift >= 0 then denominator
        else denominator * power_two (~-shift) in
      let significand =
        round_quotient scaled_numerator scaled_denominator in
      let carry = significand >= power_two 53 in
      let exponent = if carry then exponent + 1 else exponent in
      let significand = if carry then significand / 2 else significand in
      if exponent > 1023 then construct sign 2047 0
      else construct sign (exponent + 1023)
             (significand - power_two 52) in
  match n with
  | Int i -> of_ratio i 1
  | Rat r -> of_ratio (Cake.Rat.numerator r) (Cake.Rat.denominator r)
;;

let minus_num n =
  match n with
  | Int i -> Int (~-i)
  | Rat r -> Rat (rat_minus r)
;;

let (+/) x y =
  match x, y with
  | Int i, Int j -> Int (i + j)
  | Int i, Rat r -> Rat (Cake.Rat.(+) (Cake.Rat.fromInt i) r)
  | Rat r, Int i -> Rat (Cake.Rat.(+) r (Cake.Rat.fromInt i))
  | Rat i, Rat j -> Rat (Cake.Rat.(+) i j)
;;
let (+/) x y = num_fix (x +/ y);;
let add_num = (+/);;

let (-/) x y =
  match x, y with
  | Int i, Int j -> Int (i - j)
  | Int i, Rat r -> Rat (Cake.Rat.(-) (Cake.Rat.fromInt i) r)
  | Rat r, Int i -> Rat (Cake.Rat.(-) r (Cake.Rat.fromInt i))
  | Rat i, Rat j -> Rat (Cake.Rat.(-) i j)
;;
let (-/) x y = num_fix (x -/ y);;
let sub_num = (-/);;

let ( */) x y =
  match x, y with
  | Int i, Int j -> Int (i * j)
  | Int i, Rat r -> Rat (Cake.Rat.( * ) (Cake.Rat.fromInt i) r)
  | Rat r, Int i -> Rat (Cake.Rat.( * ) r (Cake.Rat.fromInt i))
  | Rat i, Rat j -> Rat (Cake.Rat.( * ) i j)
;;
let ( */) x y = num_fix (x */ y);;
let mul_num = ( */);;

let (//) x y =
  match x, y with
  | Int i, Int j -> Rat (Cake.Rat.(/) (Cake.Rat.fromInt i) (Cake.Rat.fromInt j))
  | Int i, Rat r -> Rat (Cake.Rat.(/) (Cake.Rat.fromInt i) r)
  | Rat r, Int i -> Rat (Cake.Rat.(/) r (Cake.Rat.fromInt i))
  | Rat i, Rat j -> Rat (Cake.Rat.(/) i j)
;;
let (//) x y = num_fix (x // y);;
let div_num = (//);;

let quo_num x y =
  match x, y with
  | Int i, Int j ->
      let q = i / j in
      let r = i mod j in
      Int (if r >= 0 then q else if j > 0 then q - 1 else q + 1)
  | Int _, Rat _ ->
      let y = abs_num y in
      Int (int_of_num (x // y))
  | _ ->
      Int (int_of_num (x // y))
;;

let is_integer_num n =
  match n with
  | Int _ -> true
  | _ -> false;;

let mod_num x y =
  match x, y with
  | Int i, Int j ->
      let r = i mod j in
      Int (if r >= 0 then r else if j > 0 then r + j else r - j)
  | _ -> x -/ (y */ quo_num x y)
;;

let power_num b e =
  let rec pow b e =
    if e < 1 then
      Int 1
    else if e mod 2 <> 0 then b */ pow b (e - 1)
    else let p = pow b (e / 2) in
           p */ p in
  let exponent = int_of_num e in
  if exponent >= 0 then pow b exponent
  else (Int 1) // pow b (~-exponent)
;;

let ( **/) = power_num;;

let floor_num n =
  match n with
  | Int i -> n
  | Rat r -> Int (Cake.Rat.floor r)
;;

(* Num.round_num rounds a half away from zero.  Expressing the rule through
   the verified Rat floor/ceiling operations also handles negative rationals
   without relying on the host language's integer-division convention. *)
let round_num =
  let zero = Cake.Rat.fromInt 0 in
  let half = Cake.Rat.(/) (Cake.Rat.fromInt 1) (Cake.Rat.fromInt 2) in
  fun n ->
    match n with
    | Int _ -> n
    | Rat r ->
        if Cake.Rat.(>=) r zero then
          Int (Cake.Rat.floor (Cake.Rat.(+) r half))
        else
          Int (Cake.Rat.ceiling (Cake.Rat.(-) r half))
;;

let ceiling_num n =
  match n with
  | Int _ -> n
  | Rat r -> Int (Cake.Rat.ceiling r)
;;

let compare x y =
  let rat_compare x y =
    if Cake.Rat.(<) x y then -1 else if Cake.Rat.(>) x y then 1 else 0 in
  match x, y with
  | Int i, Int j -> if i < j then -1 else if i > j then 1 else 0
  | Int i, Rat r -> rat_compare (Cake.Rat.fromInt i) r
  | Rat r, Int j -> rat_compare r (Cake.Rat.fromInt j)
  | Rat i, Rat j -> rat_compare i j
;;

let ( </) x y = compare x y < 0;;
let ( <=/) x y = compare x y <= 0;;
let ( >/) x y = compare x y > 0;;
let ( >=/) x y = compare x y >= 0;;
let ( =/) x y = compare x y = 0;;
let ( <>/) x y = compare x y <> 0;;

let lt_num = ( </);;
let le_num = ( <=/);;
let gt_num = ( >/);;
let ge_num = ( >=/);;
let eq_num = ( =/);;

let min_num x y = if x <=/ y then x else y;;
let max_num x y = if x >=/ y then x else y;;
let gcd_num x y =
  match x, y with
  | Int i, Int j -> Int (abs (Cake.Int.gcd i j))
;;

let succ_num n = Int 1 +/ n;;

end;; (* struct *)

(* There's no 'open': *)

let num_of_int = Num.num_of_int;;
let num_of_big_int = Num.num_of_big_int;;
let big_int_of_num = Num.big_int_of_num;;
let pred_num = Num.pred_num;;
let compare_num = Num.compare_num;;
let approx_num_exp = Num.approx_num_exp;;
let int_of_num = Num.int_of_num;;
let string_of_num = Num.string_of_num;;
let float_of_num = Num.float_of_num;;
let denominator = Num.denominator;;
let numerator = Num.numerator;;
let minus_num = Num.minus_num;;
let abs_num = Num.abs_num;;
let floor_num = Num.floor_num;;
let round_num = Num.round_num;;
let ceiling_num = Num.ceiling_num;;

let ( +/ ) = Num.( +/);;
let ( -/ ) = Num.( -/);;
let ( */ ) = Num.( */);;
let ( // ) = Num.( //);;

let add_num = Num.add_num ;;
let sub_num = Num.sub_num ;;
let mul_num = Num.mul_num ;;
let div_num = Num.div_num ;;

(* These operations are for integers (unit denominator) *)

let quo_num = Num.quo_num;;
let mod_num = Num.mod_num;;

let ( </ ) = Num.( </);;
let ( >/ ) = Num.( >/);;
let ( <=/ ) = Num.( <=/);;
let ( >=/ ) = Num.( >=/);;
let ( =/ ) = Num.( =/);;
let ( <>/ ) = Num.( <>/);;

let lt_num = Num.lt_num;;
let le_num = Num.le_num;;
let gt_num = Num.gt_num;;
let ge_num = Num.ge_num;;
let eq_num = Num.eq_num;;

let min_num = Num.min_num;;
let max_num = Num.max_num;;
let compare = Num.compare;;
let gcd_num = Num.gcd_num;;

let ( **/) = Num.( **/);;
let power_num = Num.power_num;;

let is_integer_num = Num.is_integer_num;;

let succ_num = Num.succ_num;;
