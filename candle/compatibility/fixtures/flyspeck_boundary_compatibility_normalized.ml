let candle_flyspeck_setify_terms terms =
  setify Term.(<) terms;;

let candle_flyspeck_setify_named_terms named_terms =
  setify
    (fun x y -> Pair.compare String.compare Term.compare x y <= 0)
    named_terms;;

let candle_flyspeck_update_all update n initial =
  let state = ref initial in
  let rec update_all i =
    if i = n then ()
    else (state := update i !state; update_all (i + 1)) in
  update_all 0;
  !state;;

let candle_flyspeck_hash_of_string s =
  let prime200 = 1223 in
  let prime = 8831 in
  let rec hashll values =
    match values with
    | [] -> 0
    | h::t ->
        (Char.code (String.get h 0) + prime200 * hashll t) mod prime in
  hashll (explode s);;

let candle_flyspeck_structure_effects = ref ([]:int list);;
module Candle_flyspeck_structure_effects = struct
  let emit value =
    candle_flyspeck_structure_effects :=
      value::!candle_flyspeck_structure_effects;;
  let _ = emit 1;;
  let _ = emit 2;;
end;;

let candle_flyspeck_boundary_compatibility_oracle_ok =
  let aty = mk_vartype "A" in
  let x = mk_var("x",aty) in
  let y = mk_var("y",aty) in
  let z = mk_var("z",aty) in
  candle_flyspeck_setify_terms [z;x;y;x] = [x;y;z] &&
  candle_flyspeck_setify_named_terms
    [("z",x);("a",y);("a",x);("a",y)] =
    [("a",x);("a",y);("z",x)] &&
  candle_flyspeck_update_all (fun i state -> i::state) 0 [] = [] &&
  candle_flyspeck_update_all (fun i state -> i::state) 4 [] = [3;2;1;0] &&
  map Char.code ['\000';'A';'z';'\255'] = [0;65;122;255] &&
  candle_flyspeck_hash_of_string "abc" = 4111 &&
  !candle_flyspeck_structure_effects = [2;1];;
