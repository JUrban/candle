(* Explicitly state the type later forced by the table's uses. *)
module Candle_lp_hashtbl = struct
  type ('a, 'b) t = Table of (('a * 'b) list ref);;

  let create _ = Table (ref []);;

  let add (Table entries) key value =
    entries := (key,value) :: !entries;;
end;;

let candle_lp_annotated_table : (string, int) Candle_lp_hashtbl.t =
  Candle_lp_hashtbl.create 3;;

let _ = Candle_lp_hashtbl.add candle_lp_annotated_table "alpha" 11;;
let _ = Candle_lp_hashtbl.add candle_lp_annotated_table "beta" 17;;

let candle_lp_annotated_observation =
  match candle_lp_annotated_table with
    Candle_lp_hashtbl.Table entries -> !entries;;
