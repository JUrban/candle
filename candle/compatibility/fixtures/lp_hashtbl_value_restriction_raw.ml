(* DEVELOPMENT preflight: Candle is expected to reject this unconstrained
   top-level allocation at the declaration boundary. *)
module Candle_lp_hashtbl = struct
  type ('a, 'b) t = Table of (('a * 'b) list ref);;
  let create _ = Table (ref []);;
end;;

let candle_lp_unannotated_table = Candle_lp_hashtbl.create 3;;
