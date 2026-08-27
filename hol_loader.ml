(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(*              Modern OCaml version of the HOL theorem prover               *)
(*                                                                           *)
(*                            John Harrison                                  *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2024                       *)
(*              (c) Copyright, Juneyoung Lee 2024                            *)
(* ========================================================================= *)

let hol_dir = ref "hol-light/";;

(* Candle's verified boot loader keeps the search path in
   [Cakeml.loadPath].  Expose the standard HOL Light name as the same reference
   so direct source workloads can extend it without maintaining a second,
   divergent path list. *)
let load_path = Cakeml.loadPath;;
