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

(* Preserve the standard HOL Light logical identity of loaded sources while
   Candle's manifest may select an authenticated physical normalization. *)
let loaded_files = Cakeml.loadedSourceIds;;

let hol_expand_directory s =
  if s = "$" || s = "$/" then !hol_dir
  else if s = "$$" then "$"
  else if String.size s <= 2 then s
  else if String.substring s 0 2 = "$$" then
    String.substring s 1 (String.size s - 1)
  else if String.substring s 0 2 = "$/" then
    Filename.concat (!hol_dir) (String.substring s 2 (String.size s - 2))
  else s;;

let file_on_path p s =
  if not (Filename.isRelative s) then s else
  let rec find_file = function
    | [] -> failwith ("No such manifest source: " ^ s)
    | d::ds ->
        let d' = hol_expand_directory d in
        let candidate = Filename.concat d' s in
        if isFile candidate then
          if d' = "." then
            failwith "Candle source resolution requires a manifest-rooted path"
          else candidate
        else find_file ds in
  find_file p;;
