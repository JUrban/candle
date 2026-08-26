(* Export the exact compute initialization theorems from candle/compute.ml.
   Run this from a proof-recording HOL Light checkout after loading
   ProofTrace/pft.ml. *)

let candle_dir =
  try Sys.getenv "CANDLE_DIR"
  with Not_found -> failwith "CANDLE_DIR is not set";;

let output =
  try Sys.getenv "CANDLE_PFT_OUTPUT"
  with Not_found -> failwith "CANDLE_PFT_OUTPUT is not set";;

(* The ordinary HOL Light producer has no verified compute primitive.  The
   source theory only needs the module name while defining its public wrapper;
   fixture generation never calls this placeholder. *)
module Kernel = struct
  let compute _ _ = failwith "compute is only available in Candle"
end;;

loadt (candle_dir ^ "/candle/compute.ml");;

let compute_basis_targets =
  List.mapi
    (fun index theorem ->
       (Printf.sprintf "candle$COMPUTE_EQ_%02d" index, theorem))
    COMPUTE_INIT_THMS;;

let compute_basis_export = dump_pft output compute_basis_targets;;
Printf.printf
  "COMPUTE_BASIS_OK equations=%d commands=%d limits=(%d,%d,%d)\n%!"
  (List.length COMPUTE_INIT_THMS)
  compute_basis_export.export_commands
  compute_basis_export.export_type_count
  compute_basis_export.export_term_count
  compute_basis_export.export_theorem_count;;
