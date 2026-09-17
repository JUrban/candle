module Original = struct
  let table = Hashtbl.create 3
  let add (key : string) (value : int) = Hashtbl.add table key value
  let observe () =
    (Hashtbl.find table "alpha", Hashtbl.find table "beta",
     Hashtbl.length table)
end;;

module Annotated = struct
  let table : (string, int) Hashtbl.t = Hashtbl.create 3
  let add (key : string) (value : int) = Hashtbl.add table key value
  let observe () =
    (Hashtbl.find table "alpha", Hashtbl.find table "beta",
     Hashtbl.length table)
end;;

let () =
  Original.add "alpha" 11;
  Original.add "beta" 17;
  Annotated.add "alpha" 11;
  Annotated.add "beta" 17;
  if Original.observe () = (11,17,2) &&
     Annotated.observe () = Original.observe () then
    print_endline "LP_HASHTBL_ANNOTATION_OCAML_ORACLE_OK"
  else
    failwith "LP hash-table annotation changed native behavior";;
