type thm = Thm of string;;
type num = Num of int;;
type term = Term of string;;

let maximum = 3;;
let names_array = [|"D0"; "D1"; "D2"|];;
let def_array = [|Thm "d0"; Thm "d1"; Thm "d2"|];;
let def_basic_array = [|Thm "b0"; Thm "b1"; Thm "b2"|];;

let def_table : (string, thm) Hashtbl.t = Hashtbl.create maximum;;
let def_basic_table : (string, thm) Hashtbl.t = Hashtbl.create maximum;;
let mk_table : (num, term) Hashtbl.t = Hashtbl.create maximum;;
let dest_table_num : (string, num) Hashtbl.t = Hashtbl.create maximum;;
let th_add_table : (string, thm * bool) Hashtbl.t = Hashtbl.create maximum;;
let mul1_right_th_table : (string, bool * thm) Hashtbl.t =
  Hashtbl.create maximum;;

let () =
  for i = 0 to maximum - 1 do
    Hashtbl.add def_table names_array.(i) def_array.(i);
    Hashtbl.add def_basic_table names_array.(i) def_basic_array.(i)
  done;
  Hashtbl.add mk_table (Num 1) (Term "D1");
  Hashtbl.add dest_table_num "D1" (Num 1);
  Hashtbl.add th_add_table "D1D2" (Thm "add12", false);
  Hashtbl.add mul1_right_th_table "D1D2" (true, Thm "mul12");;

let () =
  if Hashtbl.find def_table "D1" = Thm "d1" &&
     Hashtbl.find def_basic_table "D2" = Thm "b2" &&
     Hashtbl.find mk_table (Num 1) = Term "D1" &&
     Hashtbl.find dest_table_num "D1" = Num 1 &&
     Hashtbl.find th_add_table "D1D2" = (Thm "add12", false) &&
     Hashtbl.find mul1_right_th_table "D1D2" = (true, Thm "mul12") then
    print_endline "ARITH_NUM_HASHTBL_ANNOTATION_OCAML_ORACLE_OK"
  else failwith "arith_num annotated theorem-table behavior mismatch";;
