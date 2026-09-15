type thm = Thm of string;;

let cache_size = 3;;

let le_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and
    add_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and
    sub_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and
    sub_le_table : (string, thm * thm) Hashtbl.t = Hashtbl.create cache_size and
    mul_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and
    div_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size;;

let () =
  Hashtbl.add le_table "le" (Thm "le");
  Hashtbl.add add_table "add" (Thm "add");
  Hashtbl.add sub_table "sub" (Thm "sub");
  Hashtbl.add sub_le_table "sub_le" (Thm "sub", Thm "le");
  Hashtbl.add mul_table "mul" (Thm "mul");
  Hashtbl.add div_table "div" (Thm "div");;

let reset_cache () =
  Hashtbl.clear le_table;
  Hashtbl.clear add_table;
  Hashtbl.clear sub_table;
  Hashtbl.clear sub_le_table;
  Hashtbl.clear mul_table;
  Hashtbl.clear div_table;;

let suc_counter = ref 1 and pre_counter = ref (-2) and
    eq0_counter = ref 3 and gt0_counter = ref (-4) and
    lt_counter = ref 5 and even_counter = ref (-6) and odd_counter = ref 7 and
    le_counter = ref 8 and add_counter = ref (-9) and sub_counter = ref 10 and
    sub_le_counter = ref (-11) and mul_counter = ref 12 and
    div_counter = ref (-13);;

let original_stat_string () =
  let len = Hashtbl.length in
  let suc_pre_str = Printf.sprintf "suc = %d\npre = %d\n" !suc_counter !pre_counter in
  let cmp0_str = Printf.sprintf "eq0 = %d\ngt0 = %d\n" !eq0_counter !gt0_counter in
  let lt_str = Printf.sprintf "lt = %d\n" !lt_counter in
  let even_odd_str = Printf.sprintf "even = %d\nodd = %d\n" !even_counter !odd_counter in
  let le_str = Printf.sprintf "le = %d (le_hash = %d)\n" !le_counter (len le_table) in
  let add_str = Printf.sprintf "add = %d (add_hash = %d)\n" !add_counter (len add_table) in
  let sub_str = Printf.sprintf "sub = %d (sub_hash = %d)\n" !sub_counter (len sub_table) in
  let sub_le_str = Printf.sprintf "sub_le = %d (sub_le_hash = %d)\n" !sub_le_counter (len sub_le_table) in
  let mul_str = Printf.sprintf "mul = %d (mul_hash = %d)\n" !mul_counter (len mul_table) in
  let div_str = Printf.sprintf "div = %d (div_hash = %d)\n" !div_counter (len div_table) in
    suc_pre_str ^ cmp0_str ^ lt_str ^ even_odd_str ^
      le_str ^ add_str ^ sub_str ^ sub_le_str ^ mul_str ^ div_str;;

let normalized_stat_string () =
  let suc_pre_str = "suc = " ^ string_of_int !suc_counter ^
    "\npre = " ^ string_of_int !pre_counter ^ "\n" in
  let cmp0_str = "eq0 = " ^ string_of_int !eq0_counter ^
    "\ngt0 = " ^ string_of_int !gt0_counter ^ "\n" in
  let lt_str = "lt = " ^ string_of_int !lt_counter ^ "\n" in
  let even_odd_str = "even = " ^ string_of_int !even_counter ^
    "\nodd = " ^ string_of_int !odd_counter ^ "\n" in
  let le_str = "le = " ^ string_of_int !le_counter ^
    " (le_hash = " ^ string_of_int (Hashtbl.length le_table) ^ ")\n" in
  let add_str = "add = " ^ string_of_int !add_counter ^
    " (add_hash = " ^ string_of_int (Hashtbl.length add_table) ^ ")\n" in
  let sub_str = "sub = " ^ string_of_int !sub_counter ^
    " (sub_hash = " ^ string_of_int (Hashtbl.length sub_table) ^ ")\n" in
  let sub_le_str = "sub_le = " ^ string_of_int !sub_le_counter ^
    " (sub_le_hash = " ^ string_of_int (Hashtbl.length sub_le_table) ^ ")\n" in
  let mul_str = "mul = " ^ string_of_int !mul_counter ^
    " (mul_hash = " ^ string_of_int (Hashtbl.length mul_table) ^ ")\n" in
  let div_str = "div = " ^ string_of_int !div_counter ^
    " (div_hash = " ^ string_of_int (Hashtbl.length div_table) ^ ")\n" in
    suc_pre_str ^ cmp0_str ^ lt_str ^ even_odd_str ^
      le_str ^ add_str ^ sub_str ^ sub_le_str ^ mul_str ^ div_str;;

let () =
  let values_match =
     Hashtbl.find le_table "le" = Thm "le" &&
     Hashtbl.find add_table "add" = Thm "add" &&
     Hashtbl.find sub_table "sub" = Thm "sub" &&
     Hashtbl.find sub_le_table "sub_le" = (Thm "sub", Thm "le") &&
     Hashtbl.find mul_table "mul" = Thm "mul" &&
     Hashtbl.find div_table "div" = Thm "div" in
  let format_matches = original_stat_string () = normalized_stat_string () in
  reset_cache ();
  if values_match && format_matches &&
     Hashtbl.length le_table = 0 && Hashtbl.length add_table = 0 &&
     Hashtbl.length sub_table = 0 && Hashtbl.length sub_le_table = 0 &&
     Hashtbl.length mul_table = 0 && Hashtbl.length div_table = 0 then
    print_endline "ARITH_CACHE_HASHTBL_ANNOTATION_OCAML_ORACLE_OK"
  else failwith "arith_cache annotated theorem-table behavior mismatch";;
