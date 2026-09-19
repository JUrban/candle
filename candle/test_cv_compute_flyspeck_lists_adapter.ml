(* A minimal, independently clean fixture for the exact theorem interface used
   by Flyspeck's compute_all list_of_faces leaf.  The definitions and the
   existing conversion below have the same equations and theorem shape as
   formal_lp/hypermap/computations/list_hypermap_computations.hl, without
   requiring a cumulative Flyspeck replay merely to exercise this adapter. *)

needs "candle/compute.ml";;

let list_pairs2 = define
 `(list_pairs2 [] (hd:num) = []) /\
  (list_pairs2 [h] hd = [(h,hd)]) /\
  (list_pairs2 (CONS h1 (CONS h2 t)) hd =
     CONS (h1,h2) (list_pairs2 (CONS h2 t) hd))`;;

let list_pairs = new_definition
 `list_pairs (l:num list) = list_pairs2 l (HD l)`;;

let list_of_faces = new_definition
 `list_of_faces (l:(num list)list) = MAP list_pairs l`;;

let list_pairs_eq_list_pairs2 = prove
 (`!l:num list. list_pairs l = list_pairs2 l (HD l)`,
  REWRITE_TAC[list_pairs]);;

module List_hypermap_computations = struct

let hd_var_num = `hd:num` and
    h_var_num = `h:num` and
    h1_var_num = `h1:num` and
    h2_var_num = `h2:num` and
    t_var = `t:num list` and
    l_cap_var = `L:(num list)list`;;

let rule tm = prove(tm,REWRITE_TAC[list_pairs2]);;
let list_pairs2_0 = rule `list_pairs2 [] (hd:num) = []` and
    list_pairs2_1 = rule `list_pairs2 [h1] (hd:num) = [(h1,hd)]` and
    list_pairs2_2 = rule
      `list_pairs2 (CONS h1 (CONS h2 t)) (hd:num) =
         CONS (h1,h2) (list_pairs2 (CONS h2 t) hd)`;;

let rule tm = prove
  (tm,REWRITE_TAC[list_pairs_eq_list_pairs2; list_pairs2_0; HD]);;
let list_pairs_empty = rule `list_pairs ([]:num list) = []` and
    list_pairs_cons = rule
      `list_pairs (CONS (h:num) t) = list_pairs2 (CONS h t) h`;;

let list_pairs2_conv tm =
  let ltm,hd_tm = dest_comb tm in
  let rec list_pairs2_rec list_tm =
    if is_comb list_tm then
      let h_tm',t1_tm = dest_comb list_tm in
      let h1_tm = rand h_tm' in
      if is_comb t1_tm then
        let h_tm',t2_tm = dest_comb t1_tm in
        let h2_tm = rand h_tm' in
        let th0 = INST
          [h1_tm,h1_var_num; h2_tm,h2_var_num; t2_tm,t_var; hd_tm,hd_var_num]
          list_pairs2_2 in
        let ltm = rator (rand (concl th0)) in
        let th1 = list_pairs2_rec t1_tm in
        TRANS th0 (AP_TERM ltm th1)
      else
        INST[h1_tm,h1_var_num; hd_tm,hd_var_num] list_pairs2_1
    else
      INST[hd_tm,hd_var_num] list_pairs2_0 in
  list_pairs2_rec (rand ltm);;

let eval_list_pairs list_tm =
  if is_comb list_tm then
    let h_tm',t_tm = dest_comb list_tm in
    let h_tm = rand h_tm' in
    let th0 = INST[h_tm,h_var_num; t_tm,t_var] list_pairs_cons in
    let th1 = list_pairs2_conv (rand (concl th0)) in
    TRANS th0 th1
  else
    list_pairs_empty;;

let list_pairs_conv = eval_list_pairs o rand;;

let map_empty = prove
 (`MAP (f:num list->(num#num)list) [] = []`,REWRITE_TAC[MAP]) and
    map_cons = prove
 (`MAP (f:num list->(num#num)list) (CONS h t) =
     CONS (f h) (MAP f t)`,REWRITE_TAC[MAP]);;

let map_conv_univ f_conv tm =
  let ltm,list_tm = dest_comb tm in
  let f_tm = rand ltm in
  let f_var = `f:num list->(num#num)list` and
      h_var = `h:num list` and
      t_var = `t:(num list)list` in
  let rec map_conv_raw list_tm =
    if is_comb list_tm then
      let h_tm',t_tm = dest_comb list_tm in
      let h_tm = rand h_tm' in
      let th0 = INST[f_tm,f_var; h_tm,h_var; t_tm,t_var] map_cons in
      let ltm,rtm = dest_comb (rand (concl th0)) in
      let cons_tm,f_h_tm = dest_comb ltm in
      let f_h_th = f_conv f_h_tm in
      let map_t_th = map_conv_raw t_tm in
      TRANS th0 (MK_COMB (AP_TERM cons_tm f_h_th,map_t_th))
    else
      INST[f_tm,f_var] map_empty in
  map_conv_raw list_tm;;

let eval_list_of_faces =
  let eq_th = prove
   (`list_of_faces (L:(num list)list) = MAP list_pairs L`,
    REWRITE_TAC[list_of_faces]) in
  fun tm ->
    let th0 = INST[tm,l_cap_var] eq_th in
    let th1 = map_conv_univ list_pairs_conv (rand (concl th0)) in
    TRANS th0 th1;;

end;;

needs "candle/flyspeck_cv_compute.ml";;

open List_hypermap_computations;;
open Flyspeck_cv_compute;;

let candle_cv_adapter_input =
 `[[0;1;2;3;4;5];
   [0;5;6;7];
   [6;5;4];
   [6;4;8];
   [8;4;3];
   [8;3;9];
   [9;3;2];
   [9;2;10];
   [10;2;11];
   [11;2;1];
   [11;1;0];
   [11;0;7];
   [10;11;7];
   [10;7;12];
   [12;7;6];
   [12;6;8];
   [12;8;9];
   [9;10;12]]:(num list)list`;;

let candle_cv_existing_result = eval_list_of_faces candle_cv_adapter_input;;
let candle_cv_reflected_result =
  candle_cv_list_of_faces_conv candle_cv_adapter_input;;

if hyp candle_cv_reflected_result <> [] then
  failwith "reflected list_of_faces theorem has assumptions";;
if not (aconv (concl candle_cv_existing_result)
              (concl candle_cv_reflected_result)) then
  failwith "reflected list_of_faces theorem interface mismatch";;

let rec candle_cv_repeat n f x last =
  if n = 0 then last else candle_cv_repeat (n - 1) f x (f x);;

(* Candle deliberately makes Sys.time deterministic, so the companion Python
   controller measures wall time between the ready/done protocol markers. *)
print_endline "CANDLE_CV_FLYSPECK_LIST_ADAPTER_OK";;
print_endline "CANDLE_CV_FLYSPECK_LIST_BENCH_READY";;
