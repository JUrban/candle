(* Native diagnostic for the authenticated nonlinear reconstruction tree.
   Load after break_case_type.hl and break_case_log.hl.  This does not prove a
   theorem and must not be used as Flyspeck evidence. *)

let rec candle_iarg_shape depth = function
  | Iarg_leaf milliseconds ->
      (1, 0, 0, depth, milliseconds)
  | Iarg_facet (_, _, milliseconds, child) ->
      let leaves, bisects, facets, max_depth, logged_ms =
        candle_iarg_shape (depth + 1) child in
      (leaves, bisects, facets + 1, max_depth,
       logged_ms + milliseconds)
  | Iarg_bisect (_, left, right) ->
      let ll, lb, lf, ld, lm = candle_iarg_shape (depth + 1) left in
      let rl, rb, rf, rd, rm = candle_iarg_shape (depth + 1) right in
      (ll + rl, lb + rb + 1, lf + rf, max ld rd, lm + rm);;

let candle_iarg_rows =
  List.map
    (fun (name, tree) -> name, candle_iarg_shape 0 tree)
    !(Break_case_log.break_data);;

let candle_iarg_totals =
  List.fold_left
    (fun (leaves, bisects, facets, max_depth, logged_ms)
         (_, (l, b, f, d, m)) ->
       (leaves + l, bisects + b, facets + f, max max_depth d,
        logged_ms + m))
    (0, 0, 0, 0, 0) candle_iarg_rows;;

let candle_iarg_compare (_, (l1, _, _, _, _)) (_, (l2, _, _, _, _)) =
  compare l2 l1;;

let candle_iarg_sorted = List.sort candle_iarg_compare candle_iarg_rows;;

let leaves, bisects, facets, max_depth, logged_ms = candle_iarg_totals;;
Printf.printf
  "NONLINEAR_IARG_TOTAL cases=%d leaves=%d bisects=%d facets=%d subdomains=%d max_depth=%d logged_milliseconds=%d\n"
  (List.length candle_iarg_rows) leaves bisects facets (leaves + facets)
  max_depth logged_ms;;

let rec candle_print_top rank = function
  | _ when rank > 10 -> ()
  | [] -> ()
  | (name, (l, b, f, d, m)) :: rest ->
      Printf.printf
        "NONLINEAR_IARG_TOP rank=%d leaves=%d bisects=%d facets=%d depth=%d logged_milliseconds=%d id=%S\n"
        rank l b f d m name;
      candle_print_top (rank + 1) rest;;

candle_print_top 1 candle_iarg_sorted;;
