(* Native data-shape/timing diagnostic for Flyspeck LP certificate shards.
   It does not execute the HOL verifier and must not be used as proof evidence. *)

type constraint_type = string * int list * int64 list;;

type terminal_case = {
  precision : int;
  infeasible : bool;
  constraints : constraint_type list;
  target_variables : constraint_type list;
  variable_bounds : constraint_type list;
};;

type split_case = {
  split_type : string;
  split_face : int list;
};;

type lp_certificate_case =
  | Lp_terminal of terminal_case
  | Lp_split of split_case * lp_certificate_case list;;

type lp_certificate = {
  hypermap_string : string;
  root_case : lp_certificate_case;
};;

type candle_lp_detail = {
  detail_terminals : int;
  detail_constraint_rows : int;
  detail_target_rows : int;
  detail_bound_rows : int;
  detail_constraint_coefficients : int;
  detail_target_coefficients : int;
  detail_bound_coefficients : int;
  detail_negative_coefficients : int;
  detail_zero_coefficients : int;
  detail_max_coefficient_decimal_digits : int;
  detail_total_coefficient_decimal_digits : int;
  detail_index_coefficient_length_mismatches : int;
  detail_max_row_coefficients : int;
  detail_infeasible_terminals : int;
  detail_min_precision : int;
  detail_max_precision : int;
};;

let candle_lp_empty_detail = {
  detail_terminals = 0;
  detail_constraint_rows = 0;
  detail_target_rows = 0;
  detail_bound_rows = 0;
  detail_constraint_coefficients = 0;
  detail_target_coefficients = 0;
  detail_bound_coefficients = 0;
  detail_negative_coefficients = 0;
  detail_zero_coefficients = 0;
  detail_max_coefficient_decimal_digits = 0;
  detail_total_coefficient_decimal_digits = 0;
  detail_index_coefficient_length_mismatches = 0;
  detail_max_row_coefficients = 0;
  detail_infeasible_terminals = 0;
  detail_min_precision = max_int;
  detail_max_precision = min_int;
};;

let candle_lp_combine_detail left right = {
  detail_terminals = left.detail_terminals + right.detail_terminals;
  detail_constraint_rows =
    left.detail_constraint_rows + right.detail_constraint_rows;
  detail_target_rows = left.detail_target_rows + right.detail_target_rows;
  detail_bound_rows = left.detail_bound_rows + right.detail_bound_rows;
  detail_constraint_coefficients =
    left.detail_constraint_coefficients + right.detail_constraint_coefficients;
  detail_target_coefficients =
    left.detail_target_coefficients + right.detail_target_coefficients;
  detail_bound_coefficients =
    left.detail_bound_coefficients + right.detail_bound_coefficients;
  detail_negative_coefficients =
    left.detail_negative_coefficients + right.detail_negative_coefficients;
  detail_zero_coefficients =
    left.detail_zero_coefficients + right.detail_zero_coefficients;
  detail_max_coefficient_decimal_digits =
    max left.detail_max_coefficient_decimal_digits
      right.detail_max_coefficient_decimal_digits;
  detail_total_coefficient_decimal_digits =
    left.detail_total_coefficient_decimal_digits +
    right.detail_total_coefficient_decimal_digits;
  detail_index_coefficient_length_mismatches =
    left.detail_index_coefficient_length_mismatches +
    right.detail_index_coefficient_length_mismatches;
  detail_max_row_coefficients =
    max left.detail_max_row_coefficients right.detail_max_row_coefficients;
  detail_infeasible_terminals =
    left.detail_infeasible_terminals + right.detail_infeasible_terminals;
  detail_min_precision =
    min left.detail_min_precision right.detail_min_precision;
  detail_max_precision =
    max left.detail_max_precision right.detail_max_precision;
};;

let candle_lp_coefficient_stats rows =
  List.fold_left
    (fun (count, negative, zero, max_digits, total_digits, mismatches, max_row)
         (_, indices, coefficients) ->
       let row_count, row_negative, row_zero, row_max_digits, row_total_digits =
         List.fold_left
         (fun (count, negative, zero, max_digits, total_digits) coefficient ->
            let rendered = Int64.to_string coefficient in
            let digits =
              String.length rendered -
              (if rendered.[0] = '-' then 1 else 0) in
            (count + 1,
             negative + (if Int64.compare coefficient 0L < 0 then 1 else 0),
             zero + (if coefficient = 0L then 1 else 0),
             max max_digits digits, total_digits + digits))
         (0, 0, 0, 0, 0) coefficients in
       (count + row_count, negative + row_negative, zero + row_zero,
        max max_digits row_max_digits,
        total_digits + row_total_digits,
        mismatches +
          (if List.length indices = List.length coefficients then 0 else 1),
        max max_row row_count))
    (0, 0, 0, 0, 0, 0, 0) rows;;

let rec candle_lp_detail = function
  | Lp_terminal terminal ->
      let constraint_coefficients, constraint_negative, constraint_zero,
          constraint_digits, constraint_total_digits, constraint_mismatches,
          constraint_max_row =
        candle_lp_coefficient_stats terminal.constraints in
      let target_coefficients, target_negative, target_zero, target_digits,
          target_total_digits, target_mismatches, target_max_row =
        candle_lp_coefficient_stats terminal.target_variables in
      let bound_coefficients, bound_negative, bound_zero, bound_digits,
          bound_total_digits, bound_mismatches, bound_max_row =
        candle_lp_coefficient_stats terminal.variable_bounds in
      {
        detail_terminals = 1;
        detail_constraint_rows = List.length terminal.constraints;
        detail_target_rows = List.length terminal.target_variables;
        detail_bound_rows = List.length terminal.variable_bounds;
        detail_constraint_coefficients = constraint_coefficients;
        detail_target_coefficients = target_coefficients;
        detail_bound_coefficients = bound_coefficients;
        detail_negative_coefficients =
          constraint_negative + target_negative + bound_negative;
        detail_zero_coefficients =
          constraint_zero + target_zero + bound_zero;
        detail_max_coefficient_decimal_digits =
          max constraint_digits (max target_digits bound_digits);
        detail_total_coefficient_decimal_digits =
          constraint_total_digits + target_total_digits + bound_total_digits;
        detail_index_coefficient_length_mismatches =
          constraint_mismatches + target_mismatches + bound_mismatches;
        detail_max_row_coefficients =
          max constraint_max_row (max target_max_row bound_max_row);
        detail_infeasible_terminals = if terminal.infeasible then 1 else 0;
        detail_min_precision = terminal.precision;
        detail_max_precision = terminal.precision;
      }
  | Lp_split (_, children) ->
      List.fold_left
        (fun detail child ->
           candle_lp_combine_detail detail (candle_lp_detail child))
        candle_lp_empty_detail children;;

let rec candle_lp_terminals = function
  | Lp_terminal terminal -> [terminal]
  | Lp_split (_, children) ->
      List.flatten (List.map candle_lp_terminals children);;

let rec candle_lp_shape depth = function
  | Lp_terminal terminal ->
      let constraints =
        List.length terminal.constraints +
        List.length terminal.target_variables +
        List.length terminal.variable_bounds in
      (1, 0, constraints, depth, constraints)
  | Lp_split (_, children) ->
      List.fold_left
        (fun (terminals, splits, constraints, max_depth, max_terminal)
             child ->
           let ct, cs, cc, cd, cm = candle_lp_shape (depth + 1) child in
           (terminals + ct, splits + cs, constraints + cc,
            max max_depth cd, max max_terminal cm))
        (0, 1, 0, depth, 0) children;;

let candle_decode path =
  let channel = open_in_bin path in
  let certificates = (Marshal.from_channel channel : lp_certificate list) in
  close_in channel;
  certificates;;

let candle_profile_file repetitions path =
  let started = Unix.gettimeofday () in
  let last = ref [] in
  for _ = 1 to repetitions do
    last := candle_decode path
  done;
  let elapsed = Unix.gettimeofday () -. started in
  let totals =
    List.fold_left
      (fun (tt, ts, tc, td, tm) certificate ->
         let t, s, c, d, m = candle_lp_shape 0 certificate.root_case in
         (tt + t, ts + s, tc + c, max td d, max tm m))
      (0, 0, 0, 0, 0) !last in
  let terminals, splits, constraints, max_depth, max_terminal = totals in
  Printf.printf
    "LP_CERT_PROFILE file=%S repetitions=%d decode_seconds=%.9f certificates=%d terminals=%d splits=%d constraints=%d max_depth=%d max_terminal_constraints=%d\n"
    path repetitions elapsed (List.length !last) terminals splits constraints
    max_depth max_terminal;
  let detail =
    List.fold_left
      (fun total certificate ->
         candle_lp_combine_detail total
           (candle_lp_detail certificate.root_case))
      candle_lp_empty_detail !last in
  Printf.printf
    "LP_CERT_DETAIL file=%S terminals=%d constraint_rows=%d target_rows=%d bound_rows=%d constraint_coefficients=%d target_coefficients=%d bound_coefficients=%d negative_coefficients=%d zero_coefficients=%d max_coefficient_decimal_digits=%d total_coefficient_decimal_digits=%d index_coefficient_length_mismatches=%d max_row_coefficients=%d infeasible_terminals=%d min_precision=%d max_precision=%d\n"
    path detail.detail_terminals detail.detail_constraint_rows
    detail.detail_target_rows detail.detail_bound_rows
    detail.detail_constraint_coefficients detail.detail_target_coefficients
    detail.detail_bound_coefficients detail.detail_negative_coefficients
    detail.detail_zero_coefficients
    detail.detail_max_coefficient_decimal_digits
    detail.detail_total_coefficient_decimal_digits
    detail.detail_index_coefficient_length_mismatches
    detail.detail_max_row_coefficients
    detail.detail_infeasible_terminals detail.detail_min_precision
    detail.detail_max_precision;
  let terminal_index = ref 0 in
  List.iter
    (fun certificate ->
       List.iter
         (fun terminal ->
            terminal_index := !terminal_index + 1;
            let terminal_detail =
              candle_lp_detail (Lp_terminal terminal) in
            Printf.printf
              "LP_CERT_TERMINAL file=%S index=%d constraint_rows=%d target_rows=%d bound_rows=%d coefficient_entries=%d coefficient_decimal_digits=%d max_row_coefficients=%d precision=%d infeasible=%b\n"
              path !terminal_index terminal_detail.detail_constraint_rows
              terminal_detail.detail_target_rows terminal_detail.detail_bound_rows
              (terminal_detail.detail_constraint_coefficients +
               terminal_detail.detail_target_coefficients +
               terminal_detail.detail_bound_coefficients)
              terminal_detail.detail_total_coefficient_decimal_digits
              terminal_detail.detail_max_row_coefficients terminal.precision
              terminal.infeasible)
         (candle_lp_terminals certificate.root_case))
    !last;;

let () =
  if Array.length Sys.argv < 3 then
    failwith "usage: ocaml unix.cma lp_certificate_shape_profile.ml REPETITIONS FILE..."
  else
    let repetitions = int_of_string Sys.argv.(1) in
    for i = 2 to Array.length Sys.argv - 1 do
      candle_profile_file repetitions Sys.argv.(i)
    done;;
