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
    max_depth max_terminal;;

let () =
  if Array.length Sys.argv < 3 then
    failwith "usage: ocaml unix.cma lp_certificate_shape_profile.ml REPETITIONS FILE..."
  else
    let repetitions = int_of_string Sys.argv.(1) in
    for i = 2 to Array.length Sys.argv - 1 do
      candle_profile_file repetitions Sys.argv.(i)
    done;;
