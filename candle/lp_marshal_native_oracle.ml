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

let input = open_in_bin Sys.argv.(1);;
let certificates = (Marshal.from_channel input : lp_certificate list);;
close_in input;;

let rec certificate_shape = function
  | Lp_terminal terminal ->
      (1, 0,
       List.length terminal.constraints +
       List.length terminal.target_variables +
       List.length terminal.variable_bounds)
  | Lp_split (_, children) ->
      List.fold_left
        (fun (terminals, splits, constraints) child ->
          let child_terminals, child_splits, child_constraints =
            certificate_shape child in
          (terminals + child_terminals,
           splits + child_splits,
           constraints + child_constraints))
        (0, 1, 0) children;;

match certificates with
| [] -> failwith "native LP Marshal oracle decoded an empty list"
| certificate::_ ->
    let terminals, splits, constraints = certificate_shape certificate.root_case in
    Printf.printf "LP_MARSHAL_SUMMARY %d %d %d %d %d\n"
      (List.length certificates) (String.length certificate.hypermap_string)
      terminals splits constraints;;
