(* ========================================================================== *)
(* Exact one-cell call at the complete case-10173 checker boundary.           *)
(*                                                                            *)
(* This is a development fixture for the trusted fast-evaluator handoff.      *)
(* It deliberately uses the same complete wrapper and equation bundle as the  *)
(* 4,173-cell certificate, but restricts the raw jobs and postfix topology to  *)
(* the first genuine leaf.  Kernel.compute remains the authority for the      *)
(* captured equality.                                                         *)
(* ========================================================================== *)

module Benchmark_cv_compute_analytic_expr_case10173_registered_cell0_capture = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_case10173_registered_equation_head theorem =
  let lhs,_ = dest_eq (concl (SPEC_ALL theorem)) in
  let operator,_ = strip_comb lhs in
  fst (dest_const operator);;

let candle_case10173_registered_term_constant_names term =
  rev
    (itlist
      (fun constant names ->
        let name,_ = dest_const constant in
        if List.mem name names then names else name :: names)
      (find_terms is_const term) []);;

let candle_case10173_registered_equation_slice equations term =
  let named =
    map
      (fun theorem ->
        let specialized = SPEC_ALL theorem in
        let _,rhs = dest_eq (concl specialized) in
        candle_case10173_registered_equation_head specialized,theorem,rhs)
      equations in
  let names = map (fun (name,_,_) -> name) named in
  let rec dependencies result = function
    | [] -> rev result
    | name :: remaining ->
        if List.mem name names && not (List.mem name result) then
          dependencies (name :: result) remaining
        else dependencies result remaining in
  let equation_dependencies name =
    let rec collect result = function
      | [] -> result
      | (candidate,_,rhs) :: remaining ->
          let result' =
            if candidate = name then
              itlist
                (fun dependency selected ->
                  if List.mem dependency names &&
                     not (List.mem dependency selected)
                  then dependency :: selected
                  else selected)
                (candle_case10173_registered_term_constant_names rhs) result
            else result in
          collect result' remaining in
    collect [] named in
  let rec close pending selected =
    match pending with
    | [] -> selected
    | name :: remaining ->
        if List.mem name selected then close remaining selected
        else if List.mem name names then
          close
            (equation_dependencies name @ remaining)
            (name :: selected)
        else close remaining selected in
  let roots =
    dependencies [] (candle_case10173_registered_term_constant_names term) in
  let selected_names = close roots [] in
  List.filter
    (fun theorem ->
      List.mem
        (candle_case10173_registered_equation_head theorem)
        selected_names)
    equations;;

type candle_case10173_registered_cell0_capture = {
  case10173_registered_cell0_equations : thm list;
  case10173_registered_cell0_call : term;
  case10173_registered_cell0_theorem : thm;
};;

let candle_case10173_registered_cell0_capture_state :
    candle_case10173_registered_cell0_capture option ref = ref None;;

let _ =
  let complete = candle_case10173_complete_capture () in
  let first_job,_ =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 registered cell0 jobs"
      complete.case10173_complete_encoded_jobs in
  let encoded_jobs =
    candle_q_dim_stable_program_cval_pair first_job `Cexp_num 0` in
  let encoded_tokens =
    candle_q_dim_stable_program_cval_pair `Cexp_num 0` `Cexp_num 0` in
  let call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
       [complete.case10173_complete_prepared.program_representation_term;
        `Cexp_num 6`;encoded_tokens;encoded_jobs]) in
  let all_equations =
    candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs () in
  let equations =
    candle_case10173_registered_equation_slice all_equations call in
  let theorem = Kernel.compute (COMPUTE_INIT_THMS,equations) call in
  let numerical,topology =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 registered cell0 result" (rand (concl theorem)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 registered cell0 topology" topology in
  let remaining_jobs,final_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 registered cell0 payload" topology_payload in
  let _,stack_tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 registered cell0 stack" final_stack in
  if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) ||
     not (aconv numerical `Cexp_num 1`) ||
     not (aconv topology_success `Cexp_num 1`) ||
     not (aconv remaining_jobs `Cexp_num 0`) ||
     not (aconv stack_tail `Cexp_num 0`)
  then failwith "case10173 registered cell0: verdict mismatch";
  let captured = {
    case10173_registered_cell0_equations = equations;
    case10173_registered_cell0_call = call;
    case10173_registered_cell0_theorem = theorem;
  } in
  candle_case10173_registered_cell0_capture_state := Some captured;
  print_endline
    ("CANDLE_CV_CASE10173_REGISTERED_CELL0_OK DEVELOPMENT_NON_RELEASE" ^
     " equations=" ^ string_of_int (length equations) ^
     " assumptions=0 numerical=1 topology=1" ^
     " remaining_jobs=0 active_roots=1");;

let candle_case10173_registered_cell0_capture () =
  match !candle_case10173_registered_cell0_capture_state with
  | Some captured -> captured
  | None -> failwith "case10173 registered cell0: unavailable";;

end;;
