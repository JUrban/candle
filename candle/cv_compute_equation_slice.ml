(* ========================================================================== *)
(* Host-side reachability slicing for Candle compute-equation bundles.        *)
(*                                                                            *)
(* The slice is only a performance preparation step.  Kernel.compute still   *)
(* checks every retained characteristic theorem, rejects missing constants,  *)
(* executes the concrete call, and returns the sole authoritative theorem.    *)
(* ========================================================================== *)

module Candle_cv_compute_equation_slice = struct

let candle_cv_compute_equation_head theorem =
  let lhs,_ = dest_eq (concl (SPEC_ALL theorem)) in
  let operator,_ = strip_comb lhs in
  let name,_ = dest_const operator in
  name;;

let candle_cv_compute_term_constant_names term =
  rev
    (itlist
      (fun constant names ->
        let name,_ = dest_const constant in
        if List.mem name names then names else name :: names)
      (find_terms is_const term) []);;

let candle_cv_compute_equation_slice equations term =
  let named =
    map
      (fun theorem ->
        let specialized = SPEC_ALL theorem in
        let _,rhs = dest_eq (concl specialized) in
        candle_cv_compute_equation_head specialized,theorem,rhs)
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
                (candle_cv_compute_term_constant_names rhs) result
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
    dependencies [] (candle_cv_compute_term_constant_names term) in
  let selected_names = close roots [] in
  let selected =
    List.filter
      (fun theorem ->
        List.mem
          (candle_cv_compute_equation_head theorem)
          selected_names)
      equations in
  if length selected > length equations then
    failwith "compute equation slice: cardinality increased";
  selected;;

let candle_cv_compute_sliced equations term =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_compute_equation_slice equations term)
    term;;

print_endline "CANDLE_CV_COMPUTE_EQUATION_SLICE_OK DEVELOPMENT_NON_RELEASE";;

end;;
