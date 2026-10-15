(* ========================================================================== *)
(* Authenticated four-piece plan for genuine Flyspeck prep-5202826650 a.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This exposes the exact serialized Iarg       *)
(* partition and expanded disjunct sources before constructing reflected     *)
(* programs.  It performs no numerical acceptance check.                     *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_matan_genuine_root_prepare.ml";;

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_analytic_expr_matan_domain_probe;;

module Test_cv_compute_analytic_expr_matan_prep520_partition_plan = struct

let axioms_before = axioms ();;
let source_id = "prep-5202826650 a";;
let target = candle_nl_matan_target source_id;;
let partition = Break_case_exec.get_iarg source_id;;
let components = Break_case_exec.mk_case_list target partition;;

let exact_bound tm =
  let expanded = rand (concl (REWRITE_CONV candle_nl_matan_defs tm)) in
  let lo,hi = candle_nl_matan_interval_eval [] expanded in
  if not (Num.eq_num lo hi) then
    failwith "prep520 partition plan: inexact component bound";
  lo;;

let normalize_bounds tm =
  (REWRITE_CONV
    [Sphere.frac_left; Sphere.frac_right;
     Break_case_exec.bisect_left_frac; Break_case_exec.bisect_right_frac;
     Break_case_exec.subat_explicit; Hales_tactic.LET_THM;
     LAMBDA_PAIR; Basics.EL_EXPLICIT]
   THENC REAL_RAT_REDUCE_CONV) tm;;

let relation_source relation =
  let operator,arguments = strip_comb relation in
  let name =
    if aconv operator `(<):real->real->bool` then "lt"
    else if aconv operator `(<=):real->real->bool` then "le"
    else failwith "prep520 partition plan: unsupported relation operator" in
  match arguments with
  | [source;zero] when aconv zero `&0:real` -> name,source
  | _ ->
      failwith
        ("prep520 partition plan: unsupported relation " ^
         string_of_term relation);;

let component_plan index component =
  let operator,arguments = strip_comb component in
  if not (aconv operator `ineqm`) then
    failwith "prep520 partition plan: expected ineqm component";
  let variables_term,bounds_term,formula =
    match arguments with
    | [variables;bounds;formula] -> variables,bounds,formula
    | _ -> failwith "prep520 partition plan: component arity" in
  let variables = dest_list variables_term in
  let bounds_expansion = normalize_bounds bounds_term in
  let normalized_bounds = rand (concl bounds_expansion) in
  let bounds = map dest_pair (dest_list normalized_bounds) in
  let expansion = candle_nl_matan_expand_theorem formula in
  let expanded = rand (concl expansion) in
  let disjuncts = striplist dest_disj expanded in
  let relations = map relation_source disjuncts in
  let sources = map snd relations in
  let vector_functions,variable_vector =
    candle_direct_exprs_to_vector_fun sources in
  let ordered_variables = M_taylor.dest_vector variable_vector in
  let bound_for variable =
    let rec find variables bounds =
      match variables,bounds with
      | candidate :: remaining_variables,bound :: remaining_bounds ->
          if aconv variable candidate then bound
          else find remaining_variables remaining_bounds
      | [],[] -> failwith "prep520 partition plan: missing variable bound"
      | _ -> failwith "prep520 partition plan: variable/bound drift" in
    find variables bounds in
  let ordered_bounds = map bound_for ordered_variables in
  let lower = map (fun (lo,_) -> exact_bound lo) ordered_bounds in
  let upper = map (fun (_,hi) -> exact_bound hi) ordered_bounds in
  let bounds_text =
    String.concat ","
      (map2
        (fun lo hi -> Num.string_of_num lo ^ ":" ^ Num.string_of_num hi)
        lower upper) in
  let source_text = String.concat " || " (map string_of_term sources) in
  let matan_counts = map (length o candle_nl_matan_subterms) sources in
  let relation_names = String.concat "," (map fst relations) in
  let matan_text = String.concat "," (map string_of_int matan_counts) in
  if length variables <> 6 || length bounds <> 6 ||
     length ordered_variables <> 6 || length disjuncts <> 2 ||
     length vector_functions <> 2 || hyp bounds_expansion <> [] ||
     hyp expansion <> [] then
    failwith "prep520 partition plan: component contract mismatch";
  print_endline
    ("CANDLE_CV_MATAN_PREP520_PARTITION_COMPONENT" ^
     " DEVELOPMENT_NON_RELEASE index=" ^ string_of_int index ^
     " dimensions=6 disjuncts=2 relations=" ^ relation_names ^
     " matan=" ^ matan_text ^
     " bounds_md5=" ^ Digest.to_hex (Digest.string bounds_text) ^
     " source_md5=" ^ Digest.to_hex (Digest.string source_text) ^
     " assumptions=0");
  component,bounds_expansion,normalized_bounds,
  variables,ordered_variables,ordered_bounds,lower,upper,
  formula,expansion,expanded,sources,vector_functions;;

let plans = map2 component_plan (0--3) components;;

let axioms_after = axioms ();;
if length components <> 4 || length plans <> 4 ||
   length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "prep520 partition plan: final contract mismatch";;

print_endline
  ("CANDLE_CV_MATAN_PREP520_PARTITION_PLAN_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " components=4 disjuncts_per_component=2 assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_PREP520_PARTITION_PLAN_OK";;

end;;
