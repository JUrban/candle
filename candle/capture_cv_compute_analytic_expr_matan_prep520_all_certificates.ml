(* ========================================================================== *)
(* Capture current search trees for all four prep-5202826650 a components.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Search and emitted topology are untrusted     *)
(* preparation.  A production reflected checker must recheck every terminal  *)
(* numerical claim against the independently reconstructed direct source.    *)
(* ========================================================================== *)

open M_verifier_main;;
open Certificate;;
open Informal_taylor;;
open Informal_verifier;;

let source_id = "prep-5202826650 a";;
let pp = 6;;
let axioms_before = axioms ();;

let rec all2 predicate left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      predicate left_head right_head &&
      all2 predicate left_tail right_tail
  | _ -> false;;

let formula =
  `tau_residual_x x1 x2 x3 x4 x5 x6 * -- &1 < &0 \/
   delta_x x1 x2 x3 x4 x5 x6 < &0`;;

let variables = `[x1; x2; x3; x4; x5; x6]:real list`;;
let component_bounds =
 [`frac_right 3 #0.2547
    [#6.3504,#6.3504; #4.0,#6.3504; #4.0,#6.3504;
     #3.01 * #3.01,#3.915 * #3.915; #4.0,#4.0; #4.0,#4.0]`;
  `frac_left 1 #0.5000
    (frac_left 3 #0.2547
     [#6.3504,#6.3504; #4.0,#6.3504; #4.0,#6.3504;
      #3.01 * #3.01,#3.915 * #3.915; #4.0,#4.0; #4.0,#4.0])`;
  `frac_left 2 #0.5000
    (frac_right 1 #0.5000
     (frac_left 3 #0.2547
      [#6.3504,#6.3504; #4.0,#6.3504; #4.0,#6.3504;
       #3.01 * #3.01,#3.915 * #3.915; #4.0,#4.0; #4.0,#4.0]))`;
  `frac_right 2 #0.5000
    (frac_right 1 #0.5000
     (frac_left 3 #0.2547
      [#6.3504,#6.3504; #4.0,#6.3504; #4.0,#6.3504;
       #3.01 * #3.01,#3.915 * #3.915; #4.0,#4.0; #4.0,#4.0]))`];;

let components =
  map
    (fun bounds -> list_mk_comb (`ineqm`,[variables;bounds;formula]))
    component_bounds;;

let prepare_component component =
  let domain_expansion = Break_case.ineqm_conv component in
  let encoded_component = rand (concl domain_expansion) in
  let formula_expansion =
    (REWRITE_CONV
       [TAUT `(P ==> Q) <=> (~P \/ Q)`;
        REAL_ARITH `~(a > b:real) <=> a <= b`;
        REAL_ARITH `~(a < b:real) <=> b <= a`;
        REAL_ARITH `~(a >= b:real) <=> a < b`;
        REAL_ARITH `~(a <= b:real) <=> b < a`]
     THENC
     REWRITE_CONV
       ([Definitions.ineq; IMP_IMP; REAL_MUL_LZERO; REAL_MUL_RZERO] @
        Definitions.flyspeck_defs)
     THENC DEPTH_CONV let_CONV)
      encoded_component in
  let expanded_component = rand (concl formula_expansion) in
  let inequality,source_variable_names,source_bounds =
    M_verifier_main.dest_ineq expanded_component in
  let source_lower,source_upper = source_bounds in
  let standard =
    M_verifier_main.mk_standard_ineq [REAL_POW_1;real_pow] inequality in
  let normalized_relations =
    striplist dest_disj ((lhand o concl) standard) in
  let source_terms = map lhand normalized_relations in
  let function_terms,variable_vector =
    M_verifier_main.exprs_to_vector_fun source_terms in
  let ordered_variables = M_taylor.dest_vector variable_vector in
  let variable_names = map (fst o dest_var) ordered_variables in
  let named_bounds =
    zip source_variable_names
      (zip (dest_list source_lower) (dest_list source_upper)) in
  let ordered_bounds = map (fun name -> assoc name named_bounds) variable_names in
  let xx,zz = unzip ordered_bounds in
  let xx_tm,zz_tm = Misc_vars.mk_real_list xx,Misc_vars.mk_real_list zz in
  let xx_float = Informal_taylor.convert_to_float_list pp true xx_tm in
  let zz_float = Informal_taylor.convert_to_float_list pp false zz_tm in
  if length function_terms <> 2 || length source_terms <> 2 ||
     length normalized_relations <> 2 || length variable_names <> 6 ||
     hyp domain_expansion <> [] || hyp formula_expansion <> [] ||
     hyp standard <> [] then
    failwith "prep520 all capture: component preparation contract";
  function_terms,Informal_taylor.mk_m_center_domain pp xx_float zz_float;;

let prepared = map prepare_component components;;
let base_function_terms = fst (hd prepared);;

let build_numerical_function index function_term =
  let dimension = 6 in
  print_endline
    ("CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_FUNCTION_BEGIN" ^
     " DEVELOPMENT_NON_RELEASE index=" ^ string_of_int index);
  let _,taylor = M_verifier_main.mk_funs dimension pp function_term in
  let eval0 = Informal_taylor.mk_eval_function pp function_term in
  print_endline
    ("CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_FUNCTION_END" ^
     " DEVELOPMENT_NON_RELEASE index=" ^ string_of_int index);
  eval0,taylor;;

let numerical_function0 =
  build_numerical_function 0 (List.nth base_function_terms 0);;
let numerical_function1 =
  build_numerical_function 1 (List.nth base_function_terms 1);;
let numerical_functions = [numerical_function0;numerical_function1];;

let search_options =
  Candle_informal_search_options.make false 1e-10 200 pp 0;;

let exact_text value =
  Num.string_of_num (Informal_float.num_of_ifloat value);;

let bounds_text values = String.concat "," (map exact_text values);;

let historical_leaves = [403;339;189;404];;

let capture_component index (function_terms,root_domain) =
  if not
       (all2
         (fun expected actual -> aconv expected actual)
         base_function_terms function_terms) then
    failwith "prep520 all capture: source identity drift";
  print_endline
    ("CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_SEARCH_BEGIN" ^
     " DEVELOPMENT_NON_RELEASE component=" ^ string_of_int index ^
     " pp=" ^ string_of_int pp);
  let certificate =
    Informal_search.construct_certificate
      search_options root_domain numerical_functions in
  let stats = Certificate.result_stats certificate in
  print_endline
    ("CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_SEARCH_END" ^
     " DEVELOPMENT_NON_RELEASE component=" ^ string_of_int index ^
     " pass=" ^ string_of_int stats.pass ^
     " glue=" ^ string_of_int stats.glue ^
     " mono=" ^ string_of_int stats.mono ^
     " pass_raw=" ^ string_of_int stats.pass_raw ^
     " pass_mono=" ^ string_of_int stats.pass_mono ^
     " glue_convex=" ^ string_of_int stats.glue_convex ^
     " historical_legacy_pass=" ^
       string_of_int (List.nth historical_leaves index));
  let leaf_count = ref 0 in
  let branch0_count = ref 0 in
  let branch1_count = ref 0 in
  let rec emit_tree path domain tree =
    match tree with
    | Result_pass (branch,raw_flag) ->
        let lower,upper = domain.lo,domain.hi in
        let leaf = !leaf_count in
        let _ = leaf_count := leaf + 1 in
        let _ =
          if branch = 0 then branch0_count := !branch0_count + 1
          else if branch = 1 then branch1_count := !branch1_count + 1
          else failwith "prep520 all capture: unexpected branch index" in
        print_endline
          ("CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_LEAF" ^
           " DEVELOPMENT_NON_RELEASE component=" ^ string_of_int index ^
           " leaf=" ^ string_of_int leaf ^
           " branch=" ^ string_of_int branch ^
           " raw=" ^ (if raw_flag then "true" else "false") ^
           " path=" ^ String.concat "." (rev path) ^
           " lower=" ^ bounds_text lower ^
           " upper=" ^ bounds_text upper)
    | Result_glue (axis0,convex_flag,left,right) ->
        if convex_flag then
          failwith "prep520 all capture: unexpected convex glue";
        let axis = axis0 + 1 in
        let left_domain,right_domain =
          Informal_search.split_domain pp axis domain in
        emit_tree (("L" ^ string_of_int axis) :: path) left_domain left;
        emit_tree (("R" ^ string_of_int axis) :: path) right_domain right
    | Result_mono _ -> failwith "prep520 all capture: unexpected mono node"
    | Result_pass_mono _ ->
        failwith "prep520 all capture: unexpected mono pass"
    | Result_pass_ref _ ->
        failwith "prep520 all capture: unexpected reference"
    | Result_false _ -> failwith "prep520 all capture: false leaf" in
  emit_tree [] root_domain certificate;
  if !leaf_count <> stats.pass || stats.glue <> stats.pass - 1 ||
     !branch0_count + !branch1_count <> !leaf_count ||
     stats.mono <> 0 || stats.pass_raw <> 0 || stats.pass_mono <> 0 ||
     stats.glue_convex <> 0 then
    failwith "prep520 all capture: tree contract mismatch";
  print_endline
    ("CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_COMPONENT_RESULT" ^
     " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
     " component=" ^ string_of_int index ^
     " leaves=" ^ string_of_int !leaf_count ^
     " branch0=" ^ string_of_int !branch0_count ^
     " branch1=" ^ string_of_int !branch1_count ^
     " glue=" ^ string_of_int stats.glue ^
     " historical_legacy_leaves=" ^
       string_of_int (List.nth historical_leaves index) ^
     " current_leaf_delta=" ^
       string_of_int (!leaf_count - List.nth historical_leaves index));
  !leaf_count,stats.glue;;

let results = map2 capture_component (0--3) prepared;;
let total_leaves = itlist (fun (leaves,_) total -> leaves + total) results 0;;
let total_glue = itlist (fun (_,glue) total -> glue + total) results 0;;

let axioms_after = axioms ();;
if length components <> 4 || length prepared <> 4 || length results <> 4 ||
   total_glue <> total_leaves - 4 ||
   length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "prep520 all capture: final contract mismatch";;

print_endline
  ("CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " components=4 leaves=" ^ string_of_int total_leaves ^
   " glue=" ^ string_of_int total_glue ^
   " historical_legacy_leaves=1335 assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_OK";;
