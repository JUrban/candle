(* ========================================================================== *)
(* Capture a current search tree for genuine prep-5202826650 a, component 2. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Certificate search is untrusted preparation.  *)
(* The emitted exact boxes, branch choices and split topology must later be   *)
(* consumed by the reflected checker and its general soundness theorem.       *)
(* This file deliberately performs no legacy formal theorem reconstruction.   *)
(* ========================================================================== *)

open M_verifier_main;;
open Certificate;;

open Informal_taylor;;
open Informal_verifier;;

let domain_bounds domain = domain.lo,domain.hi;;
let axioms_before = axioms ();;
let source_id = "prep-5202826650 a";;
let component_index = 2;;
let pp = 6;;

(* This is verbatim case 8450 from the authenticated Flyspeck [ineqs.txt].
   The resulting boxes remain untrusted data until the reflected checker
   proves them against the independently reconstructed direct source. *)
let component =
  `ineqm [x1; x2; x3; x4; x5; x6]
   (frac_left 2 #0.5000
    (frac_right 1 #0.5000
     (frac_left 3 #0.2547
      [#6.3504,#6.3504; #4.0,#6.3504; #4.0,#6.3504;
       #3.01 * #3.01,#3.915 * #3.915; #4.0,#4.0; #4.0,#4.0])))
   (tau_residual_x x1 x2 x3 x4 x5 x6 * -- &1 < &0 \/
    delta_x x1 x2 x3 x4 x5 x6 < &0)`;;

let domain_expansion = Break_case.ineqm_conv component;;
let encoded_component = rand (concl domain_expansion);;
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
    encoded_component;;
let expanded_component = rand (concl formula_expansion);;
let inequality,source_variable_names,source_bounds =
  M_verifier_main.dest_ineq expanded_component;;
let source_lower,source_upper = source_bounds;;
let standard =
  M_verifier_main.mk_standard_ineq [REAL_POW_1;real_pow] inequality;;
let normalized_relations =
  striplist dest_disj ((lhand o concl) standard);;
let source_terms = map lhand normalized_relations;;
let function_terms,variable_vector =
  M_verifier_main.exprs_to_vector_fun source_terms;;
let ordered_variables = M_taylor.dest_vector variable_vector;;
let variable_names = map (fst o dest_var) ordered_variables;;
let named_bounds =
  zip source_variable_names
    (zip (dest_list source_lower) (dest_list source_upper));;
let ordered_bounds = map (fun name -> assoc name named_bounds) variable_names;;
let xx,zz = unzip ordered_bounds;;
let xx_tm,zz_tm = Misc_vars.mk_real_list xx,Misc_vars.mk_real_list zz;;
let xx_float = Informal_taylor.convert_to_float_list pp true xx_tm;;
let zz_float = Informal_taylor.convert_to_float_list pp false zz_tm;;

let build_numerical_function index function_term =
  let dimension = 6 in
  let _ =
    print_endline
      ("CANDLE_CV_MATAN_PREP520_CAPTURE_FUNCTION_BEGIN" ^
       " DEVELOPMENT_NON_RELEASE index=" ^ string_of_int index) in
  let _,taylor = mk_funs dimension pp function_term in
  let eval0 = Informal_taylor.mk_eval_function pp function_term in
  let _ =
    print_endline
      ("CANDLE_CV_MATAN_PREP520_CAPTURE_FUNCTION_END" ^
       " DEVELOPMENT_NON_RELEASE index=" ^ string_of_int index) in
  eval0,taylor;;
let numerical_function0 =
  build_numerical_function 0 (List.nth function_terms 0);;
let numerical_function1 =
  build_numerical_function 1 (List.nth function_terms 1);;
let numerical_functions = [numerical_function0;numerical_function1];;
let root_domain = Informal_taylor.mk_m_center_domain pp xx_float zz_float;;
let search_options =
  Candle_informal_search_options.make false 1e-10 200 pp 0;;

print_endline
  ("CANDLE_CV_MATAN_PREP520_CAPTURE_SEARCH_BEGIN" ^
   " DEVELOPMENT_NON_RELEASE component=" ^ string_of_int component_index ^
   " pp=" ^ string_of_int pp);;
let certificate =
  Informal_search.construct_certificate
    search_options root_domain numerical_functions;;
let stats = Certificate.result_stats certificate;;
print_endline
  ("CANDLE_CV_MATAN_PREP520_CAPTURE_SEARCH_END" ^
   " DEVELOPMENT_NON_RELEASE component=" ^ string_of_int component_index ^
   " pass=" ^ string_of_int stats.pass ^
   " glue=" ^ string_of_int stats.glue ^
   " mono=" ^ string_of_int stats.mono ^
   " pass_raw=" ^ string_of_int stats.pass_raw ^
   " pass_mono=" ^ string_of_int stats.pass_mono ^
   " glue_convex=" ^ string_of_int stats.glue_convex ^
   " historical_legacy_pass=189 historical_legacy_glue=188");;

let exact_text value =
  Num.string_of_num (Informal_float.num_of_ifloat value);;

let bounds_text values = String.concat "," (map exact_text values);;

let leaf_count = ref 0;;
let branch0_count = ref 0;;
let branch1_count = ref 0;;

let rec emit_tree path domain tree =
  match tree with
  | Result_pass (branch,raw_flag) ->
      let lower,upper = domain_bounds domain in
      let index = !leaf_count in
      let _ = leaf_count := index + 1 in
      let _ =
        if branch = 0 then branch0_count := !branch0_count + 1
        else if branch = 1 then branch1_count := !branch1_count + 1
        else failwith "prep520 capture: unexpected branch index" in
      print_endline
        ("CANDLE_CV_MATAN_PREP520_CAPTURE_LEAF" ^
         " DEVELOPMENT_NON_RELEASE component=" ^ string_of_int component_index ^
         " leaf=" ^ string_of_int index ^
         " branch=" ^ string_of_int branch ^
         " raw=" ^ (if raw_flag then "true" else "false") ^
         " path=" ^ String.concat "." (rev path) ^
         " lower=" ^ bounds_text lower ^
         " upper=" ^ bounds_text upper)
  | Result_glue (axis0,convex_flag,left,right) ->
      if convex_flag then failwith "prep520 capture: unexpected convex glue";
      let axis = axis0 + 1 in
      let left_domain,right_domain =
        Informal_search.split_domain pp axis domain in
      emit_tree (("L" ^ string_of_int axis) :: path) left_domain left;
      emit_tree (("R" ^ string_of_int axis) :: path) right_domain right
  | Result_mono _ -> failwith "prep520 capture: unexpected mono node"
  | Result_pass_mono _ -> failwith "prep520 capture: unexpected mono pass"
  | Result_pass_ref _ -> failwith "prep520 capture: unexpected reference"
  | Result_false _ -> failwith "prep520 capture: false leaf";;

let _ = emit_tree [] root_domain certificate;;

let axioms_after = axioms ();;
if length function_terms <> 2 || length source_terms <> 2 ||
   length normalized_relations <> 2 || length variable_names <> 6 ||
   !leaf_count <> stats.pass ||
   !branch0_count + !branch1_count <> !leaf_count ||
   !branch0_count <> 183 || !branch1_count <> 0 ||
   stats.pass <> 183 || stats.glue <> 182 || stats.mono <> 0 ||
   stats.pass_raw <> 0 || stats.pass_mono <> 0 || stats.glue_convex <> 0 ||
   hyp domain_expansion <> [] || hyp formula_expansion <> [] ||
   hyp standard <> [] ||
   length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "prep520 capture: final contract mismatch";;

print_endline
  ("CANDLE_CV_MATAN_PREP520_COMPONENT2_CAPTURE_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " component=" ^ string_of_int component_index ^
   " leaves=" ^ string_of_int !leaf_count ^
   " branch0=" ^ string_of_int !branch0_count ^
   " branch1=" ^ string_of_int !branch1_count ^
   " glue=" ^ string_of_int stats.glue ^
   " historical_legacy_leaves=189 current_leaf_delta=-6" ^
   " assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_PREP520_COMPONENT2_CAPTURE_OK";;
