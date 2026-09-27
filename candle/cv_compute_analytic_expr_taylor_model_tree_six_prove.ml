(* ========================================================================== *)
(* Concrete six-dimensional topology proofs for exact Taylor split trees.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is theorem-side infrastructure only: it  *)
(* proves that explicitly encoded rational child boxes form an exact split.  *)
(* It performs no numerical Taylor computation and weakens no checker guard. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree_prove.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;

module Candle_cv_analytic_expr_taylor_model_tree_six_prove = struct

open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_prove;;

let candle_q_dim_taylor_model_tree_lower_selector_six =
  `candle_q_box_lower_vector:
     (((num#num)#num)#((num#num)#num))list->real^6`;;

let candle_q_dim_taylor_model_tree_upper_selector_six =
  `candle_q_box_upper_vector:
     (((num#num)#num)#((num#num)#num))list->real^6`;;

let candle_q_dim_taylor_model_tree_index_facts_six =
  map
    (fun index ->
      index,
      prove
        (subst
          [mk_small_numeral index,`i:num`]
          `i IN 1..dimindex (:6)`,
         REWRITE_TAC[IN_NUMSEG;candle_q_dim_poly_jet_dim_six] THEN
         ARITH_TAC))
    [1;2;3;4;5;6];;

(* Prove the finite index elimination once over an abstract predicate.  In
   particular, do not run a rewriting tactic over the large rational box
   terms at every internal tree node. *)
let candle_q_dim_taylor_model_tree_non_split_cases_six =
  let predicate = `P:num->bool` in
  let at index = mk_comb (predicate,mk_small_numeral index) in
  let prove_cases split_index =
    let remaining =
      filter (fun index -> index <> split_index) [1;2;3;4;5;6] in
    let premise =
      end_itlist (fun left right -> mk_conj (left,right))
        (map at remaining) in
    let conclusion =
      subst
        [mk_small_numeral split_index,`split_index:num`]
        `!i. 1 <= i /\ i <= dimindex (:6) /\ ~(i = split_index)
             ==> P i` in
    let rec split_cases = function
      | [] -> ASM_ARITH_TAC
      | index :: indices ->
          ASM_CASES_TAC (mk_eq (`i:num`,mk_small_numeral index)) THENL
           [if index = split_index then ASM_ARITH_TAC
            else ASM_MESON_TAC[];
            split_cases indices] in
    split_index,
    prove
      (mk_forall (predicate,mk_imp (premise,conclusion)),
       GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
       REWRITE_TAC[candle_q_dim_poly_jet_dim_six] THEN
       STRIP_TAC THEN split_cases [1;2;3;4;5;6]) in
  map prove_cases [1;2;3;4;5;6];;

let candle_q_dim_taylor_model_tree_vector_equality_six
    left_selector left_boxes left_components
    right_selector right_boxes right_components =
  let left =
    candle_reflected_nl_selector_vector_identity
      left_selector left_boxes left_components and
      right =
        candle_reflected_nl_selector_vector_identity
          right_selector right_boxes right_components in
  if not (aconv (rand (concl left)) (rand (concl right))) then
    failwith "six-dimensional Taylor tree: unequal endpoint vectors";
  TRANS left (SYM right);;

let candle_q_dim_taylor_model_tree_component_equality_six
    left_selector left_boxes right_selector right_boxes index =
  let component selector boxes =
    let theorem =
      match fst (dest_const selector) with
      | "candle_q_box_lower_vector" ->
          candle_q_box_lower_vector_component
      | "candle_q_box_upper_vector" ->
          candle_q_box_upper_vector_component
      | _ -> failwith "six-dimensional Taylor tree: unknown box selector" in
    let implication =
      SPECL [boxes;mk_small_numeral index]
        (INST_TYPE [`:6`,`:N`] theorem) in
    let premise_theorem =
      try assoc index candle_q_dim_taylor_model_tree_index_facts_six
      with Failure _ ->
        failwith "six-dimensional Taylor tree: component index out of range" in
    let selected_component = MATCH_MP implication premise_theorem in
    let q_function,projected =
      dest_comb (rand (concl selected_component)) in
    let projection,selected = dest_comb projected in
    let select_with_index,boxes_term = dest_comb selected in
    let select_function,index_term = dest_comb select_with_index in
    let index_equality = NUM_REDUCE_CONV index_term in
    let selected_index_equality =
      MK_COMB
        (AP_TERM select_function index_equality,REFL boxes_term) in
    let selected_equality =
      TRANS selected_index_equality
        (EL_CONV (rand (concl selected_index_equality))) in
    let projected_equality0 = AP_TERM projection selected_equality in
    let projected_equality =
      TRANS projected_equality0
        (REWRITE_CONV[FST;SND] (rand (concl projected_equality0))) in
    TRANS selected_component (AP_TERM q_function projected_equality) in
  let left = component left_selector left_boxes and
      right = component right_selector right_boxes in
  if not (aconv (rand (concl left)) (rand (concl right))) then
    failwith
      ("six-dimensional Taylor tree: unequal endpoint components at " ^
       string_of_int index);
  TRANS left (SYM right);;

let candle_q_dim_taylor_model_tree_structural_vector_equality_six
    left_selector left_boxes right_selector right_boxes =
  let selector_list_theorem =
    match fst (dest_const left_selector),fst (dest_const right_selector) with
    | "candle_q_box_lower_vector","candle_q_box_lower_vector" ->
        candle_reflected_nl_lower_vector_list
    | "candle_q_box_upper_vector","candle_q_box_upper_vector" ->
        candle_reflected_nl_upper_vector_list
    | _ -> failwith "six-dimensional Taylor tree: incompatible selectors" in
  let identity selector boxes =
    let length_six =
      prove
        (mk_eq
          (mk_comb
            (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,boxes),
           `6`),
         REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) in
    let abstract_identity =
      MATCH_MP
        (SPEC boxes
          (REWRITE_RULE[candle_q_dim_poly_jet_dim_six]
            (INST_TYPE [`:6`,`:N`] selector_list_theorem)))
        length_six in
    let expanded_identity =
      PURE_REWRITE_RULE [FST;SND]
        (BETA_RULE (PURE_REWRITE_RULE [MAP] abstract_identity)) in
    if hyp expanded_identity <> [] ||
       not
         (aconv (lhand (concl expanded_identity))
           (mk_comb (selector,boxes))) then
      failwith "six-dimensional Taylor tree: encoded vector identity";
    expanded_identity in
  let left = identity left_selector left_boxes and
      right = identity right_selector right_boxes in
  if not (aconv (rand (concl left)) (rand (concl right))) then
    failwith
      ("six-dimensional Taylor tree: unequal encoded endpoint vectors: " ^
       string_of_term (rand (concl left)) ^ " <> " ^
       string_of_term (rand (concl right)));
  TRANS left (SYM right);;

let candle_q_dim_taylor_model_tree_length_six boxes =
  let length_evaluation =
    CONV_RULE (RAND_CONV NUM_REDUCE_CONV)
      (REWRITE_CONV[LENGTH]
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,boxes))) in
  if not
      (aconv (rand (concl length_evaluation))
        (rand (concl candle_q_dim_poly_jet_dim_six))) then
    failwith "six-dimensional Taylor tree: box length mismatch";
  TRANS length_evaluation (SYM candle_q_dim_poly_jet_dim_six);;

let candle_q_dim_taylor_model_tree_leaf_well_formed_six tree =
  let goal =
    list_mk_comb
      (`candle_q_dim_taylor_model_tree_well_formed:
          real^6->candle_q_dim_taylor_model_tree->bool`,
       [`ARB:real^6`;tree]) in
  let expansion =
    REWRITE_CONV [candle_q_dim_taylor_model_tree_well_formed_def] goal in
  let length_call,dimension = dest_eq (rand (concl expansion)) in
  let length_evaluation =
    CONV_RULE (RAND_CONV NUM_REDUCE_CONV)
      (REWRITE_CONV[LENGTH] length_call) in
  if not
      (aconv dimension (lhand (concl candle_q_dim_poly_jet_dim_six)) &&
       aconv (rand (concl length_evaluation))
         (rand (concl candle_q_dim_poly_jet_dim_six))) then
    failwith "six-dimensional Taylor tree: leaf dimension mismatch";
  let length_theorem =
    TRANS length_evaluation (SYM candle_q_dim_poly_jet_dim_six) in
  EQ_MP (SYM expansion) length_theorem;;

let candle_q_dim_taylor_model_tree_non_split_six
    split_index root_boxes left_boxes right_boxes =
  if split_index < 1 || split_index > 6 then
    failwith "six-dimensional Taylor tree: split index out of range";
  let component_facts =
    map
      (fun index ->
        let lower =
          candle_q_dim_taylor_model_tree_component_equality_six
            candle_q_dim_taylor_model_tree_lower_selector_six
            right_boxes
            candle_q_dim_taylor_model_tree_lower_selector_six
            root_boxes index and
            upper =
              candle_q_dim_taylor_model_tree_component_equality_six
                candle_q_dim_taylor_model_tree_upper_selector_six
                left_boxes
                candle_q_dim_taylor_model_tree_upper_selector_six
                root_boxes index in
        index,CONJ lower upper)
      (filter (fun index -> index <> split_index) [1;2;3;4;5;6]) in
  let right_variable =
    `right_boxes:(((num#num)#num)#((num#num)#num))list` and
      left_variable =
        `left_boxes:(((num#num)#num)#((num#num)#num))list` and
      root_variable =
        `root_boxes:(((num#num)#num)#((num#num)#num))list` and
      split_variable = `split_index:num` in
  let goal =
    subst
      [right_boxes,right_variable;
       left_boxes,left_variable;
       root_boxes,root_variable;
       mk_small_numeral split_index,split_variable]
      `!i. 1 <= i /\ i <= dimindex (:6) /\ ~(i = split_index)
           ==> (candle_q_box_lower_vector right_boxes:real^6)$i =
                 (candle_q_box_lower_vector root_boxes:real^6)$i /\
               (candle_q_box_upper_vector left_boxes:real^6)$i =
                 (candle_q_box_upper_vector root_boxes:real^6)$i` in
  let index,body = dest_forall goal in
  let _,claim = dest_imp body in
  let predicate = mk_abs (index,claim) in
  let elimination =
    BETA_RULE
      (SPEC predicate
        (assoc split_index
          candle_q_dim_taylor_model_tree_non_split_cases_six)) in
  let facts = end_itlist CONJ (map snd component_facts) in
  let elimination_premise,elimination_conclusion =
    dest_imp (concl elimination) in
  if not (aconv elimination_premise (concl facts)) then
    failwith "six-dimensional Taylor tree: non-split premise mismatch";
  if not (aconv elimination_conclusion goal) then
    failwith "six-dimensional Taylor tree: non-split conclusion mismatch";
  MATCH_MP elimination facts;;

let candle_q_dim_taylor_model_tree_node_well_formed_six
    split_index
    root_boxes root_lower root_upper
    left_tree left_boxes left_lower left_upper left_well_formed
    right_tree right_boxes right_lower right_upper right_well_formed =
  if split_index < 1 || split_index > 6 then
    failwith "six-dimensional Taylor tree: split index out of range";
  let tree =
    candle_q_dim_taylor_model_tree_node_term
      (mk_small_numeral split_index) root_boxes left_tree right_tree in
  let root_left_lower =
    candle_q_dim_taylor_model_tree_structural_vector_equality_six
      candle_q_dim_taylor_model_tree_lower_selector_six
      root_boxes
      candle_q_dim_taylor_model_tree_lower_selector_six
      left_boxes and
      root_right_upper =
        candle_q_dim_taylor_model_tree_structural_vector_equality_six
          candle_q_dim_taylor_model_tree_upper_selector_six
          root_boxes
          candle_q_dim_taylor_model_tree_upper_selector_six
          right_boxes and
      non_split =
        candle_q_dim_taylor_model_tree_non_split_six
          split_index root_boxes left_boxes right_boxes and
      split_face =
        candle_q_dim_taylor_model_tree_component_equality_six
          candle_q_dim_taylor_model_tree_upper_selector_six
          left_boxes
          candle_q_dim_taylor_model_tree_lower_selector_six
          right_boxes split_index in
  let length_six = candle_q_dim_taylor_model_tree_length_six root_boxes and
      split_lower =
        prove
          (subst
            [mk_small_numeral split_index,`split_index:num`]
            `1 <= split_index`,
           ARITH_TAC) and
      split_upper =
        prove
          (subst
            [mk_small_numeral split_index,`split_index:num`]
            `split_index <= dimindex (:6)`,
           REWRITE_TAC[candle_q_dim_poly_jet_dim_six] THEN ARITH_TAC) in
  let goal =
    list_mk_comb
      (`candle_q_dim_taylor_model_tree_well_formed:
          real^6->candle_q_dim_taylor_model_tree->bool`,
       [`ARB:real^6`;tree]) in
  let outer_expansion =
    ONCE_REWRITE_CONV
      [candle_q_dim_taylor_model_tree_well_formed_def] goal in
  let expansion =
    TRANS outer_expansion
      (REWRITE_CONV
        [candle_q_dim_taylor_model_tree_root_boxes_def]
        (rand (concl outer_expansion))) in
  let facts =
    end_itlist CONJ
      [length_six;split_lower;split_upper;
       root_left_lower;root_right_upper;non_split;split_face;
       left_well_formed;right_well_formed] in
  if not (aconv (rand (concl expansion)) (concl facts)) then
    failwith "six-dimensional Taylor tree: topology expansion mismatch";
  tree,EQ_MP (SYM expansion) facts;;

end;;
