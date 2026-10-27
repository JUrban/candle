(* ========================================================================== *)
(* Genuine case-16594 cell-0 correspondence for the packed 2^40 checker.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The exact source box below is row zero of the *)
(* authenticated 875-cell jobs fixture (SHA-256                              *)
(* 236c4ffa1773b92c80584defa24beeddfb20b59811bc287a4f4770da87ac8e80).      *)
(* The packed center, upward radius, and outer box are the values emitted by  *)
(* the untrusted packer.  This test gives those values no authority: the HOL  *)
(* kernel proves the complete source-correspondence predicate.               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_packed_geometry_sound.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_cell0_correspondence = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_packed_geometry_sound;;

let candle_case16594_cell0_num text = Num.num_of_string text;;

let candle_case16594_cell0_q numerator denominator =
  candle_q_term
    (Num.div_num
      (candle_case16594_cell0_num numerator)
      (candle_case16594_cell0_num denominator));;

let candle_case16594_cell0_scaled_q text =
  candle_q_term
    (Num.div_num
      (candle_case16594_cell0_num text)
      (candle_case16594_cell0_num "1099511627776"));;

let candle_case16594_cell0_interval
    lower_numerator lower_denominator upper_numerator upper_denominator =
  mk_pair
    (candle_case16594_cell0_q lower_numerator lower_denominator,
     candle_case16594_cell0_q upper_numerator upper_denominator);;

let candle_case16594_cell0_scaled_interval lower upper =
  mk_pair
    (candle_case16594_cell0_scaled_q lower,
     candle_case16594_cell0_scaled_q upper);;

let candle_case16594_cell0_source_boxes =
  mk_list
    ([candle_case16594_cell0_interval
        "6469" "1250" "3500160000001" "640000000000";
      candle_case16594_cell0_interval
        "4" "1" "2748032000001" "640000000000";
      candle_case16594_cell0_interval
        "6469" "1250" "3500160000001" "640000000000";
      candle_case16594_cell0_interval
        "4" "1" "2936064000001" "640000000000";
      candle_case16594_cell0_interval
        "423903" "40000" "7028444000001" "640000000000";
      candle_case16594_cell0_interval
        "6469" "1250" "3688192000001" "640000000000"],
     candle_q_interval_type);;

let candle_case16594_cell0_center_boxes =
  mk_list
    ([candle_case16594_cell0_scaled_interval "5851710834187" "5851710834188";
      candle_case16594_cell0_scaled_interval "4559564769225" "4559564769226";
      candle_case16594_cell0_scaled_interval "5851710834187" "5851710834188";
      candle_case16594_cell0_scaled_interval "4721083027345" "4721083027346";
      candle_case16594_cell0_scaled_interval "11863465893718" "11863465893719";
      candle_case16594_cell0_scaled_interval "6013229092307" "6013229092308"],
     candle_q_interval_type);;

let candle_case16594_cell0_outer_boxes =
  mk_list
    ([candle_case16594_cell0_scaled_interval "5690192576065" "6013229092310";
      candle_case16594_cell0_scaled_interval "4398046511103" "4721083027348";
      candle_case16594_cell0_scaled_interval "5690192576065" "6013229092310";
      candle_case16594_cell0_scaled_interval "4398046511103" "5044119543588";
      candle_case16594_cell0_scaled_interval "11652156938727" "12074774848710";
      candle_case16594_cell0_scaled_interval "5690192576065" "6336265608550"],
     candle_q_interval_type);;

let candle_case16594_cell0_radii =
  mk_list
    (map candle_case16594_cell0_scaled_q
       ["161518258122"; "161518258122"; "161518258122";
        "323036516242"; "211308954991"; "323036516242"],
     `:((num#num)#num)`);;

let candle_case16594_cell0_forall_lt_six = prove
 (`(!k. k < 6 ==> P k) <=>
    P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5`,
  EQ_TAC THENL
   [DISCH_THEN (LABEL_TAC "bounded") THEN
    REPEAT CONJ_TAC THEN
    USE_THEN "bounded" MATCH_MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 2` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 3` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 4` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 5` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let candle_case16594_cell0_forall_lt_length_six = prove
 (`(!k. k < SUC (SUC (SUC (SUC (SUC (SUC 0))))) ==> P k) <=>
    P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5`,
  EQ_TAC THENL
   [DISCH_THEN (LABEL_TAC "bounded") THEN
    REPEAT CONJ_TAC THEN
    USE_THEN "bounded" MATCH_MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 2` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 3` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 4` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 5` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let candle_case16594_cell0_correspondence_goal =
  list_mk_comb
    (`candle_q_packed_source_correspondence`,
     [candle_case16594_cell0_source_boxes;
      candle_case16594_cell0_center_boxes;
      candle_case16594_cell0_outer_boxes;
      candle_case16594_cell0_radii]);;

let candle_case16594_cell0_correspondence = prove
  (candle_case16594_cell0_correspondence_goal,
   REWRITE_TAC
     [candle_q_packed_source_correspondence_def;
      candle_q_packed_center_contains_source_midpoint_def;
      candle_q_packed_radii_cover_source_def;
      candle_q_packed_outer_covers_source_def;
      candle_case16594_cell0_forall_lt_six;
      candle_case16594_cell0_forall_lt_length_six;
      candle_q_box_valid_list_def; candle_q_radius_list_def;
      candle_q_interval_contains_def; candle_q_le_real;
      LENGTH; ALL] THEN
   CONV_TAC (DEPTH_CONV EL_CONV) THEN
   REWRITE_TAC
     [candle_q_midpoint_real; candle_q_radius_real;
      candle_q_real_def; candle_q_den_def; candle_lc_zreal_def;
      FST; SND] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN
   TRY (REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV));;

let candle_case16594_cell0_handoff =
  let theorem =
    INST_TYPE [`:6`,`:N`]
      candle_q_packed_source_correspondence_handoff in
  MATCH_MP
    (SPECL
      [candle_case16594_cell0_source_boxes;
       candle_case16594_cell0_center_boxes;
       candle_case16594_cell0_outer_boxes;
       candle_case16594_cell0_radii]
      theorem)
    (CONJ
      (TRANS
        (LENGTH_CONV
          (mk_comb
            (`LENGTH:
               ((((num#num)#num)#((num#num)#num))list)->num`,
             candle_case16594_cell0_source_boxes)))
        (SYM (DIMINDEX_CONV `dimindex (:6)`)))
      candle_case16594_cell0_correspondence);;

if hyp candle_case16594_cell0_correspondence <> [] ||
   hyp candle_case16594_cell0_handoff <> [] then
  failwith "case16594 packed cell0 correspondence: assumptions";;

print_endline
  "CANDLE_CV_CASE16594_PACKED_CELL0_CORRESPONDENCE_OK DEVELOPMENT_NON_RELEASE";;

end;;
