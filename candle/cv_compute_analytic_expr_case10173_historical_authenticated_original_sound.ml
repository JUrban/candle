(* ========================================================================== *)
(* Genuine case-10173: checked batch and topology to original Flyspeck goal. *)
(*                                                                            *)
(* This is the complete logical composition, independent of how the three   *)
(* executable premises are discharged.  In particular, the production fast *)
(* path may supply the checked verdict without replaying the generic checker. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_complete_sound.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_original_bridge.ml";;

module Candle_cv_analytic_expr_case10173_historical_authenticated_original_sound = struct

open Candle_cv_analytic_expr_case10173_historical_source_contract;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_complete_sound;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_original_bridge;;

let candle_case10173_hist_authenticated_original_sound = prove
 (`!encoded roots tokens (type_witness:real^6) root_boxes.
     candle_cv_case10173_hist_jobs_well_formed encoded = Cexp_num 1 /\
     candle_cv_case10173_hist_checked_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile
           candle_case10173_hist_authenticated_source))
       encoded (candle_cv_case10173_hist_root_records roots) = Cexp_num 1 /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_run
       (dimindex (:6)) tokens
       (candle_cv_fso_variable_jobs_decode encoded) [] =
       (T,([],[root_boxes])) /\
     ((candle_q_box_lower_vector root_boxes:real^6),
      (candle_q_box_upper_vector root_boxes:real^6)) =
       candle_case10173_hist_original_domain
     ==>
     ineqm [x1; x2; x3; x4; x5; x6]
       (frac_left 0 #0.5000
       [#4.7524,#6.3504; #4.0,#4.7524; #4.0,#4.7524;
        #4.0,#2.25 * #2.25; #4.0,#2.25 * #2.25;
        #4.0,#2.25 * #2.25])
       (unit6 x1 x2 x3 x4 x5 x6 * #1.277 +
        sqrt_x1 x1 x2 x3 x4 x5 x6 * #0.273298 +
        unit6 x1 x2 x3 x4 x5 x6 * #0.273298 * -- #2.18 +
        sqrt_x2 x1 x2 x3 x4 x5 x6 * -- #0.273853 +
        unit6 x1 x2 x3 x4 x5 x6 * #0.273853 * #2.0 +
        sqrt_x3 x1 x2 x3 x4 x5 x6 * -- #0.273853 +
        unit6 x1 x2 x3 x4 x5 x6 * #0.273853 * #2.0 +
        sqrt_x4 x1 x2 x3 x4 x5 x6 * #0.708818 +
        unit6 x1 x2 x3 x4 x5 x6 * #0.708818 * -- #2.0 +
        sqrt_x5 x1 x2 x3 x4 x5 x6 * -- #0.313988 +
        unit6 x1 x2 x3 x4 x5 x6 * #0.313988 * #2.0 +
        sqrt_x6 x1 x2 x3 x4 x5 x6 * -- #0.313988 +
        unit6 x1 x2 x3 x4 x5 x6 * #0.313988 * #2.0 +
        dihatn_x x1 x2 x3 x4 x5 x6 * -- &1 < &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_case10173_hist_authenticated_original_bridge THEN
  MP_TAC
    (ISPECL
      [`encoded:cval`;
       `roots:
         (((((num#num)#(num#num))#((num#num)#(num#num)))#
           (((num#num)#(num#num))#((num#num)#(num#num)))))list`;
       `tokens:
         candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
       `type_witness:real^6`;
       `root_boxes:(((num#num)#num)#((num#num)#num))list`]
      candle_case10173_hist_authenticated_complete_sound) THEN
  ASM_REWRITE_TAC[]);;

if hyp candle_case10173_hist_authenticated_original_sound <> [] ||
   not
     (aconv
       (snd (dest_imp (snd (strip_forall
         (concl candle_case10173_hist_authenticated_original_sound)))))
       Candle_cv_analytic_expr_case10173_fixture.candle_case10173_analytic_target)
then failwith "case10173 authenticated original sound: theorem drift";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_ORIGINAL_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
