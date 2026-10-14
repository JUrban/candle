(* ========================================================================== *)
(* Genuine case-10173: one authenticated verdict through compact topology.   *)
(*                                                                            *)
(* The raw checker authenticates and proves every numerical leaf; the        *)
(* compact token replay glues exactly those source-level cells to one root.   *)
(* This theorem is deliberately independent of any particular captured data. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_batch_sound.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_compact_stack_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_authenticated_complete_sound = struct

open Candle_cv_analytic_expr_case10173_historical_source_contract;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_batch_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;

let candle_case10173_hist_authenticated_complete_sound = prove
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
       (T,([],[root_boxes]))
     ==>
     m_cell_pass
       (candle_analytic_denote_dim
         candle_case10173_hist_authenticated_source)
       ((candle_q_box_lower_vector root_boxes:real^6),
        (candle_q_box_upper_vector root_boxes:real^6))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (ISPECL
      [`candle_case10173_hist_authenticated_source`;
       `type_witness:real^6`;
       `tokens:
         candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
       `candle_cv_fso_variable_jobs_decode (encoded:cval)`;
       `root_boxes:(((num#num)#num)#((num#num)#num))list`]
      candle_case10173_hist_jobs_compact_sound) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      (ISPECL
        [`encoded:cval`;
         `roots:
           (((((num#num)#(num#num))#((num#num)#(num#num)))#
             (((num#num)#(num#num))#((num#num)#(num#num)))))list`]
        candle_case10173_hist_authenticated_checked_raw_jobs_sound) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_COMPLETE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
