(* ========================================================================== *)
(* Reusable data contract for packed-object whole-call batches.              *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The numerical certificate payload is attached *)
(* only after the source/center/outer/radius geometry has been established.   *)
(* This keeps the reusable geometric proof independent of certificate bytes;  *)
(* the executable whole-call theorem remains responsible for accepting those  *)
(* bytes.                                                                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_whole_success_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_whole_input_data_sound = struct

open Candle_cv_analytic_expr_packed_source_object_whole_success_sound;;

let candle_q_packed_object_attach_certificates_input_contract = prove
 (`!radii_batches (certificate_batches:A list) jobs.
     LENGTH radii_batches = LENGTH certificate_batches /\
     ALL2
       (\radii job.
          LENGTH (SND (SND job)) = 6 /\
          LENGTH (FST (SND job)) = 6 /\
          LENGTH (FST job) = 6 /\
          LENGTH radii = 6 /\
          candle_q_packed_source_correspondence
            (SND (SND job)) (FST (SND job)) (FST job) radii /\
          candle_q_packed_source_correspondence
            (FST job) (FST (SND job)) (FST job) radii)
       radii_batches jobs
     ==>
     candle_q_packed_object_whole_input_contract
       (MAP2
         (\radii certificates. (radii,certificates))
         radii_batches certificate_batches)
       jobs`,
  LIST_INDUCT_TAC THENL
   [X_GEN_TAC `certificate_batches:A list` THEN
    MP_TAC (ISPEC `certificate_batches:A list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `certificate_batch:A`
          (X_CHOOSE_THEN `remaining_certificate_batches:A list`
            SUBST_ALL_TAC))) THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC
      [LENGTH; ALL2; NOT_SUC;
       MAP2_DEF; candle_q_packed_object_whole_input_contract_def];
    POP_ASSUM (LABEL_TAC "input_contract_ih") THEN
    X_GEN_TAC `certificate_batches:A list` THEN
    MP_TAC (ISPEC `certificate_batches:A list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `certificate_batch:A`
          (X_CHOOSE_THEN `remaining_certificate_batches:A list`
            SUBST_ALL_TAC))) THENL
     [X_GEN_TAC
        `jobs:
          ((((num#num)#num)#((num#num)#num))list #
           ((((num#num)#num)#((num#num)#num))list #
            (((num#num)#num)#((num#num)#num))list))list` THEN
      REWRITE_TAC[LENGTH; NOT_SUC];
      ALL_TAC] THEN
    X_GEN_TAC
      `jobs:
        ((((num#num)#num)#((num#num)#num))list #
         ((((num#num)#num)#((num#num)#num))list #
          (((num#num)#num)#((num#num)#num))list))list` THEN
    MP_TAC
      (ISPEC
        `jobs:
          ((((num#num)#num)#((num#num)#num))list #
           ((((num#num)#num)#((num#num)#num))list #
            (((num#num)#num)#((num#num)#num))list))list`
        list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN
          `job:
            (((num#num)#num)#((num#num)#num))list #
            ((((num#num)#num)#((num#num)#num))list #
             (((num#num)#num)#((num#num)#num))list)`
          (X_CHOOSE_THEN
            `remaining_jobs:
              ((((num#num)#num)#((num#num)#num))list #
               ((((num#num)#num)#((num#num)#num))list #
                (((num#num)#num)#((num#num)#num))list))list`
            SUBST_ALL_TAC))) THENL
     [REWRITE_TAC[ALL2];
      REWRITE_TAC
        [LENGTH; SUC_INJ; ALL2;
         MAP2_DEF;
         candle_q_packed_object_whole_input_contract_def;
         FST; SND] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REMOVE_THEN "input_contract_ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[TL]]]);;

if hyp candle_q_packed_object_attach_certificates_input_contract <> [] then
  failwith "packed object whole input data: assumptions";;

print_endline
  "CANDLE_CV_PACKED_OBJECT_WHOLE_INPUT_DATA_SOUND_OK assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
