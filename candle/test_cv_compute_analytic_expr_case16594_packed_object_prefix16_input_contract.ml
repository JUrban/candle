(* ========================================================================== *)
(* Genuine case-16594 sixteen-cell input contract from the sealed capture.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the first measured scale-up of the    *)
(* four-cell generic whole-input contract.                                    *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_prefix4_input_contract.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_prefix16_input_contract = struct

open Candle_cv_analytic_expr_packed_source_object_whole_input_data_sound;;
open Test_cv_compute_analytic_expr_case16594_packed_object_prefix4_input_contract;;

let candle_case16594_prefix16_count = 16;;

let candle_case16594_prefix16_read_cells () =
  let channel = Stdlib.open_in candle_case16594_prefix4_fixture_path in
  let rec read index result =
    if index = candle_case16594_prefix16_count then
      (Stdlib.close_in channel; rev result)
    else
      let fields =
        candle_case16594_prefix4_split '\t' (Stdlib.input_line channel) in
      if length fields <> 5 ||
         int_of_string (candle_case16594_prefix4_nth 0 fields) <> index then
        failwith "case16594 prefix16 input contract: fixture row drift";
      let lower = candle_case16594_prefix4_vector
        (candle_case16594_prefix4_nth 3 fields)
      and upper = candle_case16594_prefix4_vector
        (candle_case16594_prefix4_nth 4 fields) in
      if length lower <> 6 || length upper <> 6 then
        failwith "case16594 prefix16 input contract: box width drift";
      read (index + 1) ((lower,upper) :: result) in
  read 0 [];;

let candle_case16594_prefix16_geometry =
  map candle_case16594_prefix4_pack_cell
    (candle_case16594_prefix16_read_cells ());;

let candle_case16594_prefix16_radii_batches =
  mk_list
    (map fst candle_case16594_prefix16_geometry,
     `:((num#num)#num)list`);;

let candle_case16594_prefix16_jobs =
  mk_list
    (map snd candle_case16594_prefix16_geometry,
     `:((((num#num)#num)#((num#num)#num))list #
       (((((num#num)#num)#((num#num)#num))list) #
        ((((num#num)#num)#((num#num)#num))list)))`);;

let candle_case16594_prefix16_job_geometry_goal =
  let builder =
    `\radii_batches jobs.
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
         radii_batches jobs` in
  list_mk_comb
    (builder,
     [candle_case16594_prefix16_radii_batches;
      candle_case16594_prefix16_jobs]);;

let candle_case16594_prefix16_job_geometry = prove
 (candle_case16594_prefix16_job_geometry_goal,
  candle_case16594_prefix4_job_geometry_tactic);;

let candle_case16594_prefix16_input_contract_goal =
  let certificate_batches =
    mk_var ("certificate_batches",`:A list`) in
  let builder =
    `\radii_batches jobs count (certificate_batches:A list).
       LENGTH certificate_batches = count
       ==>
       candle_q_packed_object_whole_input_contract
         (MAP2
           (\radii certificates. (radii,certificates))
           radii_batches certificate_batches)
         jobs` in
  mk_forall
    (certificate_batches,
     list_mk_comb
       (builder,
        [candle_case16594_prefix16_radii_batches;
         candle_case16594_prefix16_jobs;
         mk_small_numeral candle_case16594_prefix16_count;
         certificate_batches]));;

let candle_case16594_prefix16_input_contract_tactic =
  BETA_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_q_packed_object_attach_certificates_input_contract THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    MATCH_ACCEPT_TAC (BETA_RULE candle_case16594_prefix16_job_geometry)];;

let candle_case16594_prefix16_input_contract = prove
 (candle_case16594_prefix16_input_contract_goal,
  candle_case16594_prefix16_input_contract_tactic);;

if hyp candle_case16594_prefix16_job_geometry <> [] ||
   hyp candle_case16594_prefix16_input_contract <> [] then
  failwith "case16594 prefix16 input contract: assumptions";;

print_endline
  "CANDLE_CV_CASE16594_PACKED_OBJECT_PREFIX16_INPUT_CONTRACT_OK cells=16 certificate_payload=parametric assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
