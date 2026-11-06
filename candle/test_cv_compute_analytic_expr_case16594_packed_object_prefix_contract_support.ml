(* ========================================================================== *)
(* Reusable genuine-prefix proof driver for the case-16594 input contract.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The driver turns an exact prefix of the       *)
(* preserved 875-row plan capture into closed HOL terms and proves both      *)
(* correspondence directions before applying the payload-parametric contract *)
(* theorem.                                                                   *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_prefix4_input_contract.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support = struct

open Candle_cv_analytic_expr_packed_source_object_whole_input_data_sound;;
open Test_cv_compute_analytic_expr_case16594_packed_object_prefix4_input_contract;;

let candle_case16594_prefix_contract_read_cells count =
  if count < 1 || count > 875 then
    failwith "case16594 prefix contract support: count";
  let channel = Stdlib.open_in candle_case16594_prefix4_fixture_path in
  let rec read index result =
    if index = count then (Stdlib.close_in channel; rev result) else
    let fields =
      candle_case16594_prefix4_split '\t' (Stdlib.input_line channel) in
    if length fields <> 5 ||
       int_of_string (candle_case16594_prefix4_nth 0 fields) <> index then
      failwith "case16594 prefix contract support: fixture row drift";
    let lower = candle_case16594_prefix4_vector
      (candle_case16594_prefix4_nth 3 fields)
    and upper = candle_case16594_prefix4_vector
      (candle_case16594_prefix4_nth 4 fields) in
    if length lower <> 6 || length upper <> 6 then
      failwith "case16594 prefix contract support: box width drift";
    read (index + 1) ((lower,upper) :: result) in
  read 0 [];;

let candle_case16594_prefix_contract_data_with_radius_padding
    radius_padding count =
  let geometry =
    map
      (candle_case16594_prefix4_pack_cell_with_radius_padding
        radius_padding)
      (candle_case16594_prefix_contract_read_cells count) in
  let radii_batches =
    mk_list
      (map fst geometry,
       `:((num#num)#num)list`)
  and jobs =
    mk_list
      (map snd geometry,
       `:((((num#num)#num)#((num#num)#num))list #
         (((((num#num)#num)#((num#num)#num))list) #
          ((((num#num)#num)#((num#num)#num))list)))`) in
  radii_batches,jobs;;

let candle_case16594_prefix_contract_data =
  candle_case16594_prefix_contract_data_with_radius_padding 0;;

let candle_case16594_prefix_contract_job_geometry_goal
    radii_batches jobs =
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
  list_mk_comb (builder,[radii_batches;jobs]);;

let candle_case16594_prefix_contract_job_geometry
    radii_batches jobs =
  prove
    (candle_case16594_prefix_contract_job_geometry_goal
       radii_batches jobs,
     candle_case16594_prefix4_job_geometry_tactic);;

let candle_case16594_prefix_contract_input_goal
    count radii_batches jobs =
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
        [radii_batches;jobs;mk_small_numeral count;certificate_batches]));;

let candle_case16594_prefix_contract_input
    count radii_batches jobs job_geometry =
  prove
    (candle_case16594_prefix_contract_input_goal
       count radii_batches jobs,
     BETA_TAC THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC
       candle_q_packed_object_attach_certificates_input_contract THEN
     CONJ_TAC THENL
      [ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
       MATCH_ACCEPT_TAC (BETA_RULE job_geometry)]);;

let candle_case16594_prefix_contract_prove_with_radius_padding
    radius_padding count =
  let radii_batches,jobs =
    candle_case16594_prefix_contract_data_with_radius_padding
      radius_padding count in
  let job_geometry =
    candle_case16594_prefix_contract_job_geometry radii_batches jobs in
  let input_contract =
    candle_case16594_prefix_contract_input
      count radii_batches jobs job_geometry in
  if hyp job_geometry <> [] || hyp input_contract <> [] then
    failwith "case16594 prefix contract support: assumptions";
  radii_batches,jobs,job_geometry,input_contract;;

let candle_case16594_prefix_contract_prove =
  candle_case16594_prefix_contract_prove_with_radius_padding 0;;

end;;
