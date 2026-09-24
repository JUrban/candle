(* ========================================================================== *)
(* Prepare every genuine source expression in the first nonlinear target.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The reflected-driver checkpoint has already   *)
(* authenticated and reconstructed the three source disjuncts.  This focused *)
(* batch measures the one-time theorem-producing reification/compilation for  *)
(* each expression.  It deliberately makes no certificate or acceptance      *)
(* claim for the two expressions not selected by the genuine certificate.    *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

open Candle_cv_polynomial_expr_dim_jet_prove;;

let candle_reflected_real_source_batch_axioms_before = axioms ();;

let rec candle_reflected_real_source_batch_prepare index functions =
  match functions with
  | [] -> []
  | function_tm :: rest ->
      let _ =
        print_endline
          ("CANDLE_CV_REAL_SOURCE_BATCH_BEGIN index=" ^
           string_of_int index) in
      let started = Unix.gettimeofday () in
      let prepared = candle_q_dim_poly_jet_prepare_six function_tm in
      let seconds = Unix.gettimeofday () -. started in
      let instructions = length (dest_list prepared.program_term) in
      if hyp prepared.valid_theorem <> [] ||
         hyp prepared.source_theorem <> [] ||
         hyp prepared.compile_theorem <> [] ||
         hyp prepared.program_representation <> [] then
        failwith "reflected real source batch: prepared theorem assumptions"
      else
        print_endline
          ("CANDLE_CV_REAL_SOURCE_BATCH_ITEM index=" ^
           string_of_int index ^
           " instructions=" ^ string_of_int instructions ^
           " seconds=" ^ string_of_float seconds ^
           " source_theorem_md5=" ^
           Digest.to_hex
             (Digest.string (string_of_thm prepared.source_theorem)));
      prepared ::
        candle_reflected_real_source_batch_prepare (index + 1) rest;;

let candle_reflected_real_source_batch_prepared =
  candle_reflected_real_source_batch_prepare 0 candle_nl_capture_functions;;

if length candle_reflected_real_source_batch_prepared <> 3 then
  failwith "reflected real source batch: expression cardinality drift";;

let candle_reflected_real_source_batch_axioms_after = axioms ();;
if length candle_reflected_real_source_batch_axioms_after <>
     length candle_reflected_real_source_batch_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_reflected_real_source_batch_axioms_before)
       candle_reflected_real_source_batch_axioms_after) then
  failwith "reflected real source batch: changed the global axiom set";;

let _ =
  print_endline
    "CANDLE_CV_REAL_SOURCE_BATCH_RESULT expressions=3 theorem_producing=true";;
let _ = print_endline "CANDLE_CV_REAL_SOURCE_BATCH_OK";;
