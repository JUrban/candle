#!/usr/bin/env python3
"""Add development-only phase markers to exact Flyspeck checker sources.

The instrumented sources preserve theorem-producing expressions and add only
flushed text markers.  Callers must pin the input hash so profiling never
silently targets a different compatibility source.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


class InstrumentationError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def replace_once(source: str, old: str, new: str, label: str) -> str:
    count = source.count(old)
    if count != 1:
        raise InstrumentationError(
            f"{label}: expected one exact source anchor, found {count}"
        )
    return source.replace(old, new, 1)


LP_HELPERS = r'''let candle_lp_profile_terminal = ref 0;;

let candle_lp_profile_marker scope phase event =
  Format.print_string
    ("CANDLE_CERT_PROFILE lane=lp scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);
  Format.print_newline();
  Format.print_flush();;

let candle_lp_profile_scope () =
  "terminal-" ^ string_of_int !candle_lp_profile_terminal;;
'''


def instrument_lp(source: str) -> str:
    source = replace_once(
        source,
        "let var_table : (term, thm) Hashtbl.t = Hashtbl.create 1000;;\n",
        "let var_table : (term, thm) Hashtbl.t = Hashtbl.create 1000;;\n\n"
        + LP_HELPERS,
        "lp helpers",
    )
    source = replace_once(
        source,
        "let candle_lp_profile_scope () =\n"
        "  \"terminal-\" ^ string_of_int !candle_lp_profile_terminal;;\n\n\n"
        "let prove_flyspeck_lp_step1 hyp_list_tm hyp_set hyp_fun std_flag precision infeasible constraints target_variables variable_bounds =\n"
        "  let precision_constant = num 10 **/ (num precision) in\n",
        "let candle_lp_profile_scope () =\n"
        "  \"terminal-\" ^ string_of_int !candle_lp_profile_terminal;;\n\n\n"
        "let prove_flyspeck_lp_step1 hyp_list_tm hyp_set hyp_fun std_flag precision infeasible constraints target_variables variable_bounds =\n"
        "  let candle_profile_scope = candle_lp_profile_scope () in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"step1-total\" \"begin\" in\n"
        "  let precision_constant = num 10 **/ (num precision) in\n",
        "lp step begin",
    )
    source = replace_once(
        source,
        "  let ineqs1 = map sum_step constraints in\n  let ineqs2 = List.sort",
        "  let _ = candle_lp_profile_marker candle_profile_scope \"constraint-theorems\" \"begin\" in\n"
        "  let ineqs1 = map sum_step constraints in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"constraint-theorems\" \"end\" in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"constraint-combine\" \"begin\" in\n"
        "  let ineqs2 = List.sort",
        "lp constraints",
    )
    source = replace_once(
        source,
        "  let s1 = mul_step s1' (mk_real_int precision_constant) in\n  let r1 = if infeasible then s1 else\n",
        "  let s1 = mul_step s1' (mk_real_int precision_constant) in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"constraint-combine\" \"end\" in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"global-inequality\" \"begin\" in\n"
        "  let r1 = if infeasible then s1 else\n",
        "lp constraint combine",
    )
    source = replace_once(
        source,
        "      add_step' ineq_th4 s1 in\n  let _ = map add_to_var_table variable_bounds and\n",
        "      add_step' ineq_th4 s1 in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"global-inequality\" \"end\" in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"variable-bounds\" \"begin\" in\n"
        "  let _ = map add_to_var_table variable_bounds and\n",
        "lp global inequality",
    )
    source = replace_once(
        source,
        "      _ = map add_to_var_table target_variables in\n  let list1 = Hashtbl.fold",
        "      _ = map add_to_var_table target_variables in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"variable-bounds\" \"end\" in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"variable-cancellation\" \"begin\" in\n"
        "  let list1 = Hashtbl.fold",
        "lp variable bounds",
    )
    source = replace_once(
        source,
        "  let result = List.fold_left add_cancel_step r1 var_list in\n  let n_tm =",
        "  let result = List.fold_left add_cancel_step r1 var_list in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"variable-cancellation\" \"end\" in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"final-numeral-check\" \"begin\" in\n"
        "  let n_tm =",
        "lp cancellation",
    )
    source = replace_once(
        source,
        "  let _ = candle_lp_profile_marker candle_profile_scope \"final-numeral-check\" \"begin\" in\n"
        "  let n_tm = (rand o rand o rand o concl) result in\n"
        "  let r_eq_th = INST[n_tm, n_var_num] FINAL_INEQ in\n"
        "  let not_zero_th = NUM_EQ0_HASH_CONV n_tm in\n"
        "    EQ_MP not_zero_th (EQ_MP r_eq_th result);;\n",
        "  let _ = candle_lp_profile_marker candle_profile_scope \"final-numeral-check\" \"begin\" in\n"
        "  let n_tm = (rand o rand o rand o concl) result in\n"
        "  let r_eq_th = INST[n_tm, n_var_num] FINAL_INEQ in\n"
        "  let not_zero_th = NUM_EQ0_HASH_CONV n_tm in\n"
        "  let final_th = EQ_MP not_zero_th (EQ_MP r_eq_th result) in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"final-numeral-check\" \"end\" in\n"
        "  let _ = candle_lp_profile_marker candle_profile_scope \"step1-total\" \"end\" in\n"
        "    final_th;;\n",
        "lp final check",
    )
    source = replace_once(
        source,
        "    | Lp_terminal terminal ->\n\tlet _ = next_terminal() in\n\tlet hyp_set, hyp_fun = snd (compute_hypermap arg) in\n\tlet r =",
        "    | Lp_terminal terminal ->\n"
        "\tlet _ = next_terminal() in\n"
        "\tlet _ = candle_lp_profile_terminal := !candle_lp_profile_terminal + 1 in\n"
        "\tlet candle_profile_scope = candle_lp_profile_scope () in\n"
        "\tlet _ = candle_lp_profile_marker candle_profile_scope \"terminal-total\" \"begin\" in\n"
        "\tlet _ = candle_lp_profile_marker candle_profile_scope \"compute-hypermap\" \"begin\" in\n"
        "\tlet hyp_set, hyp_fun = snd (compute_hypermap arg) in\n"
        "\tlet _ = candle_lp_profile_marker candle_profile_scope \"compute-hypermap\" \"end\" in\n"
        "\tlet _ = candle_lp_profile_marker candle_profile_scope \"certificate-reification\" \"begin\" in\n"
        "\tlet r =",
        "lp terminal entry",
    )
    source = replace_once(
        source,
        "\t    vb = map r terminal.variable_bounds in\n\tlet th0 =",
        "\t    vb = map r terminal.variable_bounds in\n"
        "\tlet _ = candle_lp_profile_marker candle_profile_scope \"certificate-reification\" \"end\" in\n"
        "\tlet th0 =",
        "lp terminal reification",
    )
    source = replace_once(
        source,
        "\tlet _ = report_progress() in\n\tlet th1 =",
        "\tlet _ = report_progress() in\n"
        "\tlet _ = candle_lp_profile_marker candle_profile_scope \"terminal-discharge\" \"begin\" in\n"
        "\tlet th1 =",
        "lp terminal discharge begin",
    )
    source = replace_once(
        source,
        "\tlet th2 = if std_flag then MY_PROVE_HYP estd_refl th1 else itlist MY_PROVE_HYP base_ineqs th1 in\n\t  (MY_PROVE_HYP arg.lp_cond_th) th2\n",
        "\tlet th2 = if std_flag then MY_PROVE_HYP estd_refl th1 else itlist MY_PROVE_HYP base_ineqs th1 in\n"
        "\tlet final_th = (MY_PROVE_HYP arg.lp_cond_th) th2 in\n"
        "\tlet _ = candle_lp_profile_marker candle_profile_scope \"terminal-discharge\" \"end\" in\n"
        "\tlet _ = candle_lp_profile_marker candle_profile_scope \"terminal-total\" \"end\" in\n"
        "\t  final_th\n",
        "lp terminal discharge end",
    )
    source = replace_once(
        source,
        "let verify_lp_certificate certificate good_th =\n  let n = count_terminals certificate.root_case in\n  let hyp_list =",
        "let verify_lp_certificate certificate good_th =\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"total\" \"begin\" in\n"
        "  let _ = candle_lp_profile_terminal := 0 in\n"
        "  let n = count_terminals certificate.root_case in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"hypermap-decode\" \"begin\" in\n"
        "  let hyp_list =",
        "lp certificate begin",
    )
    source = replace_once(
        source,
        "  let hyp_list0_tm = (to_num o create_hol_list) hyp_list in\n  let hyp_set0, hyp_fun0 = compute_all hyp_list0_tm good_th in\n  let lp_cond0, lp_tau0 = contravening_conditions hyp_list0_tm hyp_set0 in\n",
        "  let hyp_list0_tm = (to_num o create_hol_list) hyp_list in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"hypermap-decode\" \"end\" in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"compute-all\" \"begin\" in\n"
        "  let hyp_set0, hyp_fun0 = compute_all hyp_list0_tm good_th in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"compute-all\" \"end\" in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"conditions\" \"begin\" in\n"
        "  let lp_cond0, lp_tau0 = contravening_conditions hyp_list0_tm hyp_set0 in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"conditions\" \"end\" in\n",
        "lp certificate compute",
    )
    source = replace_once(
        source,
        "  let ye_sym_th = (MY_PROVE_HYP lp_cond0 o INST[estd_v, e_cap_var]) ye_sym0 in\n  let base_ineqs =\n",
        "  let ye_sym_th = (MY_PROVE_HYP lp_cond0 o INST[estd_v, e_cap_var]) ye_sym0 in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"base-inequalities\" \"begin\" in\n"
        "  let base_ineqs =\n",
        "lp certificate base begin",
    )
    source = replace_once(
        source,
        "\t(r ye_hi_3) @ (r ye_hi_2h0) @ (r2 diag4_lo) @ (r2 diag5_lo) @ (r2 diag5_lo_sym) @ (r2 diag6_lo) @ (r2 diag6_lo_sym) in\n  let arg =",
        "\t(r ye_hi_3) @ (r ye_hi_2h0) @ (r2 diag4_lo) @ (r2 diag5_lo) @ (r2 diag5_lo_sym) @ (r2 diag6_lo) @ (r2 diag6_lo_sym) in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"base-inequalities\" \"end\" in\n"
        "  let arg =",
        "lp certificate base end",
    )
    source = replace_once(
        source,
        "  let final_th = verify_lp_case base_ineqs true (arg, certificate.root_case) in\n  let _ = Format.print_newline() in\n    (DISCH contravening_v o EXPAND_RULE \"L\" o EXPAND_RULE \"g\" o EXPAND_RULE \"h\") final_th;;\n",
        "  let _ = candle_lp_profile_marker \"certificate\" \"case-tree\" \"begin\" in\n"
        "  let final_th = verify_lp_case base_ineqs true (arg, certificate.root_case) in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"case-tree\" \"end\" in\n"
        "  let _ = Format.print_newline() in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"final-interface\" \"begin\" in\n"
        "  let result = (DISCH contravening_v o EXPAND_RULE \"L\" o EXPAND_RULE \"g\" o EXPAND_RULE \"h\") final_th in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"final-interface\" \"end\" in\n"
        "  let _ = candle_lp_profile_marker \"certificate\" \"total\" \"end\" in\n"
        "    result;;\n",
        "lp certificate end",
    )
    return source


NONLINEAR_HELPERS = r'''let candle_nonlinear_profile_case = ref "unassigned";;

let candle_nonlinear_profile_marker scope phase event =
  Format.print_string
    ("CANDLE_CERT_PROFILE lane=nonlinear scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);
  Format.print_newline();
  Format.print_flush();;
'''


def instrument_nonlinear_break(source: str) -> str:
    source = replace_once(
        source,
        "          let _ = incr candle_nonlinear_iarg_leaf_visits in\n",
        "          let _ =\n"
        "            candle_nonlinear_iarg_leaf_visits :=\n"
        "              !candle_nonlinear_iarg_leaf_visits + 1 in\n",
        "nonlinear leaf counter compatibility",
    )
    source = replace_once(
        source,
        "let candle_nonlinear_iarg_leaf_visits = ref 0;;\n",
        "let candle_nonlinear_iarg_leaf_visits = ref 0;;\n\n"
        + NONLINEAR_HELPERS,
        "nonlinear helpers",
    )
    source = replace_once(
        source,
        "let prove_serialize_processed_idq t iarg = \n  let cl =  mk_case_list t iarg in\n  let cthms = map Serialization.mk_ser_thm cl in  (* serialization used here *)\n  let athm =  prove_iargs_cases t iarg in\n  let rthm = itlist (PROVE_HYP) cthms athm in\n  let vthm = REWRITE_RULE \n",
        "let prove_serialize_processed_idq t iarg = \n"
        "  let scope = !candle_nonlinear_profile_case in\n"
        "  let _ = candle_nonlinear_profile_marker scope \"leaf-enumeration\" \"begin\" in\n"
        "  let cl =  mk_case_list t iarg in\n"
        "  let _ = candle_nonlinear_profile_marker scope \"leaf-enumeration\" \"end\" in\n"
        "  let _ = candle_nonlinear_profile_marker scope \"serialized-leaf-theorems\" \"begin\" in\n"
        "  let cthms = map Serialization.mk_ser_thm cl in  (* serialization used here *)\n"
        "  let _ = candle_nonlinear_profile_marker scope \"serialized-leaf-theorems\" \"end\" in\n"
        "  let _ = candle_nonlinear_profile_marker scope \"iarg-tree-reconstruction\" \"begin\" in\n"
        "  let athm =  prove_iargs_cases t iarg in\n"
        "  let _ = candle_nonlinear_profile_marker scope \"iarg-tree-reconstruction\" \"end\" in\n"
        "  let _ = candle_nonlinear_profile_marker scope \"leaf-discharge\" \"begin\" in\n"
        "  let rthm = itlist (PROVE_HYP) cthms athm in\n"
        "  let _ = candle_nonlinear_profile_marker scope \"leaf-discharge\" \"end\" in\n"
        "  let _ = candle_nonlinear_profile_marker scope \"length-rewrite\" \"begin\" in\n"
        "  let vthm = REWRITE_RULE \n",
        "nonlinear reconstruction phases",
    )
    source = replace_once(
        source,
        "    (DISCH_ALL rthm) in\n    vthm;;\n",
        "    (DISCH_ALL rthm) in\n"
        "  let _ = candle_nonlinear_profile_marker scope \"length-rewrite\" \"end\" in\n"
        "    vthm;;\n",
        "nonlinear reconstruction end",
    )
    source = replace_once(
        source,
        "let prove_prep s =\n  let _ = report s in\n    try\n      (s,prove_serialized_idv s)\n    with Failure m -> (report \"FAIL\"; (m^s,TRUTH));;\n",
        "let prove_prep s =\n"
        "  let _ = report s in\n"
        "  let _ = candle_nonlinear_profile_case := s in\n"
        "  let _ = candle_nonlinear_profile_marker s \"prep-case-total\" \"begin\" in\n"
        "    try\n"
        "      let th = prove_serialized_idv s in\n"
        "      let _ = candle_nonlinear_profile_marker s \"prep-case-total\" \"end\" in\n"
        "        (s,th)\n"
        "    with Failure m ->\n"
        "      (candle_nonlinear_profile_marker s \"prep-case-total\" \"fail\";\n"
        "       report \"FAIL\"; (m^s,TRUTH));;\n",
        "nonlinear prep wrapper",
    )
    return source


def instrument_nonlinear_assembly(source: str) -> str:
    source = replace_once(
        source,
        "let exec_results = exec();;\n",
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"implication-tactics\" \"begin\";;\n"
        "let exec_results = exec();;\n"
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"implication-tactics\" \"end\";;\n",
        "nonlinear implication tactics",
    )
    source = replace_once(
        source,
        "let prepared_nonlinear_imp_nonlinear = \n",
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"implication-assembly\" \"begin\";;\n\n"
        "let prepared_nonlinear_imp_nonlinear = \n",
        "nonlinear implication assembly begin",
    )
    source = replace_once(
        source,
        "    EQ_MP (SYM def) ineq_nn;;\n",
        "    EQ_MP (SYM def) ineq_nn;;\n\n"
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"implication-assembly\" \"end\";;\n",
        "nonlinear implication assembly end",
    )
    source = replace_once(
        source,
        "let prep_nonlinear_thml  =\n",
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"serialized-prep-cases\" \"begin\";;\n\n"
        "let prep_nonlinear_thml  =\n",
        "nonlinear prep begin",
    )
    source = replace_once(
        source,
        "       v;;\n\nlet _ = \n",
        "       v;;\n\n"
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"serialized-prep-cases\" \"end\";;\n\n"
        "let _ = \n",
        "nonlinear prep end",
    )
    source = replace_once(
        source,
        "let prepared_nonlinear = \n",
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"prepared-theorem-assembly\" \"begin\";;\n\n"
        "let prepared_nonlinear = \n",
        "nonlinear prepared begin",
    )
    source = replace_once(
        source,
        "     EQ_MP (SYM pn) prep_conj;;\n\nlet the_nonlinear_inequalities =",
        "     EQ_MP (SYM pn) prep_conj;;\n\n"
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"prepared-theorem-assembly\" \"end\";;\n"
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"final-theorem\" \"begin\";;\n\n"
        "let the_nonlinear_inequalities =",
        "nonlinear prepared end",
    )
    source = replace_once(
        source,
        "  ]);;\n  (* }}} *)\n\n(*\n\n the_nonlinear_inequalities\n",
        "  ]);;\n  (* }}} *)\n\n"
        "let _ = Break_case_exec.candle_nonlinear_profile_marker \"assembly\" \"final-theorem\" \"end\";;\n\n"
        "(*\n\n the_nonlinear_inequalities\n",
        "nonlinear final theorem",
    )
    return source


INSTRUMENTERS = {
    "lp": instrument_lp,
    "nonlinear-break": instrument_nonlinear_break,
    "nonlinear-assembly": instrument_nonlinear_assembly,
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", choices=sorted(INSTRUMENTERS), required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--expected-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    raw = args.input.read_bytes()
    actual = sha256(raw)
    if actual != args.expected_sha256:
        raise InstrumentationError(
            f"input hash mismatch: expected {args.expected_sha256}, got {actual}"
        )
    source = raw.decode("utf-8")
    result = INSTRUMENTERS[args.kind](source).encode("utf-8")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(result)
    print(f"input_sha256={actual}")
    print(f"output_sha256={sha256(result)}")
    print(f"output={args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
