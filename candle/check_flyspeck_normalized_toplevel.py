#!/usr/bin/env python3
"""Check that the selected normalized route has no OCaml toplevel backdoor."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

import flyspeck_manifest
import flyspeck_normalize


ENTRY_PATHS = {
    "PROJECT-TOPLOOP-S3-USE-FILE-B-001":
        "text_formalization/build/strictbuild.hl",
    "PROJECT-MODULE-S3-SET-MAKE-001":
        "text_formalization/general/serialization.hl",
    "PROJECT-TOPLOOP-S3-UPDATE-DATABASE-001":
        "text_formalization/general/update_database_400.ml",
    "PROJECT-TOPLOOP-S3-EVAL-COMMAND-001":
        "text_formalization/general/flyspeck_eval_4.14.hl",
    "PROJECT-TOPLOOP-S3-SSREFLECT-LOOKUP-001":
        "jHOLLight/caml/ssreflect.hl",
}

DYNAMIC_MODULE = re.compile(r"\b(?:Toploop|Lexing|Obj)\s*\.")
UNBOUND_FORMAT = re.compile(
    r"\bFormat\s*\.\s*(?:formatter_of_buffer|pp_set_margin|sprintf|std_formatter)\b"
)


def executable_source(source: bytes) -> str:
    text = source.decode("utf-8")
    return flyspeck_manifest._code_mask(
        flyspeck_manifest.strip_ocaml_comments(text)
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument(
        "--contract", type=Path,
        default=Path(__file__).with_name(flyspeck_normalize.CONTRACT_NAME),
    )
    arguments = parser.parse_args()
    _, outputs = flyspeck_normalize.evaluate_contract(
        arguments.contract.resolve(), arguments.flyspeck_root.resolve(),
    )
    by_id = {str(entry["id"]): (entry, output) for entry, output in outputs}
    if set(ENTRY_PATHS) - set(by_id):
        raise SystemExit("missing selected toplevel normalization entry")
    for entry_id, expected_path in ENTRY_PATHS.items():
        entry, output = by_id[entry_id]
        if entry["path"] != expected_path:
            raise SystemExit(f"unexpected path for {entry_id}: {entry['path']}")
        code = executable_source(output)
        finding = DYNAMIC_MODULE.search(code) or UNBOUND_FORMAT.search(code)
        if finding:
            line = code.count("\n", 0, finding.start()) + 1
            raise SystemExit(
                f"selected dynamic compiler reference remains in {expected_path}:{line}"
            )

    serialization = by_id["PROJECT-MODULE-S3-SET-MAKE-001"][1]
    if serialization.count(
        b'#flyspeck_loadt "general/update_database_400.ml";;'
    ) != 1 or b'needs "general/update_database_310.ml"' in serialization:
        raise SystemExit("serialization branch is not the exact static 4.x action")

    update_database = by_id["PROJECT-TOPLOOP-S3-UPDATE-DATABASE-001"][1]
    for required in (
        b"let update_database () =",
        b"dynamic theorem-search database update is disabled",
        b"let candle_flyspeck_update_database_effect_elided = true;;",
        b"let search_thml term_matcher =",
    ):
        if update_database.count(required) != 1:
            raise SystemExit(f"update_database disposition drift: {required!r}")

    eval_source = by_id["PROJECT-TOPLOOP-S3-EVAL-COMMAND-001"][1]
    if eval_source.count(b"dynamic eval_command is disabled") != 1:
        raise SystemExit("eval_command is not fail closed")

    ssreflect = by_id["PROJECT-TOPLOOP-S3-SSREFLECT-LOOKUP-001"][1]
    if (
        ssreflect.count(b"dynamic test_id_thm is disabled") != 1
        or ssreflect.count(b"dynamic use_arg_then is disabled") != 1
        or ssreflect.count(b"let use_arg_then2") != 1
    ):
        raise SystemExit("ssreflect typed/dynamic lookup partition drift")

    print(
        "normalized toplevel route ok: "
        f"{len(ENTRY_PATHS)} sources, 0 selected dynamic compiler references"
    )


if __name__ == "__main__":
    main()
