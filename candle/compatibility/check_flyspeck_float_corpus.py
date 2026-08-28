#!/usr/bin/env python3
"""Run the authenticated 1,741-spelling Flyspeck float gate in Candle.

The host inventory and OCaml 4.14.1 observations are regenerated before a
linked Candle process starts.  A PASS requires every exact corpus spelling to
produce its pinned IEEE-754 word after the complete hol.ml insulation stack.
It remains a numeric compatibility gate, not theorem, S2, or S3 evidence.
"""

from __future__ import annotations

import argparse
import collections
import datetime as dt
import json
from pathlib import Path
import resource
import shutil
import sys
from typing import Any


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))

import cakeml_artifact_provenance
import flyspeck_float_corpus


CHUNK_SIZE = 100


def authenticated_artifact(
    candle_root: Path,
    flyspeck_root: Path,
    overlay_root: Path,
    ocamlc: str,
    artifact_path: Path,
) -> dict:
    manifest, runtime_sources = flyspeck_float_corpus.validate_inputs(
        candle_root, flyspeck_root, overlay_root
    )
    scan = flyspeck_float_corpus.scan_corpus(manifest, runtime_sources)
    generated = flyspeck_float_corpus.make_artifact(manifest, scan, ocamlc)
    flyspeck_float_corpus.validate_artifact_shape(generated)
    expected = flyspeck_float_corpus.load_object(
        artifact_path, "float-corpus artifact"
    )
    flyspeck_float_corpus.validate_artifact_shape(expected)
    flyspeck_float_corpus.require(
        flyspeck_float_corpus.json_bytes(generated) == artifact_path.read_bytes(),
        "float-corpus artifact differs from authenticated regeneration",
    )
    return expected


def candle_source(payload: dict, chunk_size: int = CHUNK_SIZE) -> str:
    flyspeck_float_corpus.validate_artifact_shape(payload)
    flyspeck_float_corpus.require(chunk_size > 0, "chunk size must be positive")
    spellings = payload["spellings"]
    lines = [
        "let rec candle_flyspeck_float_check cases =",
        "  match cases with",
        "  | [] -> 0",
        "  | (actual,expected)::rest ->",
        "      if Cake.Word64.toInt (Cake.Double.toWord actual) = expected then",
        "        1 + candle_flyspeck_float_check rest",
        '      else failwith "Flyspeck decimal-float word mismatch"',
        ";;",
    ]
    chunk_names = []
    for chunk_index, offset in enumerate(range(0, len(spellings), chunk_size)):
        chunk = spellings[offset:offset + chunk_size]
        name = f"candle_flyspeck_float_chunk_{chunk_index:03d}"
        chunk_names.append(name)
        lines.extend([
            f"let {name} =",
            "  candle_flyspeck_float_check [",
        ])
        for record in chunk:
            lines.append(
                f'    ({record["literal"]},'
                f'{record["ocaml_word64_decimal"]});'
            )
        lines.extend([
            "  ]",
            ";;",
        ])
    lines.extend([
        "let candle_flyspeck_float_checked =",
        "  " + " +\n  ".join(chunk_names),
        ";;",
        ("let () = if candle_flyspeck_float_checked = "
         f"{len(spellings)} then () else failwith "
         '"Flyspeck decimal-float corpus count mismatch"'),
        ";;",
        "let candle_flyspeck_float_corpus_passed = true;;",
    ])
    return "\n".join(lines) + "\n"


def validate_generated_source(payload: dict, source: str) -> None:
    observed = flyspeck_float_corpus.scan_source(
        "generated:flyspeck_float_corpus.ml", source.encode("ascii")
    )
    counts = collections.Counter(site["literal"] for site in observed["sites"])
    expected = collections.Counter(
        {record["literal"]: 1 for record in payload["spellings"]}
    )
    flyspeck_float_corpus.require(
        counts == expected,
        "generated Candle source does not contain every exact spelling once",
    )
    flyspeck_float_corpus.require(
        source.endswith("let candle_flyspeck_float_corpus_passed = true;;\n"),
        "generated Candle success witness is not final",
    )


def _expect_prompt(process, timeout: int) -> None:
    import pexpect

    index = process.expect([
        r"\n# ",
        r"\n(ERROR: .+)",
        r"\n(EXCEPTION: .+)",
        pexpect.TIMEOUT,
        pexpect.EOF,
    ], timeout=timeout)
    if index != 0:
        detail = (process.match.group(1) if index in (1, 2)
                  else "timeout" if index == 3 else "unexpected EOF")
        raise AssertionError(f"Candle did not reach its prompt: {detail}")


def _utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def _write_json(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8",
    )


def _ocaml_string(value: str) -> str:
    flyspeck_float_corpus.require(
        all(32 <= ord(character) < 127 for character in value),
        "evidence path contains a non-printable character",
    )
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def _archive_file(
    source: Path,
    destination: Path,
    expected: dict[str, Any] | None = None,
) -> dict[str, Any]:
    flyspeck_float_corpus.require(
        source.is_file() and not source.is_symlink() and
        not destination.exists() and not destination.is_symlink(),
        f"cannot archive ordinary evidence input: {source}",
    )
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
    observed = flyspeck_float_corpus.file_record(destination)
    if expected is not None:
        projection = {field: observed[field] for field in expected}
        flyspeck_float_corpus.require(
            projection == expected,
            f"archived evidence identity mismatch: {destination}",
        )
    destination.chmod(0o444)
    return observed


def check_candle(
    payload: dict,
    candle_root: Path,
    timeout: int,
    evidence_root: Path,
    artifact_path: Path,
) -> dict[str, Any]:
    try:
        import pexpect
    except ImportError as error:
        raise RuntimeError("compiled float corpus gate requires pexpect") from error

    candle_root = candle_root.resolve()
    launcher = candle_root / "candle.sh"
    flyspeck_float_corpus.require(
        launcher.is_file() and not launcher.is_symlink(),
        f"missing ordinary Candle launcher: {launcher}",
    )
    linked = cakeml_artifact_provenance.validate_linked_record(candle_root)
    runtime_env = cakeml_artifact_provenance.runtime_environment()
    source_text = candle_source(payload)
    validate_generated_source(payload, source_text)

    evidence_root = evidence_root.resolve()
    flyspeck_float_corpus.require(
        evidence_root.parent.is_dir() and not evidence_root.exists(),
        f"evidence output must be a new child of an existing directory: {evidence_root}",
    )
    evidence_root.mkdir()
    archive_root = evidence_root / "provenance"
    artifact_archive = archive_root / "flyspeck_float_corpus.json"
    artifact_archive_record = _archive_file(artifact_path, artifact_archive)
    linked_record_path = (
        candle_root / cakeml_artifact_provenance.LINKED_RECORD_RELATIVE
    )
    linked_archive = archive_root / "linked-provenance.json"
    linked_archive_record = _archive_file(linked_record_path, linked_archive)
    flyspeck_float_corpus.require(
        flyspeck_float_corpus.load_object(
            linked_archive, "archived linked provenance"
        ) == linked,
        "archived linked provenance differs from validated record",
    )
    build_dir = candle_root / "candle/build"
    bootstrap_archive = archive_root / "bootstrap-provenance.json"
    bootstrap_archive_record = _archive_file(
        build_dir / cakeml_artifact_provenance.LINKED_BOOTSTRAP_RECORD,
        bootstrap_archive, linked["bootstrap_record"],
    )
    bootstrap_log_archive = archive_root / "bootstrap.log"
    bootstrap_log_archive_record = _archive_file(
        build_dir / cakeml_artifact_provenance.LINKED_BOOTSTRAP_LOG,
        bootstrap_log_archive, linked["bootstrap_log"],
    )
    elf_archive_records = []
    for path_string, expected in sorted(
        linked["runtime_elf_closure"]["files"].items()
    ):
        source = Path(path_string)
        destination = (
            archive_root / "runtime-elf" /
            f"{expected['sha256'][:16]}-{source.name}"
        )
        elf_archive_records.append({
            "path": str(destination.relative_to(evidence_root)),
            **_archive_file(source, destination, expected),
        })
    source_path = evidence_root / "flyspeck_float_corpus.ml"
    source_path.write_text(source_text, encoding="ascii")
    source_path.chmod(0o444)
    transcript_path = evidence_root / "transcript.log"
    transcript = transcript_path.open("x+", encoding="utf-8")
    attempt_path = evidence_root / "attempt.json"
    receipt_path = evidence_root / "receipt.json"
    started = _utc_now()
    attempt = {
        "schema": 1,
        "kind": "compiled-candle-flyspeck-float-corpus-attempt",
        "claim": (
            "numeric compatibility attempt over every pinned direct-corpus "
            "decimal spelling; not theorem, S2, or S3 evidence"
        ),
        "state": "running",
        "started_utc": started,
        "timeout_seconds": timeout,
        "exact_spelling_count": len(payload["spellings"]),
        "runtime_environment": runtime_env,
        "command": [str(launcher)],
        "inputs": {
            "artifact": {
                "path": str(artifact_archive.relative_to(evidence_root)),
                **artifact_archive_record,
            },
            "generated_source": flyspeck_float_corpus.file_record(source_path),
            "linked_provenance": {
                "path": str(linked_archive.relative_to(evidence_root)),
                **linked_archive_record,
            },
            "bootstrap_provenance": {
                "path": str(bootstrap_archive.relative_to(evidence_root)),
                **bootstrap_archive_record,
            },
            "bootstrap_log": {
                "path": str(bootstrap_log_archive.relative_to(evidence_root)),
                **bootstrap_log_archive_record,
            },
            "runtime_elf_objects": elf_archive_records,
        },
        "repositories": {
            "candle": linked["candle_commit"],
            "cakeml": linked["cakeml_commit"],
            "hol4": linked["hol4_commit"],
            "flyspeck": flyspeck_float_corpus.EXPECTED_FLYSPECK_COMMIT,
        },
        "s2_s3_evidence": False,
    }
    _write_json(attempt_path, attempt)
    attempt_path.chmod(0o444)
    process = None
    passed = False
    failure: BaseException | None = None
    postflight_reauthenticated = False
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    try:
        process = pexpect.spawn(
            str(launcher), encoding="utf-8", logfile=transcript,
            cwd=str(candle_root), env=runtime_env,
        )
        _expect_prompt(process, timeout)
        process.send(
            '#use "hol.ml";;\n'
            'let candle_hol_load_complete = (check_axioms (); true);;\n'
        )
        loaded = process.expect([
            r"\n- Finished loading (?:\S*/)?hol\.ml",
            r"\n(ERROR: .+)",
            r"\n(Parsing failed)",
            r"\n(EXCEPTION: .+)",
            pexpect.TIMEOUT,
            pexpect.EOF,
        ], timeout=timeout)
        if loaded != 0:
            detail = (process.match.group(1) if loaded in (1, 2, 3)
                      else "timeout" if loaded == 4 else "unexpected EOF")
            raise AssertionError(f"Candle hol.ml EOF witness failed: {detail}")
        witness = process.expect([
            r"\nval candle_hol_load_complete = true",
            r"\n(ERROR: .+)",
            r"\n(Parsing failed)",
            r"\n(EXCEPTION: .+)",
            pexpect.TIMEOUT,
            pexpect.EOF,
        ], timeout=timeout)
        if witness != 0:
            detail = (process.match.group(1) if witness in (1, 2, 3)
                      else "timeout" if witness == 4 else "unexpected EOF")
            raise AssertionError(f"Candle hol.ml load failed: {detail}")
        _expect_prompt(process, timeout)
        process.sendline(f"#use {_ocaml_string(str(source_path))};;")
        result = process.expect([
            r"\nval candle_flyspeck_float_corpus_passed = true",
            r"\n(ERROR: .+)",
            r"\n(Parsing failed)",
            r"\n(EXCEPTION: .+)",
            pexpect.TIMEOUT,
            pexpect.EOF,
        ], timeout=timeout)
        if result != 0:
            detail = (process.match.group(1) if result in (1, 2, 3)
                      else "timeout" if result == 4 else "unexpected EOF")
            raise AssertionError(
                f"compiled Candle float corpus failed: {detail}"
            )
        _expect_prompt(process, timeout)
        process.sendeof()
        process.expect(pexpect.EOF, timeout=timeout)
        process.close()
        flyspeck_float_corpus.require(
            process.exitstatus == 0 and process.signalstatus is None,
            "compiled Candle float corpus process did not exit cleanly",
        )
        passed = True
    except BaseException as error:
        failure = error
    finally:
        if process is not None and process.isalive():
            process.close(force=True)
        transcript.close()
    transcript_path.chmod(0o444)

    try:
        post_linked = cakeml_artifact_provenance.validate_linked_record(candle_root)
        flyspeck_float_corpus.require(
            post_linked == linked, "linked provenance changed during corpus gate",
        )
        flyspeck_float_corpus.validate_record(
            source_path, attempt["inputs"]["generated_source"],
            "retained float-corpus source",
        )
        for label in ("artifact", "linked_provenance",
                      "bootstrap_provenance", "bootstrap_log"):
            archived = attempt["inputs"][label]
            flyspeck_float_corpus.validate_record(
                evidence_root / archived["path"],
                {field: archived[field] for field in ("bytes", "md5", "sha256")},
                f"retained {label}",
            )
        for archived in attempt["inputs"]["runtime_elf_objects"]:
            flyspeck_float_corpus.validate_record(
                evidence_root / archived["path"],
                {field: archived[field] for field in ("bytes", "md5", "sha256")},
                "retained runtime ELF object",
            )
        postflight_reauthenticated = True
    except BaseException as error:
        if failure is None:
            failure = error

    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    receipt = {
        **attempt,
        "state": "completed" if passed and failure is None else "failed",
        "finished_utc": _utc_now(),
        "compiled_pass": passed and failure is None,
        "postflight_reauthenticated": postflight_reauthenticated,
        "transcript": flyspeck_float_corpus.file_record(transcript_path),
        "child_resources": {
            "user_cpu_seconds": usage_after.ru_utime - usage_before.ru_utime,
            "system_cpu_seconds": usage_after.ru_stime - usage_before.ru_stime,
            "max_rss_kib": usage_after.ru_maxrss,
            "major_page_faults": usage_after.ru_majflt - usage_before.ru_majflt,
            "minor_page_faults": usage_after.ru_minflt - usage_before.ru_minflt,
        },
        "validation_error": None if failure is None else str(failure),
    }
    _write_json(receipt_path, receipt)
    receipt_path.chmod(0o444)
    if failure is not None:
        raise AssertionError(
            f"{failure}\nCandle evidence: {evidence_root}"
        ) from failure
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-root", required=True, type=Path)
    parser.add_argument("--flyspeck-root", required=True, type=Path)
    parser.add_argument("--overlay-root", required=True, type=Path)
    parser.add_argument("--ocamlc", default="/usr/bin/ocamlc")
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--artifact", type=Path)
    parser.add_argument("--write", required=True, type=Path,
                        metavar="EVIDENCE_ROOT")
    arguments = parser.parse_args()
    flyspeck_float_corpus.require(arguments.timeout > 0,
                                  "timeout must be positive")
    candle_root = arguments.candle_root.resolve()
    artifact_path = (arguments.artifact.resolve() if arguments.artifact else
                     candle_root / flyspeck_float_corpus.ARTIFACT_RELATIVE)
    payload = authenticated_artifact(
        candle_root, arguments.flyspeck_root.resolve(),
        arguments.overlay_root.resolve(), arguments.ocamlc, artifact_path,
    )
    check_candle(
        payload, candle_root, arguments.timeout, arguments.write,
        artifact_path,
    )
    print(
        "Compiled Candle Flyspeck decimal-float corpus PASS: "
        f"{len(payload['spellings'])} exact spellings match OCaml "
        f"{flyspeck_float_corpus.EXPECTED_OCAML_VERSION} Word64 observations"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except flyspeck_float_corpus.CorpusError as error:
        raise SystemExit(f"compiled float corpus gate failed: {error}") from error
