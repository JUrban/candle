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
from pathlib import Path
import sys
import tempfile


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))

import cakeml_artifact_provenance
import check_flyspeck_float_completeness
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
    check_flyspeck_float_completeness.validate_completeness(
        manifest, runtime_sources, expected, ocamlc
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


def check_candle(payload: dict, candle_root: Path, timeout: int) -> None:
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
    cakeml_artifact_provenance.validate_linked_record(candle_root)
    runtime_env = cakeml_artifact_provenance.runtime_environment()
    source_text = candle_source(payload)
    validate_generated_source(payload, source_text)

    transcript = tempfile.NamedTemporaryFile(
        mode="w+", encoding="utf-8", prefix="candle-flyspeck-floats-",
        suffix=".log", delete=False,
    )
    transcript_path = Path(transcript.name)
    process = None
    passed = False
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

        with tempfile.TemporaryDirectory(
            prefix="candle-flyspeck-float-source-"
        ) as tmp:
            source_path = Path(tmp) / "flyspeck_float_corpus.ml"
            source_path.write_text(source_text, encoding="ascii")
            process.sendline(f'#use "{source_path}";;')
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
        passed = True
    except Exception as error:
        transcript.flush()
        raise AssertionError(
            f"{error}\nCandle transcript: {transcript_path}"
        ) from error
    finally:
        if process is not None:
            process.close(force=True)
        transcript.close()
        if passed:
            transcript_path.unlink()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-root", required=True, type=Path)
    parser.add_argument("--flyspeck-root", required=True, type=Path)
    parser.add_argument("--overlay-root", required=True, type=Path)
    parser.add_argument("--ocamlc", default="/usr/bin/ocamlc")
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--artifact", type=Path)
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
    check_candle(payload, candle_root, arguments.timeout)
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
