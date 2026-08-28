#!/usr/bin/env python3
"""Independently check completeness of the Flyspeck float inventory.

Unlike ``flyspeck_float_corpus.scan_source``, this check delegates lexical
classification to OCaml 4.14.1's compiler-libs Lexer.  The OCaml helper omits
tokens between paired HOL backticks and reports every remaining FLOAT token
with its compiler location.  Exact site, spelling, file, and count projections
must match the committed authenticated artifact.
"""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Any


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import flyspeck_float_corpus


ORACLE_SOURCE = HERE / "ocaml_float_token_oracle.ml"
EXPECTED_ORACLE_SHA256 = (
    "353ceff1f34f233c1c37fa31785cd43425e2bc21febc0c8692d8fd391797911f"
)
EXPECTED_OCAML_WHERE = Path("/usr/lib/ocaml")
EXPECTED_TOOLCHAIN = {
    "ocamlc": {
        "path": "/usr/bin/ocamlc.opt",
        "bytes": 9289608,
        "sha256":
            "84825ef63ded23b445acd4ef399e1bb0a11081976da4741e1033c8569eaa2bd6",
    },
    "ocamlcommon.cma": {
        "path": "/usr/lib/ocaml/compiler-libs/ocamlcommon.cma",
        "bytes": 18084797,
        "sha256":
            "27ae12edbd6afcab7b5c1edb7faba6f0d2e9828c40d075cd422bec885816b07b",
    },
    "lexer.cmi": {
        "path": "/usr/lib/ocaml/compiler-libs/lexer.cmi",
        "bytes": 3049,
        "sha256":
            "ebe9f2a1c034bd74ede609bb1e8dbceef2828674af086841a4e852b243e469b1",
    },
    "parser.cmi": {
        "path": "/usr/lib/ocaml/compiler-libs/parser.cmi",
        "bytes": 18374,
        "sha256":
            "9b65fd945cb41b9d2f8ca208d765e882041e6fbdcb127bbfef48a576bee122c7",
    },
}


def _environment() -> dict[str, str]:
    return {"LC_ALL": "C", "PATH": "/usr/bin:/bin"}


def validate_toolchain(ocamlc: str) -> dict[str, Any]:
    executable_string = shutil.which(ocamlc, path="/usr/bin:/bin")
    flyspeck_float_corpus.require(
        executable_string is not None, f"cannot resolve OCaml compiler: {ocamlc}",
    )
    executable = Path(executable_string).resolve(strict=True)
    version = subprocess.run(
        [str(executable), "-version"], check=False, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, env=_environment(),
    )
    flyspeck_float_corpus.require(
        version.returncode == 0,
        f"cannot execute OCaml compiler: {version.stderr.strip()}",
    )
    flyspeck_float_corpus.require(
        version.stdout.strip() == flyspeck_float_corpus.EXPECTED_OCAML_VERSION,
        f"OCaml lexer version mismatch: {version.stdout.strip()}",
    )
    where = subprocess.run(
        [str(executable), "-where"], check=False, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, env=_environment(),
    )
    flyspeck_float_corpus.require(
        where.returncode == 0 and
        Path(where.stdout.strip()).resolve(strict=True) == EXPECTED_OCAML_WHERE,
        "OCaml standard-library root differs from the pinned lexer toolchain",
    )
    observed = {}
    for label, expected in EXPECTED_TOOLCHAIN.items():
        path = executable if label == "ocamlc" else Path(expected["path"])
        record = flyspeck_float_corpus.file_record(path)
        projection = {field: record[field] for field in ("bytes", "sha256")}
        flyspeck_float_corpus.require(
            str(path) == expected["path"] and projection == {
                field: expected[field] for field in ("bytes", "sha256")
            },
            f"OCaml lexer toolchain identity mismatch: {label}",
        )
        observed[label] = {"path": str(path), **projection}
    return {
        "ocaml_version": version.stdout.strip(),
        "ocaml_where": str(EXPECTED_OCAML_WHERE),
        "files": observed,
    }


def compile_oracle(
    ocamlc: str,
    output_root: Path,
    toolchain: dict[str, Any] | None = None,
) -> Path:
    toolchain = validate_toolchain(ocamlc) if toolchain is None else toolchain
    version = subprocess.run(
        [toolchain["files"]["ocamlc"]["path"], "-version"],
        check=False, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, env=_environment(),
    )
    flyspeck_float_corpus.require(
        version.returncode == 0,
        f"cannot execute OCaml compiler: {version.stderr.strip()}",
    )
    flyspeck_float_corpus.require(
        version.stdout.strip() == flyspeck_float_corpus.EXPECTED_OCAML_VERSION,
        f"OCaml lexer version mismatch: {version.stdout.strip()}",
    )
    flyspeck_float_corpus.require(
        flyspeck_float_corpus.sha256_file(ORACLE_SOURCE) ==
        EXPECTED_ORACLE_SHA256,
        "independent OCaml lexer oracle source digest mismatch",
    )
    copied_source = output_root / ORACLE_SOURCE.name
    shutil.copyfile(ORACLE_SOURCE, copied_source)
    executable = output_root / "ocaml_float_token_oracle"
    compiled = subprocess.run(
        [toolchain["files"]["ocamlc"]["path"],
         "-I", "+compiler-libs", "ocamlcommon.cma",
         copied_source.name, "-o", str(executable)],
        cwd=str(output_root), check=False, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, env=_environment(),
    )
    flyspeck_float_corpus.require(
        compiled.returncode == 0,
        "could not compile independent OCaml lexer oracle: " +
        compiled.stderr.strip(),
    )
    return executable


def oracle_observation(
    runtime_sources: list[dict[str, Any]],
    ocamlc: str,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    toolchain = validate_toolchain(ocamlc)
    records = []
    for source in runtime_sources:
        key = source["key"]
        path = str(source["runtime_path"])
        flyspeck_float_corpus.require(
            not any(character in key + path for character in "\t\r\n"),
            f"unsafe independent-oracle key/path: {key}",
        )
        records.append(f"{key}\t{path}")
    oracle_input = "\n".join(records) + "\n"
    with tempfile.TemporaryDirectory(
        prefix="candle-ocaml-float-lexer-"
    ) as tmp:
        executable = compile_oracle(ocamlc, Path(tmp), toolchain)
        observed = subprocess.run(
            [str(executable)], input=oracle_input, check=False,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            env=_environment(),
        )
    flyspeck_float_corpus.require(
        observed.returncode == 0,
        "independent OCaml lexer oracle failed: " + observed.stderr.strip(),
    )
    known_keys = {source["key"] for source in runtime_sources}
    sites = []
    for line in observed.stdout.splitlines():
        fields = line.split("\t")
        flyspeck_float_corpus.require(
            len(fields) == 4,
            f"malformed independent lexer output: {line}",
        )
        key, line_text, column_text, literal = fields
        flyspeck_float_corpus.require(
            key in known_keys, f"unknown independent lexer source: {key}",
        )
        flyspeck_float_corpus.require(
            line_text.isdecimal() and column_text.isdecimal(),
            f"malformed independent lexer location: {line}",
        )
        try:
            literal.encode("ascii")
        except UnicodeEncodeError as error:
            raise flyspeck_float_corpus.CorpusError(
                f"non-ASCII independent float lexeme: {literal}"
            ) from error
        sites.append({
            "source": key,
            "line": int(line_text),
            "column": int(column_text),
            "literal": literal,
        })
    sites.sort(key=lambda site: (
        site["source"], site["line"], site["column"], site["literal"]
    ))
    return sites, toolchain


def oracle_sites(
    runtime_sources: list[dict[str, Any]],
    ocamlc: str,
) -> list[dict[str, Any]]:
    sites, _toolchain = oracle_observation(runtime_sources, ocamlc)
    return sites


def snapshot_runtime_sources(
    runtime_sources: list[dict[str, Any]],
    output_root: Path,
) -> list[dict[str, Any]]:
    """Copy the once-authenticated bytes used by both independent scanners."""

    flyspeck_float_corpus.require(
        output_root.is_dir() and not any(output_root.iterdir()),
        "independent lexer snapshot directory must be new and empty",
    )
    snapshots = []
    for index, source in enumerate(runtime_sources):
        original = Path(source["runtime_path"])
        flyspeck_float_corpus.require(
            original.is_file() and not original.is_symlink(),
            f"independent lexer source is not ordinary: {source['key']}",
        )
        before = flyspeck_float_corpus.file_record(original)
        flyspeck_float_corpus.require(
            before["sha256"] == source["runtime_sha256"],
            f"independent lexer source changed before snapshot: {source['key']}",
        )
        destination = output_root / f"source-{index:03d}.ml"
        shutil.copyfile(original, destination)
        copied = flyspeck_float_corpus.file_record(destination)
        after = flyspeck_float_corpus.file_record(original)
        flyspeck_float_corpus.require(
            copied == before and after == before,
            f"independent lexer source changed during snapshot: {source['key']}",
        )
        destination.chmod(0o444)
        snapshots.append({
            **source,
            "runtime_path": destination,
            "runtime_snapshot": copied,
        })
    return snapshots


def validate_completeness(
    manifest: dict[str, Any],
    runtime_sources: list[dict[str, Any]],
    artifact: dict[str, Any],
    ocamlc: str,
) -> dict[str, Any]:
    """Validate the committed inventory without invoking its Python scanner."""
    flyspeck_float_corpus.validate_artifact_shape(artifact)
    sites, toolchain = oracle_observation(runtime_sources, ocamlc)
    strata = [record["name"] for record in manifest["build_strata"]]
    stratum_rank = {name: index for index, name in enumerate(strata)}
    for site in sites:
        source_strata = manifest["source_node_strata"].get(site["source"])
        flyspeck_float_corpus.require(
            isinstance(source_strata, list) and source_strata,
            f"missing independent source stratum: {site['source']}",
        )
        site["earliest_stratum"] = min(
            source_strata, key=stratum_rank.__getitem__
        )
    site_digest = flyspeck_float_corpus.canonical_sha256(sites)
    inventory = artifact["inventory"]
    flyspeck_float_corpus.require(
        len(sites) == inventory["occurrence_count"],
        "independent OCaml lexer occurrence count mismatch",
    )
    flyspeck_float_corpus.require(
        site_digest == inventory["site_record_sha256"],
        "independent OCaml lexer site digest mismatch",
    )

    literal_counts = collections.Counter(site["literal"] for site in sites)
    unique = sorted(literal_counts)
    flyspeck_float_corpus.require(
        len(unique) == inventory["unique_spelling_count"],
        "independent OCaml lexer unique-spelling count mismatch",
    )
    flyspeck_float_corpus.require(
        flyspeck_float_corpus.canonical_sha256(unique) ==
        inventory["unique_spelling_sha256"],
        "independent OCaml lexer unique-spelling digest mismatch",
    )

    artifact_spellings = {record["literal"]: record
                          for record in artifact["spellings"]}
    flyspeck_float_corpus.require(
        set(literal_counts) == set(artifact_spellings),
        "independent OCaml lexer spelling set mismatch",
    )
    source_sets: dict[str, set[str]] = collections.defaultdict(set)
    for site in sites:
        source_sets[site["literal"]].add(site["source"])
    for literal, count in literal_counts.items():
        record = artifact_spellings[literal]
        flyspeck_float_corpus.require(
            record["occurrence_count"] == count and
            record["sources"] == sorted(source_sets[literal]) and
            record["source_count"] == len(source_sets[literal]),
            f"independent OCaml lexer spelling projection mismatch: {literal}",
        )

    runtime_by_key = {source["key"]: source for source in runtime_sources}
    sites_by_key: dict[str, list[dict[str, Any]]] = collections.defaultdict(list)
    for site in sites:
        sites_by_key[site["source"]].append(site)
    independent_files = []
    for key, source_sites in sorted(sites_by_key.items()):
        source = runtime_by_key[key]
        source_strata = manifest["source_node_strata"][key]
        independent_files.append({
            "source": key,
            "path": source["path"],
            "earliest_stratum": min(
                source_strata, key=stratum_rank.__getitem__
            ),
            "occurrence_count": len(source_sites),
            "unique_spelling_count": len({
                site["literal"] for site in source_sites
            }),
            "original_sha256": source["original_sha256"],
            "runtime_sha256": source["runtime_sha256"],
            "normalized": source["normalized"],
        })
    flyspeck_float_corpus.require(
        independent_files == inventory["files"],
        "independent OCaml lexer file projection mismatch",
    )
    result = {
        "schema": 1,
        "kind": "flyspeck-independent-float-completeness",
        "claim": "host/source completeness only; not compiled, S2, or S3 evidence",
        "occurrence_count": len(sites),
        "unique_spelling_count": len(unique),
        "source_file_count": len(independent_files),
        "site_record_sha256": site_digest,
        "unique_spelling_sha256":
            flyspeck_float_corpus.canonical_sha256(unique),
        "oracle_source": {
            "path": str(ORACLE_SOURCE),
            **flyspeck_float_corpus.file_record(ORACLE_SOURCE),
        },
        "toolchain": toolchain,
    }
    validate_completeness_result(result, artifact)
    return result


def validate_completeness_result(
    result: dict[str, Any],
    artifact: dict[str, Any],
) -> None:
    flyspeck_float_corpus.require(
        set(result) == {
            "schema", "kind", "claim", "occurrence_count",
            "unique_spelling_count", "source_file_count",
            "site_record_sha256", "unique_spelling_sha256",
            "oracle_source", "toolchain",
        },
        "malformed independent completeness result",
    )
    flyspeck_float_corpus.require(
        result["schema"] == 1 and
        result["kind"] == "flyspeck-independent-float-completeness" and
        result["claim"] ==
        "host/source completeness only; not compiled, S2, or S3 evidence",
        "independent completeness result claim/schema mismatch",
    )
    inventory = artifact["inventory"]
    flyspeck_float_corpus.require(
        result["occurrence_count"] == inventory["occurrence_count"] and
        result["unique_spelling_count"] ==
        inventory["unique_spelling_count"] and
        result["source_file_count"] == len(inventory["files"]) and
        result["site_record_sha256"] == inventory["site_record_sha256"] and
        result["unique_spelling_sha256"] ==
        inventory["unique_spelling_sha256"],
        "independent completeness result differs from corpus artifact",
    )
    expected_oracle = flyspeck_float_corpus.file_record(ORACLE_SOURCE)
    flyspeck_float_corpus.require(
        result["oracle_source"] == {
            "path": str(ORACLE_SOURCE), **expected_oracle,
        } and expected_oracle["sha256"] == EXPECTED_ORACLE_SHA256,
        "independent completeness oracle identity mismatch",
    )
    flyspeck_float_corpus.require(
        result["toolchain"] == {
            "ocaml_version": flyspeck_float_corpus.EXPECTED_OCAML_VERSION,
            "ocaml_where": str(EXPECTED_OCAML_WHERE),
            "files": EXPECTED_TOOLCHAIN,
        },
        "independent completeness toolchain identity mismatch",
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-root", required=True, type=Path)
    parser.add_argument("--flyspeck-root", required=True, type=Path)
    parser.add_argument("--overlay-root", required=True, type=Path)
    parser.add_argument("--ocamlc", default="/usr/bin/ocamlc")
    parser.add_argument("--artifact", type=Path)
    arguments = parser.parse_args()
    candle_root = arguments.candle_root.resolve()
    artifact_path = (arguments.artifact.resolve() if arguments.artifact else
                     candle_root / flyspeck_float_corpus.ARTIFACT_RELATIVE)
    manifest, runtime_sources = flyspeck_float_corpus.validate_inputs(
        candle_root, arguments.flyspeck_root, arguments.overlay_root
    )
    artifact = flyspeck_float_corpus.load_object(
        artifact_path, "float-corpus artifact"
    )
    with tempfile.TemporaryDirectory(
        prefix="candle-float-completeness-snapshot-"
    ) as temporary:
        snapshots = snapshot_runtime_sources(
            runtime_sources, Path(temporary),
        )
        result = validate_completeness(
            manifest, snapshots, artifact, arguments.ocamlc
        )
    print(
        "Independent OCaml lexer completeness PASS: "
        f"{result['occurrence_count']} occurrences, "
        f"{result['unique_spelling_count']} exact spellings, "
        f"{result['source_file_count']} runtime files"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except flyspeck_float_corpus.CorpusError as error:
        raise SystemExit(f"independent float completeness failed: {error}") from error
