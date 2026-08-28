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
    "915b89f64fc2d48c71e966d55f2d8b36440ee5efd49ca06d55c3afb012e6f8e2"
)


def _environment() -> dict[str, str]:
    return {"LC_ALL": "C", "PATH": "/usr/bin:/bin"}


def compile_oracle(ocamlc: str, output_root: Path) -> Path:
    version = subprocess.run(
        [ocamlc, "-version"], check=False, stdout=subprocess.PIPE,
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
        [ocamlc, "-I", "+compiler-libs", "ocamlcommon.cma",
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


def oracle_sites(
    runtime_sources: list[dict[str, Any]],
    ocamlc: str,
) -> list[dict[str, Any]]:
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
        executable = compile_oracle(ocamlc, Path(tmp))
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
    return sites


def validate_completeness(
    manifest: dict[str, Any],
    runtime_sources: list[dict[str, Any]],
    artifact: dict[str, Any],
    ocamlc: str,
) -> dict[str, Any]:
    """Validate the committed inventory without invoking its Python scanner."""
    flyspeck_float_corpus.validate_artifact_shape(artifact)
    sites = oracle_sites(runtime_sources, ocamlc)
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
    return {
        "occurrence_count": len(sites),
        "unique_spelling_count": len(unique),
        "source_file_count": len(independent_files),
        "site_record_sha256": site_digest,
        "unique_spelling_sha256":
            flyspeck_float_corpus.canonical_sha256(unique),
    }


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
    result = validate_completeness(
        manifest, runtime_sources, artifact, arguments.ocamlc
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
