#!/usr/bin/env python3
"""Independently check completeness of the Flyspeck float inventory.

Unlike ``flyspeck_float_corpus.scan_source``, this check delegates lexical
classification to OCaml 4.14.1's compiler-libs Lexer.  The OCaml helper omits
tokens between paired HOL backticks and reports every remaining FLOAT token
with its compiler location.  It also reports every skipped backtick span for
an explicit selected-source dialect fingerprint.  Exact site, spelling, file,
count, and quotation-span projections must match the authenticated contract.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import types
from typing import Any


HERE = Path(__file__).resolve().parent


def _load_local_source(name: str, path: Path):
    """Execute an exact local .py source without consulting bytecode caches."""
    source = path.read_bytes()
    source_sha256 = hashlib.sha256(source).hexdigest()
    existing = sys.modules.get(name)
    if existing is not None:
        if (getattr(existing, "__candle_source_sha256__", None) !=
                source_sha256 or
                Path(getattr(existing, "__file__", "")).resolve() != path):
            raise RuntimeError(f"untrusted preloaded local module: {name}")
        return existing
    module = types.ModuleType(name)
    module.__file__ = str(path)
    module.__package__ = ""
    module.__candle_source_sha256__ = source_sha256
    sys.modules[name] = module
    try:
        exec(compile(source, str(path), "exec", dont_inherit=True),
             module.__dict__)
    except BaseException:
        sys.modules.pop(name, None)
        raise
    return module


flyspeck_float_corpus = _load_local_source(
    "flyspeck_float_corpus", HERE / "flyspeck_float_corpus.py"
)


ORACLE_SOURCE = HERE / "ocaml_float_token_oracle.ml"
EXPECTED_ORACLE_SHA256 = (
    "cfd96ce14e3e95ea7414602501d1f001b665cbbcdce08e5e183c327f23b52f05"
)
EXPECTED_COMPILED_ORACLE = {
    "bytes": 2911680,
    "md5": "4314f8a71b037ee92d4036fed59806c7",
    "sha256":
        "b66c3433c012bf87bbce86c350aa60d31b3d8321900e6e1f557a4952e95261b9",
}
EXPECTED_COMPILED_OBJECTS = {
    "ocaml_float_token_oracle.cmi": {
        "bytes": 2154,
        "md5": "706e322a9e0a93455ddb73d5131e0223",
        "sha256":
            "0b2c659f3ac47135d71e16a3d903645a5d908c5f481f70d7f7d40150e800cdc3",
    },
    "ocaml_float_token_oracle.cmo": {
        "bytes": 6922,
        "md5": "be01e03ea70f93c48880c88d9062985e",
        "sha256":
            "24c16db0b80ebd1ca5207fd68c8a557233813d1baef551b7b5bc98546b102e34",
    },
}
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
    "camlheader": {
        "path": "/usr/lib/ocaml/camlheader",
        "bytes": 20,
        "sha256":
            "47df491b460b0a82ec1edc09a88eaf2cbaec029bf2b6c9c3ed49bfd33a89f7d0",
    },
    "camlinternalFormatBasics.cmi": {
        "path": "/usr/lib/ocaml/camlinternalFormatBasics.cmi",
        "bytes": 23317,
        "sha256":
            "00d6cbbec7953c16dfa1bd9d1e56d7b878f02f494dcdb80ebf4e9f0babc10732",
    },
    "location.cmi": {
        "path": "/usr/lib/ocaml/compiler-libs/location.cmi",
        "bytes": 11691,
        "sha256":
            "e47590c89033ef3562ec2b1429d1bbc5a3132659b5907f16fb76afc5681d4f43",
    },
    "warnings.cmi": {
        "path": "/usr/lib/ocaml/compiler-libs/warnings.cmi",
        "bytes": 9769,
        "sha256":
            "57af7b6cfbd2efb874bc0fabff3ae18d61156a4ae8ce6e1ce106950474f5b2b7",
    },
    "ld.conf": {
        "path": "/usr/lib/ocaml/ld.conf",
        "bytes": 61,
        "sha256":
            "510bf8efe88cdfcf8e3b5f9fc46b3a052bf49c05e055e40436e8d5cc0bb326de",
    },
    "std_exit.cmo": {
        "path": "/usr/lib/ocaml/std_exit.cmo",
        "bytes": 1864,
        "sha256":
            "26f2495297ffef09b02955a07c1d3494745d5a9e50f6afd4a5e7e81ab1ed96ca",
    },
    "stdlib.cma": {
        "path": "/usr/lib/ocaml/stdlib.cma",
        "bytes": 3491548,
        "sha256":
            "2a9edcdff005ffbcb95a5074cf1f89a2c4d3313c6ea0434e712922fa723921d4",
    },
    "stdlib.cmi": {
        "path": "/usr/lib/ocaml/stdlib.cmi",
        "bytes": 37533,
        "sha256":
            "93b68a73488046fd09bd469977acbc97925b28b2f16d097ac6b3a768609d4fcc",
    },
    "stdlib__Bytes.cmi": {
        "path": "/usr/lib/ocaml/stdlib__Bytes.cmi",
        "bytes": 16022,
        "sha256":
            "163cc02b2bc6ef4e58e7416ebd2647e6a2a7c6859a88847ec45ecce71df41b75",
    },
    "stdlib__Lexing.cmi": {
        "path": "/usr/lib/ocaml/stdlib__Lexing.cmi",
        "bytes": 4978,
        "sha256":
            "74b4dba28bd86c9de1ca495a772425c80c16d227dd9eb878a409fed77ee0435c",
    },
    "stdlib__Printf.cmi": {
        "path": "/usr/lib/ocaml/stdlib__Printf.cmi",
        "bytes": 2854,
        "sha256":
            "1be947816ecbce65f4320a53f321002344ed198f34a7d45535a087eb1aaeeac7",
    },
    "stdlib__String.cmi": {
        "path": "/usr/lib/ocaml/stdlib__String.cmi",
        "bytes": 12918,
        "sha256":
            "6594da5c8e6b628fecf5d0b627a4e9f399e073dfd4ffbcc382866b419cc923f0",
    },
    "ocamlrun": {
        "path": "/usr/bin/ocamlrun",
        "bytes": 338720,
        "sha256":
            "ecb7abaea5550b54d2caddffe3ca4932e1231afe32c3e3c39c75d49a740a6e8e",
    },
    "ld.so.cache": {
        "path": "/etc/ld.so.cache",
        "bytes": 50011,
        "sha256":
            "0971c6dfbc46998c25774d855b34d8494d78988f90221eb5fe5aa8816203fca1",
    },
    "libm.so.6": {
        "path": "/lib/x86_64-linux-gnu/libm.so.6",
        "bytes": 952616,
        "sha256":
            "e9c4b28d340e415b8137480ec442662f981e1399386c5931dae0e886e3639e91",
    },
    "libc.so.6": {
        "path": "/lib/x86_64-linux-gnu/libc.so.6",
        "bytes": 2125328,
        "sha256":
            "8db37cf3f2169f59a0f07ef1fea308c35656668c64c8ff294e1860f4121eb161",
    },
    "ld-linux-x86-64.so.2": {
        "path": "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
        "bytes": 236616,
        "sha256":
            "cd4df4f3c7b83673d61189bf2eaebd33ca4f2853ab9772b8a25e025ef99b1e81",
    },
}
EXPECTED_LOADER_ALIAS = {
    "path": "/lib64/ld-linux-x86-64.so.2",
    "symlink_target": "../lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
    "resolved_path": "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
    "bytes": 236616,
    "sha256":
        "cd4df4f3c7b83673d61189bf2eaebd33ca4f2853ab9772b8a25e025ef99b1e81",
}
PYTHON_SOURCE_PATHS = {
    "check_flyspeck_float_completeness.py": Path(__file__).resolve(),
    "flyspeck_float_corpus.py": Path(flyspeck_float_corpus.__file__).resolve(),
}
QUOTATION_DIALECT_POLICY = (
    "the exact authenticated selected graph treats every recorded paired "
    "backtick span as a HOL quotation; OCaml polymorphic variants are outside "
    "this direct-source dialect and any span/source change requires review"
)
EXPECTED_QUOTATION_SPAN_COUNT = 318_855
EXPECTED_QUOTATION_SPAN_SHA256 = (
    "c77a3aca5d71590637fd624b04e51f3ea4250591a4f693d338611647c9a606dd"
)


def _environment() -> dict[str, str]:
    flyspeck_float_corpus.require(
        not os.path.lexists("/etc/ld.so.preload"),
        "system-wide dynamic-loader preload is outside the oracle model",
    )
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
    alias_path = Path(EXPECTED_LOADER_ALIAS["path"])
    flyspeck_float_corpus.require(
        alias_path.is_symlink() and
        os.readlink(alias_path) == EXPECTED_LOADER_ALIAS["symlink_target"],
        "OCaml ELF interpreter alias mismatch",
    )
    alias_resolved = alias_path.resolve(strict=True)
    alias_record = flyspeck_float_corpus.file_record(alias_resolved)
    loader_alias = {
        "path": str(alias_path),
        "symlink_target": os.readlink(alias_path),
        "resolved_path": str(alias_resolved),
        "bytes": alias_record["bytes"],
        "sha256": alias_record["sha256"],
    }
    flyspeck_float_corpus.require(
        loader_alias == EXPECTED_LOADER_ALIAS,
        "OCaml ELF interpreter resolution mismatch",
    )
    return {
        "ocaml_version": version.stdout.strip(),
        "ocaml_where": str(EXPECTED_OCAML_WHERE),
        "files": observed,
        "loader_alias": loader_alias,
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
    flyspeck_float_corpus.require(
        flyspeck_float_corpus.file_record(executable) ==
        EXPECTED_COMPILED_ORACLE,
        "compiled independent OCaml lexer oracle identity mismatch",
    )
    for name, expected in EXPECTED_COMPILED_OBJECTS.items():
        flyspeck_float_corpus.require(
            flyspeck_float_corpus.file_record(output_root / name) == expected,
            f"compiled independent OCaml lexer object identity mismatch: {name}",
        )
    return executable


def oracle_observation(
    runtime_sources: list[dict[str, Any]],
    ocamlc: str,
) -> tuple[list[dict[str, Any]], dict[str, Any], list[dict[str, Any]]]:
    validated_toolchain = validate_toolchain(ocamlc)
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
        executable = compile_oracle(ocamlc, Path(tmp), validated_toolchain)
        toolchain = {
            **validated_toolchain,
            "compiled_oracle": flyspeck_float_corpus.file_record(executable),
            "compiled_objects": {
                name: flyspeck_float_corpus.file_record(Path(tmp) / name)
                for name in sorted(EXPECTED_COMPILED_OBJECTS)
            },
        }
        observed = subprocess.run(
            [str(executable)], input=oracle_input, check=False,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            env=_environment(),
        )
        flyspeck_float_corpus.require(
            validate_toolchain(ocamlc) == validated_toolchain,
            "OCaml lexer toolchain changed during independent observation",
        )
        flyspeck_float_corpus.require(
            flyspeck_float_corpus.file_record(executable) ==
            EXPECTED_COMPILED_ORACLE and
            all(
                flyspeck_float_corpus.file_record(Path(tmp) / name) == expected
                for name, expected in EXPECTED_COMPILED_OBJECTS.items()
            ),
            "compiled OCaml lexer artifacts changed during observation",
        )
    flyspeck_float_corpus.require(
        observed.returncode == 0,
        "independent OCaml lexer oracle failed: " + observed.stderr.strip(),
    )
    known_keys = {source["key"] for source in runtime_sources}
    sites = []
    quotations = []
    for line in observed.stdout.splitlines():
        fields = line.split("\t")
        flyspeck_float_corpus.require(fields, "empty independent lexer output")
        tag = fields[0]
        if tag == "F":
            flyspeck_float_corpus.require(
                len(fields) == 5,
                f"malformed independent float output: {line}",
            )
            _tag, key, line_text, column_text, literal = fields
        elif tag == "Q":
            flyspeck_float_corpus.require(
                len(fields) == 8,
                f"malformed independent quotation output: {line}",
            )
            (_tag, key, opening_line, opening_column, opening_byte,
             closing_line, closing_column, closing_byte) = fields
            flyspeck_float_corpus.require(
                key in known_keys and all(value.isdecimal() for value in (
                    opening_line, opening_column, opening_byte,
                    closing_line, closing_column, closing_byte,
                )),
                f"malformed independent quotation location: {line}",
            )
            quotation = {
                "source": key,
                "opening_line": int(opening_line),
                "opening_column": int(opening_column),
                "opening_byte": int(opening_byte),
                "closing_line": int(closing_line),
                "closing_column": int(closing_column),
                "closing_byte": int(closing_byte),
            }
            flyspeck_float_corpus.require(
                quotation["opening_byte"] < quotation["closing_byte"],
                f"empty or reversed independent quotation: {line}",
            )
            quotations.append(quotation)
            continue
        else:
            raise flyspeck_float_corpus.CorpusError(
                f"unknown independent lexer output tag: {line}"
            )
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
    quotations.sort(key=lambda quotation: (
        quotation["source"], quotation["opening_byte"],
        quotation["closing_byte"],
    ))
    return sites, toolchain, quotations


def oracle_sites(
    runtime_sources: list[dict[str, Any]],
    ocamlc: str,
) -> list[dict[str, Any]]:
    sites, _toolchain, _quotations = oracle_observation(runtime_sources, ocamlc)
    return sites


def selected_quotation_dialect(
    quotations: list[dict[str, Any]],
) -> dict[str, Any]:
    """Authenticate the explicit backtick interpretation for this graph."""
    record = {
        "policy": QUOTATION_DIALECT_POLICY,
        "paired_span_count": len(quotations),
        "span_record_sha256":
            flyspeck_float_corpus.canonical_sha256(quotations),
    }
    flyspeck_float_corpus.require(
        record == {
            "policy": QUOTATION_DIALECT_POLICY,
            "paired_span_count": EXPECTED_QUOTATION_SPAN_COUNT,
            "span_record_sha256": EXPECTED_QUOTATION_SPAN_SHA256,
        },
        "selected-source backtick dialect contract mismatch",
    )
    return record


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
    sites, toolchain, quotations = oracle_observation(runtime_sources, ocamlc)
    quotation_dialect = selected_quotation_dialect(quotations)
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
    for source in runtime_sources:
        snapshot = source.get("runtime_snapshot")
        flyspeck_float_corpus.require(
            isinstance(snapshot, dict),
            f"missing independent runtime snapshot record: {source['key']}",
        )
        flyspeck_float_corpus.validate_record(
            Path(source["runtime_path"]), snapshot,
            f"postflight independent runtime snapshot {source['key']}",
        )
    result = {
        "schema": 2,
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
        "python_sources": {
            label: {
                "path": str(path),
                **flyspeck_float_corpus.file_record(path),
            }
            for label, path in sorted(PYTHON_SOURCE_PATHS.items())
        },
        "quotation_dialect": quotation_dialect,
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
            "oracle_source", "python_sources", "quotation_dialect",
            "toolchain",
        },
        "malformed independent completeness result",
    )
    flyspeck_float_corpus.require(
        result["schema"] == 2 and
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
    expected_python_sources = {
        label: {
            "path": str(path),
            **flyspeck_float_corpus.file_record(path),
        }
        for label, path in sorted(PYTHON_SOURCE_PATHS.items())
    }
    flyspeck_float_corpus.require(
        result["python_sources"] == expected_python_sources,
        "independent completeness Python source identity mismatch",
    )
    flyspeck_float_corpus.require(
        result["quotation_dialect"] == {
            "policy": QUOTATION_DIALECT_POLICY,
            "paired_span_count": EXPECTED_QUOTATION_SPAN_COUNT,
            "span_record_sha256": EXPECTED_QUOTATION_SPAN_SHA256,
        },
        "independent completeness quotation dialect mismatch",
    )
    flyspeck_float_corpus.require(
        result["toolchain"] == {
            "ocaml_version": flyspeck_float_corpus.EXPECTED_OCAML_VERSION,
            "ocaml_where": str(EXPECTED_OCAML_WHERE),
            "files": EXPECTED_TOOLCHAIN,
            "loader_alias": EXPECTED_LOADER_ALIAS,
            "compiled_oracle": EXPECTED_COMPILED_ORACLE,
            "compiled_objects": EXPECTED_COMPILED_OBJECTS,
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
