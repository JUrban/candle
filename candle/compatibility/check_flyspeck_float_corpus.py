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
import hashlib
import importlib
import json
from pathlib import Path
import resource
import shutil
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
    module.__candle_source_bytes__ = source
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
cakeml_artifact_provenance = _load_local_source(
    "cakeml_artifact_provenance", HERE.parent / "cakeml_artifact_provenance.py"
)
runtime_lock = _load_local_source(
    "runtime_lock", HERE.parent / "runtime_lock.py"
)
check_flyspeck_float_completeness = _load_local_source(
    "check_flyspeck_float_completeness",
    HERE / "check_flyspeck_float_completeness.py",
)
RUNNER_SOURCE_BYTES = Path(__file__).read_bytes()


CHUNK_SIZE = 100
EXPECTED_PYTHON_RUNTIME = {
    "execution_binding": "/proc/self/exe",
    "version": (
        "3.12.3 (main, Jun 19 2026, 12:46:00) [GCC 13.3.0]"
    ),
    "executable": {
        "path": "/usr/bin/python3.12",
        "bytes": 8020928,
        "sha256":
            "1643dacd9feaedc58f3cc581e4d22577dfe25c09b10282936186ccf0f2e61118",
    },
    "elf_closure": {
        "policy": "ldd_roles_resolved_absolute_paths_and_content_v2",
        "files": {
            "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2": {
                "bytes": 236616,
                "sha256":
                    "cd4df4f3c7b83673d61189bf2eaebd33ca4f2853ab9772b8a25e025ef99b1e81",
            },
            "/lib/x86_64-linux-gnu/libc.so.6": {
                "bytes": 2125328,
                "sha256":
                    "8db37cf3f2169f59a0f07ef1fea308c35656668c64c8ff294e1860f4121eb161",
            },
            "/lib/x86_64-linux-gnu/libexpat.so.1.9.1": {
                "bytes": 174336,
                "sha256":
                    "c42ff317838b4b4639e2ea801905f0317177c6df7e31b2f0d0240e3c3ac0cfde",
            },
            "/lib/x86_64-linux-gnu/libm.so.6": {
                "bytes": 952616,
                "sha256":
                    "e9c4b28d340e415b8137480ec442662f981e1399386c5931dae0e886e3639e91",
            },
            "/lib/x86_64-linux-gnu/libz.so.1.3": {
                "bytes": 113000,
                "sha256":
                    "9b64150b28505a33d6bc3ecf709c279f6de97a1c184dbda65d06ee4537f6d286",
            },
        },
        "roles": {
            "ld-linux-x86-64.so.2":
                "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
            "libc.so.6": "/lib/x86_64-linux-gnu/libc.so.6",
            "libexpat.so.1": "/lib/x86_64-linux-gnu/libexpat.so.1.9.1",
            "libm.so.6": "/lib/x86_64-linux-gnu/libm.so.6",
            "libz.so.1": "/lib/x86_64-linux-gnu/libz.so.1.3",
        },
        "virtual_objects": ["linux-vdso.so.1"],
    },
}
EXPECTED_PEXPECT_SOURCES = {
    "pexpect": {
        "path": "/usr/lib/python3/dist-packages/pexpect/__init__.py",
        "bytes": 4089,
        "sha256":
            "4ae418ce9571a73a8bc19d5febca2fe53bdccbc42ffde0f5fcdcae4880e26da5",
    },
    "pexpect.exceptions": {
        "path": "/usr/lib/python3/dist-packages/pexpect/exceptions.py",
        "bytes": 1068,
        "sha256":
            "03d0b53d66c17368fd00abe7bfb5243c26b08454c419899e50b5b4bf06ccbd74",
    },
    "pexpect.expect": {
        "path": "/usr/lib/python3/dist-packages/pexpect/expect.py",
        "bytes": 13827,
        "sha256":
            "28ab419b1d8c61afb20c4ef5e5794751c96829ee677410f7e7d6b83985570fce",
    },
    "pexpect.pty_spawn": {
        "path": "/usr/lib/python3/dist-packages/pexpect/pty_spawn.py",
        "bytes": 37382,
        "sha256":
            "67281262c767549e5a73188d33d80bbcbad3d8056a83026f6c370f693c71bfd1",
    },
    "pexpect.run": {
        "path": "/usr/lib/python3/dist-packages/pexpect/run.py",
        "bytes": 6629,
        "sha256":
            "3e44c0fc818e1f32d52bcf6d548ce92c9ec8da300d379a3b183707e64d4bcbc7",
    },
    "pexpect.spawnbase": {
        "path": "/usr/lib/python3/dist-packages/pexpect/spawnbase.py",
        "bytes": 21685,
        "sha256":
            "493864410db9c22480fbbbaabde2f785b912f059cb1407e4fa25e05f63ad398f",
    },
    "pexpect.utils": {
        "path": "/usr/lib/python3/dist-packages/pexpect/utils.py",
        "bytes": 6019,
        "sha256":
            "d63221cd4ede06f637a5b5b72d9a09842394d8a5aa82dcb91e043a541608a795",
    },
    "ptyprocess": {
        "path": "/usr/lib/python3/dist-packages/ptyprocess/__init__.py",
        "bytes": 138,
        "sha256":
            "b27f96ff59cd453b883a2d9a0841d52f4eb009525c47e2ce65d8295f3c05b935",
    },
    "ptyprocess.ptyprocess": {
        "path": "/usr/lib/python3/dist-packages/ptyprocess/ptyprocess.py",
        "bytes": 31686,
        "sha256":
            "b24dac536236d98ca5d60537163166a562f7078de8d0aa86ddddc223caf436af",
    },
    "ptyprocess.util": {
        "path": "/usr/lib/python3/dist-packages/ptyprocess/util.py",
        "bytes": 2785,
        "sha256":
            "ad001d0d165fa0e88e9fabf2916b61d3023a145280a7b689b4149db7e28159d5",
    },
}


def validate_python_runtime() -> dict[str, Any]:
    process_executable = Path("/proc/self/exe")
    flyspeck_float_corpus.require(
        process_executable.is_symlink(),
        "cannot bind the executing Python image through /proc/self/exe",
    )
    executable = process_executable.resolve(strict=True)
    flyspeck_float_corpus.require(
        Path(sys.executable).resolve(strict=True) == executable,
        "Python executable metadata differs from the running image",
    )
    executable_record = flyspeck_float_corpus.file_record(executable)
    observed = {
        "execution_binding": "/proc/self/exe",
        "version": sys.version,
        "executable": {
            "path": str(executable),
            "bytes": executable_record["bytes"],
            "sha256": executable_record["sha256"],
        },
        "elf_closure":
            cakeml_artifact_provenance.elf_dynamic_closure(executable),
    }
    flyspeck_float_corpus.require(
        observed == EXPECTED_PYTHON_RUNTIME,
        "compiled corpus Python runtime identity mismatch",
    )
    return observed


def load_pexpect_from_pinned_sources(snapshot_root: Path):
    prefixes = ("pexpect", "ptyprocess")
    flyspeck_float_corpus.require(
        not any(
            name == prefix or name.startswith(prefix + ".")
            for name in sys.modules for prefix in prefixes
        ),
        "pexpect/ptyprocess were loaded before isolated source validation",
    )
    flyspeck_float_corpus.require(
        not snapshot_root.exists() and not snapshot_root.is_symlink(),
        "pexpect source snapshot must be a new path",
    )
    snapshot_root.mkdir(parents=True)
    for name, expected in sorted(EXPECTED_PEXPECT_SOURCES.items()):
        source = Path(expected["path"])
        source_record = flyspeck_float_corpus.file_record(source)
        flyspeck_float_corpus.require(
            {field: source_record[field] for field in ("bytes", "sha256")} ==
            {field: expected[field] for field in ("bytes", "sha256")},
            f"pexpect source changed before snapshot: {name}",
        )
        parts = name.split(".")
        destination = (
            snapshot_root / parts[0] /
            ("__init__.py" if len(parts) == 1 else f"{parts[-1]}.py")
        )
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(source.read_bytes())
        flyspeck_float_corpus.require(
            flyspeck_float_corpus.file_record(destination) == source_record,
            f"pexpect source changed during snapshot: {name}",
        )
        destination.chmod(0o444)
    with tempfile.TemporaryDirectory(
        prefix="candle-empty-python-cache-"
    ) as temporary:
        previous_prefix = sys.pycache_prefix
        previous_dont_write = sys.dont_write_bytecode
        sys.pycache_prefix = temporary
        sys.dont_write_bytecode = True
        sys.path.insert(0, str(snapshot_root))
        try:
            pexpect = importlib.import_module("pexpect")
            loaded_names = {
                name for name in sys.modules
                if any(
                    name == prefix or name.startswith(prefix + ".")
                    for prefix in prefixes
                )
            }
            flyspeck_float_corpus.require(
                loaded_names == set(EXPECTED_PEXPECT_SOURCES),
                "unexpected pexpect/ptyprocess module set",
            )
            observed = {}
            cache_root = Path(temporary)
            for name in sorted(loaded_names):
                module = sys.modules[name]
                source = Path(module.__file__).resolve(strict=True)
                cached = Path(module.__cached__).resolve()
                flyspeck_float_corpus.require(
                    cached.is_relative_to(cache_root) and
                    source.is_relative_to(snapshot_root) and
                    source.suffix == ".py",
                    f"Python package did not load from isolated source: {name}",
                )
                record = flyspeck_float_corpus.file_record(source)
                observed[name] = {
                    "path": str(source),
                    "bytes": record["bytes"],
                    "sha256": record["sha256"],
                }
            flyspeck_float_corpus.require(
                all(
                    {field: observed[name][field]
                     for field in ("bytes", "sha256")} ==
                    {field: expected[field]
                     for field in ("bytes", "sha256")}
                    for name, expected in EXPECTED_PEXPECT_SOURCES.items()
                ),
                "pexpect/ptyprocess source identity mismatch",
            )
        finally:
            if sys.path[0] == str(snapshot_root):
                sys.path.pop(0)
            sys.pycache_prefix = previous_prefix
            sys.dont_write_bytecode = previous_dont_write
    return pexpect, observed


def local_python_source_records(
    completeness: dict[str, Any],
) -> dict[str, dict[str, Any]]:
    records = dict(completeness["python_sources"])
    for module in local_python_modules():
        path = Path(module.__file__).resolve()
        source = module.__candle_source_bytes__
        record = {
            "path": str(path),
            **data_record(source),
        }
        flyspeck_float_corpus.require(
            module.__candle_source_sha256__ == record["sha256"] and
            hashlib.sha256(source).hexdigest() == record["sha256"] and
            flyspeck_float_corpus.file_record(path) ==
            {field: record[field]
             for field in ("bytes", "md5", "sha256")},
            f"executed local Python source identity mismatch: {path.name}",
        )
        records[path.name] = record
    runner = Path(__file__).resolve()
    records[runner.name] = {
        "path": str(runner),
        **data_record(RUNNER_SOURCE_BYTES),
    }
    flyspeck_float_corpus.require(
        flyspeck_float_corpus.file_record(runner) == {
            field: records[runner.name][field]
            for field in ("bytes", "md5", "sha256")
        },
        "top-level runner source changed after startup capture",
    )
    flyspeck_float_corpus.require(
        set(records) == {
            "cakeml_artifact_provenance.py",
            "check_flyspeck_float_completeness.py",
            "check_flyspeck_float_corpus.py",
            "flyspeck_float_corpus.py",
            "runtime_lock.py",
        },
        "unexpected local Python orchestration source set",
    )
    return records


def local_python_modules() -> tuple[types.ModuleType, ...]:
    return (
        cakeml_artifact_provenance,
        check_flyspeck_float_completeness,
        flyspeck_float_corpus,
        runtime_lock,
    )


def data_record(value: bytes) -> dict[str, Any]:
    return {
        "bytes": len(value),
        "md5": hashlib.md5(value, usedforsecurity=False).hexdigest(),
        "sha256": hashlib.sha256(value).hexdigest(),
    }


def local_python_source_bytes() -> dict[str, bytes]:
    sources = {
        Path(module.__file__).name: module.__candle_source_bytes__
        for module in local_python_modules()
    }
    sources[Path(__file__).name] = RUNNER_SOURCE_BYTES
    return sources


def authenticated_artifact(
    candle_root: Path,
    flyspeck_root: Path,
    overlay_root: Path,
    ocamlc: str,
    artifact_path: Path,
) -> tuple[dict, dict[str, Any]]:
    python_runtime = validate_python_runtime()
    manifest, runtime_sources = flyspeck_float_corpus.validate_inputs(
        candle_root, flyspeck_root, overlay_root
    )
    with tempfile.TemporaryDirectory(
        prefix="candle-float-corpus-snapshot-"
    ) as temporary:
        snapshots = (
            check_flyspeck_float_completeness.snapshot_runtime_sources(
                runtime_sources, Path(temporary),
            )
        )
        scan = flyspeck_float_corpus.scan_corpus(manifest, snapshots)
        generated = flyspeck_float_corpus.make_artifact(manifest, scan, ocamlc)
        flyspeck_float_corpus.validate_artifact_shape(generated)
        expected = flyspeck_float_corpus.load_object(
            artifact_path, "float-corpus artifact"
        )
        flyspeck_float_corpus.validate_artifact_shape(expected)
        flyspeck_float_corpus.require(
            flyspeck_float_corpus.json_bytes(generated) ==
            artifact_path.read_bytes(),
            "float-corpus artifact differs from authenticated regeneration",
        )
        completeness = (
            check_flyspeck_float_completeness.validate_completeness(
                manifest, snapshots, expected, ocamlc,
            )
        )
    flyspeck_float_corpus.require(
        validate_python_runtime() == python_runtime,
        "Python runtime changed during corpus authentication",
    )
    return expected, completeness


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


def _archive_bytes(
    value: bytes,
    destination: Path,
    expected: dict[str, Any],
) -> dict[str, Any]:
    flyspeck_float_corpus.require(
        not destination.exists() and not destination.is_symlink(),
        f"cannot archive new byte evidence: {destination}",
    )
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(value)
    observed = flyspeck_float_corpus.file_record(destination)
    flyspeck_float_corpus.require(
        {field: observed[field] for field in expected} == expected,
        f"archived byte evidence identity mismatch: {destination}",
    )
    destination.chmod(0o444)
    return observed


def check_candle(
    payload: dict,
    candle_root: Path,
    timeout: int,
    evidence_root: Path,
    artifact_path: Path,
    completeness: dict[str, Any],
) -> dict[str, Any]:
    try:
        python_runtime = validate_python_runtime()
    except (ImportError, flyspeck_float_corpus.CorpusError) as error:
        raise RuntimeError(
            "compiled float corpus gate requires the pinned Python runtime"
        ) from error

    candle_root = candle_root.resolve()
    runtime_lock_handle = runtime_lock.acquire_build_lock(candle_root)
    check_flyspeck_float_completeness.validate_completeness_result(
        completeness, payload,
    )
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
    try:
        pexpect, pexpect_sources = load_pexpect_from_pinned_sources(
            archive_root / "python-packages"
        )
    except (ImportError, flyspeck_float_corpus.CorpusError) as error:
        raise RuntimeError(
            "compiled float corpus gate requires pinned pexpect sources"
        ) from error
    artifact_archive = archive_root / "flyspeck_float_corpus.json"
    expected_artifact_bytes = flyspeck_float_corpus.json_bytes(payload)
    flyspeck_float_corpus.require(
        artifact_path.read_bytes() == expected_artifact_bytes,
        "float-corpus artifact changed before evidence archival",
    )
    artifact_archive_record = _archive_file(
        artifact_path, artifact_archive,
        flyspeck_float_corpus.file_record(artifact_path),
    )
    flyspeck_float_corpus.require(
        artifact_archive.read_bytes() == expected_artifact_bytes and
        flyspeck_float_corpus.load_object(
            artifact_archive, "archived float-corpus artifact"
        ) == payload,
        "archived float-corpus artifact differs from executed payload",
    )
    completeness_path = evidence_root / "independent-completeness.json"
    _write_json(completeness_path, completeness)
    completeness_record = flyspeck_float_corpus.file_record(completeness_path)
    flyspeck_float_corpus.require(
        flyspeck_float_corpus.load_object(
            completeness_path, "independent completeness result"
        ) == completeness,
        "retained independent completeness result changed on write",
    )
    completeness_path.chmod(0o444)
    oracle_record = completeness["oracle_source"]
    oracle_archive = archive_root / "ocaml_float_token_oracle.ml"
    oracle_archive_record = _archive_file(
        Path(oracle_record["path"]), oracle_archive,
        {field: oracle_record[field]
         for field in ("bytes", "md5", "sha256")},
    )
    python_source_archive_records = []
    python_sources = local_python_source_records(completeness)
    python_source_bytes = local_python_source_bytes()
    for label, record in sorted(python_sources.items()):
        destination = archive_root / "python" / label
        python_source_archive_records.append({
            "label": label,
            "source_path": record["path"],
            "path": str(destination.relative_to(evidence_root)),
            **_archive_bytes(
                python_source_bytes[label], destination,
                {field: record[field]
                 for field in ("bytes", "md5", "sha256")},
            ),
        })
    python_executable_record = python_runtime["executable"]
    python_executable_archive = archive_root / "python-runtime" / "python3.12"
    python_executable_archive_record = _archive_file(
        Path(python_executable_record["path"]), python_executable_archive,
        {field: python_executable_record[field]
         for field in ("bytes", "sha256")},
    )
    python_elf_archive_records = []
    for path_string, expected in sorted(
        python_runtime["elf_closure"]["files"].items()
    ):
        source = Path(path_string)
        destination = (
            archive_root / "python-runtime-elf" /
            f"{expected['sha256'][:16]}-{source.name}"
        )
        python_elf_archive_records.append({
            "source_path": path_string,
            "path": str(destination.relative_to(evidence_root)),
            **_archive_file(source, destination, expected),
        })
    pexpect_archive_records = []
    for label, record in sorted(pexpect_sources.items()):
        retained = Path(record["path"])
        retained_record = flyspeck_float_corpus.file_record(retained)
        pexpect_archive_records.append({
            "label": label,
            "source_path": EXPECTED_PEXPECT_SOURCES[label]["path"],
            "path": str(retained.relative_to(evidence_root)),
            **retained_record,
        })
    toolchain_archive_records = []
    for label, record in sorted(completeness["toolchain"]["files"].items()):
        destination = archive_root / "ocaml-toolchain" / label
        toolchain_archive_records.append({
            "label": label,
            "source_path": record["path"],
            "path": str(destination.relative_to(evidence_root)),
            **_archive_file(
                Path(record["path"]), destination,
                {field: record[field] for field in ("bytes", "sha256")},
            ),
        })
    with tempfile.TemporaryDirectory(
        prefix="candle-retained-ocaml-float-oracle-"
    ) as temporary:
        observed_toolchain = (
            check_flyspeck_float_completeness.validate_toolchain(
                completeness["toolchain"]["files"]["ocamlc"]["path"]
            )
        )
        flyspeck_float_corpus.require(
            observed_toolchain == {
                field: completeness["toolchain"][field]
                for field in (
                    "ocaml_version", "ocaml_where", "files", "loader_alias"
                )
            },
            "retained oracle compilation toolchain changed",
        )
        compiled_oracle = (
            check_flyspeck_float_completeness.compile_oracle(
                completeness["toolchain"]["files"]["ocamlc"]["path"],
                Path(temporary), observed_toolchain,
            )
        )
        compiled_oracle_archive = (
            archive_root / "ocaml_float_token_oracle.byte"
        )
        compiled_oracle_archive_record = _archive_file(
            compiled_oracle, compiled_oracle_archive,
            completeness["toolchain"]["compiled_oracle"],
        )
        compiled_object_archive_records = []
        for name, expected in sorted(
            completeness["toolchain"]["compiled_objects"].items()
        ):
            destination = archive_root / "ocaml-compile-outputs" / name
            compiled_object_archive_records.append({
                "name": name,
                "path": str(destination.relative_to(evidence_root)),
                **_archive_file(Path(temporary) / name, destination, expected),
            })
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
        "runtime_lock": runtime_lock_handle.record,
        "command": [str(launcher)],
        "inputs": {
            "artifact": {
                "path": str(artifact_archive.relative_to(evidence_root)),
                **artifact_archive_record,
            },
            "independent_completeness": {
                "path": str(completeness_path.relative_to(evidence_root)),
                **completeness_record,
            },
            "independent_oracle_source": {
                "path": str(oracle_archive.relative_to(evidence_root)),
                **oracle_archive_record,
            },
            "independent_oracle_binary": {
                "path": str(
                    compiled_oracle_archive.relative_to(evidence_root)
                ),
                **compiled_oracle_archive_record,
            },
            "independent_ocaml_toolchain": toolchain_archive_records,
            "independent_oracle_compile_outputs":
                compiled_object_archive_records,
            "independent_python_sources": python_source_archive_records,
            "python_runtime": {
                "execution_binding": python_runtime["execution_binding"],
                "version": python_runtime["version"],
                "executable": {
                    "path": str(
                        python_executable_archive.relative_to(evidence_root)
                    ),
                    **python_executable_archive_record,
                },
                "elf_policy": python_runtime["elf_closure"]["policy"],
                "elf_roles": python_runtime["elf_closure"]["roles"],
                "virtual_elf_objects":
                    python_runtime["elf_closure"]["virtual_objects"],
                "elf_objects": python_elf_archive_records,
            },
            "pexpect_sources": pexpect_archive_records,
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
        flyspeck_float_corpus.require(
            validate_python_runtime() == python_runtime,
            "Python runtime changed during compiled corpus gate",
        )
        flyspeck_float_corpus.validate_record(
            source_path, attempt["inputs"]["generated_source"],
            "retained float-corpus source",
        )
        for label in ("artifact", "independent_completeness",
                      "independent_oracle_source",
                      "independent_oracle_binary", "linked_provenance",
                      "bootstrap_provenance", "bootstrap_log"):
            archived = attempt["inputs"][label]
            flyspeck_float_corpus.validate_record(
                evidence_root / archived["path"],
                {field: archived[field] for field in ("bytes", "md5", "sha256")},
                f"retained {label}",
            )
        for archived in attempt["inputs"]["independent_ocaml_toolchain"]:
            flyspeck_float_corpus.validate_record(
                evidence_root / archived["path"],
                {field: archived[field]
                 for field in ("bytes", "md5", "sha256")},
                f"retained OCaml toolchain {archived['label']}",
            )
        for archived in attempt["inputs"]["independent_python_sources"]:
            flyspeck_float_corpus.validate_record(
                evidence_root / archived["path"],
                {field: archived[field]
                 for field in ("bytes", "md5", "sha256")},
                f"retained Python source {archived['label']}",
            )
        python_runtime_input = attempt["inputs"]["python_runtime"]
        archived_python = python_runtime_input["executable"]
        flyspeck_float_corpus.validate_record(
            evidence_root / archived_python["path"],
            {field: archived_python[field]
             for field in ("bytes", "md5", "sha256")},
            "retained Python executable",
        )
        for archived in python_runtime_input["elf_objects"]:
            flyspeck_float_corpus.validate_record(
                evidence_root / archived["path"],
                {field: archived[field]
                 for field in ("bytes", "md5", "sha256")},
                "retained Python ELF object",
            )
        for archived in attempt["inputs"]["pexpect_sources"]:
            flyspeck_float_corpus.validate_record(
                evidence_root / archived["path"],
                {field: archived[field]
                 for field in ("bytes", "md5", "sha256")},
                f"retained pexpect source {archived['label']}",
            )
        for archived in attempt["inputs"][
            "independent_oracle_compile_outputs"
        ]:
            flyspeck_float_corpus.validate_record(
                evidence_root / archived["path"],
                {field: archived[field]
                 for field in ("bytes", "md5", "sha256")},
                f"retained oracle compile output {archived['name']}",
            )
        flyspeck_float_corpus.require(
            flyspeck_float_corpus.load_object(
                completeness_path, "retained independent completeness result"
            ) == completeness,
            "retained independent completeness semantics changed",
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
    payload, completeness = authenticated_artifact(
        candle_root, arguments.flyspeck_root.resolve(),
        arguments.overlay_root.resolve(), arguments.ocamlc, artifact_path,
    )
    check_candle(
        payload, candle_root, arguments.timeout, arguments.write,
        artifact_path, completeness,
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
