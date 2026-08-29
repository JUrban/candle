#!/usr/bin/env python3
"""Build and validate the machine-readable Candle Great 100 inventory.

The upstream suite name is historical: ``GREAT_100_THEOREMS`` currently has
65 execution targets.  This script keeps that exact target list, its direct
literal ``needs`` dependencies, and the still-missing S1 evidence visible in
one deterministic artifact.
"""

import argparse
from datetime import datetime
import hashlib
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = Path(__file__).with_suffix(".json")
IDENTITY_APPROVAL = ROOT / "candle/top100_identity_approval.json"
REFERENCE_SOURCE_CONTRACT = ROOT / "candle/reference_source_contracts.json"
AUDITED_BASE_COMMIT = "5b1888b9a0c1da7ca0ef2e80526b726f2e27df9d"
HISTORICAL_REFERENCE_COMMIT = "3170739521d88d04580f61385c95b497690b7002"
EXACT_SOURCE_REFERENCE_COMMIT = "1258c129c3ddf0b239b649ba7024eab677cd953b"
NEEDS_RE = re.compile(r'^\s*needs\s*"([^"]+)"\s*;;', re.MULTILINE)
LET_BINDING_RE = re.compile(
    r"^[ \t]*let[ \t]+([A-Za-z][A-Za-z0-9_']*)[ \t]*=", re.MULTILINE)

# holtest.mk uses one synthetic target for an ordered two-file session.
SPECIAL_LOAD_FILES = {
    "100/bertrand-primerecip": ["100/bertrand.ml", "100/primerecip.ml"],
}

# Named results requested after each clean load.  This is a source audit, not
# an expected fingerprint table: until a pinned reference run supplies exact
# identities, the manifest continues to report fingerprints as missing.  A
# The audited mapping rationale records how broad or repeatedly shadowed source
# files obtain a deterministic post-load acceptance boundary.
TARGET_THEOREMS = {
    "100/arithmetic_geometric_mean": ["AGM", "AGM_ROOT"],
    "100/arithmetic": ["ARITHMETIC_PROGRESSION"],
    "100/ballot": ["BALLOT"],
    "100/bernoulli": ["SUM_OF_POWERS"],
    "100/bertrand-primerecip": ["BERTRAND", "PRIMERECIP_DIVERGES"],
    "100/birthday": ["BIRTHDAY_THM", "BIRTHDAY_THM_EXPLICIT"],
    "100/buffon": ["BUFFON_GENERAL", "BUFFON_SHORT", "BUFFON_LONG"],
    "100/cantor": ["CANTOR"],
    "100/cayley_hamilton": ["CAYLEY_HAMILTON"],
    "100/ceva": ["CEVA"],
    "100/circle": ["AREA_CBALL", "AREA_BALL"],
    "100/chords": ["SEGMENT_CHORDS"],
    "100/combinations": [
        "NUMBER_OF_COMBINATIONS", "NUMBER_OF_COMBINATIONS_EXPLICIT"],
    "100/constructible": ["DOUBLE_THE_CUBE", "TRISECT_60_DEGREES"],
    "100/cosine": ["LAW_OF_COSINES"],
    "100/cubedissection": ["ONLY_TRIVIAL_CUBE_DISSECTION"],
    "100/cubic": ["CUBIC"],
    "100/derangements": ["THE_DERANGEMENTS_FORMULA"],
    "100/desargues": ["DESARGUES_DIRECT"],
    "100/descartes": ["DESCARTES_RULE_OF_SIGNS"],
    "100/dirichlet": ["DIRICHLET"],
    "100/div3": ["DIVISIBILITY_BY_3"],
    "100/divharmonic": ["HARMONIC_DIVERGES"],
    "100/e_is_transcendental": ["Finale.TRANSCENDENTAL_E"],
    "100/euler": ["EULER_PARTITION_THEOREM"],
    "100/feuerbach": ["FEUERBACH"],
    "100/fourier": [
        "FOURIER_SERIES_L2",
        "FOURIER_DINI_TEST",
        "FOURIER_JORDAN_BOUNDED_VARIATION",
        "FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE",
    ],
    "100/four_squares": ["SUM_OF_TWO_SQUARES", "LAGRANGE_NUM"],
    "100/friendship": ["FRIENDSHIP"],
    "100/fta": ["FTA"],
    "100/gcd": ["EGCD"],
    "100/green": ["GREEN_THEOREM_CURL"],
    "100/heron": ["HERON"],
    "100/isoperimetric": ["ISOPERIMETRIC_THEOREM"],
    "100/inclusion_exclusion": [
        "INCLUSION_EXCLUSION_USUAL", "INCLUSION_EXCLUSION_MOBIUS"],
    "100/independence": [
        "TARSKI_AXIOM_1_NONEUCLIDEAN",
        "TARSKI_AXIOM_2_NONEUCLIDEAN",
        "TARSKI_AXIOM_3_NONEUCLIDEAN",
        "TARSKI_AXIOM_4_NONEUCLIDEAN",
        "TARSKI_AXIOM_5_NONEUCLIDEAN",
        "TARSKI_AXIOM_6_NONEUCLIDEAN",
        "TARSKI_AXIOM_7_NONEUCLIDEAN",
        "TARSKI_AXIOM_8_NONEUCLIDEAN",
        "TARSKI_AXIOM_9_NONEUCLIDEAN",
        "NOT_TARSKI_AXIOM_10_NONEUCLIDEAN",
        "TARSKI_AXIOM_11_NONEUCLIDEAN",
    ],
    "100/isosceles": [
        "ISOSCELES_TRIANGLE_THEOREM", "ISOSCELES_TRIANGLE_CONVERSE"],
    "100/konigsberg": ["KOENIGSBERG"],
    "100/lagrange": ["GROUP_LAGRANGE"],
    "100/leibniz": ["LEIBNIZ_PI"],
    "100/lhopital": ["LHOPITAL"],
    "100/liouville": ["TRANSCENDENTAL_LIOUVILLE"],
    "100/minkowski": ["MINKOWSKI"],
    "100/morley": ["MORLEY"],
    "100/pascal": ["PASCAL"],
    "100/perfect": ["PERFECT_EUCLID", "PERFECT_EULER"],
    "100/pick": ["PICK"],
    "100/piseries": ["EULER_HARMONIC_SUM"],
    "100/platonic": ["PLATONIC_SOLIDS"],
    "100/pnt": ["PNT"],
    "100/polyhedron": ["EULER_RELATION"],
    "100/ptolemy": ["PTOLEMY"],
    "100/pythagoras": ["PYTHAGORAS"],
    "100/quartic": ["QUARTIC_CASES"],
    "100/ramsey": ["RAMSEY"],
    "100/ratcountable": ["COUNTABLE_RATIONALS", "DENUMERABLE_RATIONALS"],
    "100/realsuncountable": ["UNCOUNTABLE_REALS"],
    "100/reciprocity": ["RECIPROCITY_LEGENDRE"],
    "100/stirling": ["STIRLING"],
    "100/subsequence": ["ERDOS_SZEKERES"],
    "100/thales": ["THALES"],
    "100/transcendence": [
        "e_is_irrational",
        "e_is_transcendental",
        "pi_is_transcendental",
        "transcendental_if_exp_nonzero_algebraic",
        "zero_sum_algebraic_exp_algebraic",
    ],
    "100/triangular": ["TRIANGLE_FINITE_SUM", "TRIANGLE_CONVERGES'"],
    "100/two_squares": ["SUM_OF_TWO_SQUARES"],
    "100/wilson": ["WILSON", "WILSON_EQ"],
}

MANUAL_REVIEW_MAPPINGS = {}

AUDITED_MAPPING_RATIONALES = {
    "100/cantor": (
        "the acceptance boundary is the pinned post-load environment, so the "
        "final visible CANTOR binding at line 62 controls; the shadowed line-25 "
        "cardinality formulation remains recorded but is not addressable after "
        "the ordered source load"
    ),
    "100/fourier": (
        "the broad source has no singular result alias, so acceptance "
        "conservatively requires all four independently headlined culmination "
        "results: L2 convergence, Dini, Jordan bounded variation, and Fejer "
        "Cesaro summability"
    ),
    "100/piseries": (
        "the source section 'Isolate the most famous special case' immediately "
        "binds EULER_HARMONIC_SUM, uniquely identifying the intended named result"
    ),
    "100/quartic": (
        "the final visible QUARTIC_CASES is labeled 'the automatic proof' and "
        "has exactly the same theorem statement as the preceding iff-form "
        "QUARTIC_CASES; the last rebinding changes only the proof"
    ),
}

EXPECTED_RECORD_FIELDS = {
    "name", "theorem_sha256", "hypotheses_sha256", "conclusion_sha256",
    "global_axioms_sha256", "hypothesis_count", "global_axiom_count",
}
POST_STATE_FIELDS = {
    "kernel_state_sha256",
    "type_constants_sha256", "type_constant_count",
    "term_constants_sha256", "term_constant_count",
    "definitions_sha256", "definition_count",
    "global_axioms_sha256", "global_axiom_count",
}
EXPECTED_IDENTITY_FIELDS = {
    "approval_sha256", "serializer_sha256", "theorems", "post_state",
}
APPROVAL_FIELDS = {
    "schema", "artifact_kind", "approval_status", "promotion_allowed",
    "inventory_contract_sha256", "serializer_sha256", "reference_policy",
    "review", "collection_evidence", "targets",
}
REFERENCE_RUN_FIELDS = {
    "artifacts", "reference_git_head", "session_nonce", "identity_sha256",
    "sweep",
}
REFERENCE_ARTIFACT_NAMES = {
    "candidate", "plan", "request", "transcript", "source_contract",
    "controller_success", "collector_stdout", "collector_stderr",
    "validator_stdout", "validator_stderr"}
COLLECTION_EVIDENCE_FIELDS = {"contract", "receipt"}
SHA256_RE = re.compile(r"[0-9a-f]{64}")
COMMIT_RE = re.compile(r"[0-9a-f]{40}")
EMPTY_HYPOTHESES_SHA256 = hashlib.sha256(b"4:list1:0").hexdigest()


def _is_sha256(value):
    return isinstance(value, str) and SHA256_RE.fullmatch(value) is not None


def _validate_post_state(target, value):
    if not isinstance(value, dict) or set(value) != POST_STATE_FIELDS:
        raise ValueError(f"{target}: malformed expected post-state identity")
    for field in POST_STATE_FIELDS:
        if field.endswith("_sha256"):
            if not _is_sha256(value[field]):
                raise ValueError(f"{target}: malformed expected state hash: {field}")
        else:
            count = value[field]
            if isinstance(count, bool) or not isinstance(count, int) or count < 0:
                raise ValueError(f"{target}: malformed expected state count: {field}")
    if value["global_axiom_count"] != 3:
        raise ValueError(f"{target}: expected post-state must use three axioms")
    return value


def _validate_expected_identity_object(target, theorem_names, expected,
                                       approval_sha256=None):
    """Reject candidates or malformed approvals before manifest generation."""
    if expected is None:
        return None
    if not isinstance(expected, dict) or set(expected) != EXPECTED_IDENTITY_FIELDS:
        raise ValueError(f"{target}: malformed expected identity object")
    if not _is_sha256(expected["approval_sha256"]):
        raise ValueError(f"{target}: malformed expected approval identity")
    if (approval_sha256 is not None and
            expected["approval_sha256"] != approval_sha256):
        raise ValueError(f"{target}: expected approval identity mismatch")
    if not _is_sha256(expected["serializer_sha256"]):
        raise ValueError(f"{target}: malformed expected serializer identity")
    records = expected["theorems"]
    if not isinstance(records, list) or [
            record.get("name") if isinstance(record, dict) else None
            for record in records] != list(theorem_names):
        raise ValueError(f"{target}: expected theorem names/order mismatch")
    for record in records:
        if set(record) != EXPECTED_RECORD_FIELDS:
            raise ValueError(f"{target}: malformed expected theorem record")
        for field in (
                "theorem_sha256", "hypotheses_sha256", "conclusion_sha256",
                "global_axioms_sha256"):
            if not _is_sha256(record[field]):
                raise ValueError(f"{target}: malformed expected hash: {field}")
        for field in ("hypothesis_count", "global_axiom_count"):
            value = record[field]
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{target}: malformed expected count: {field}")
        if (record["hypothesis_count"] != 0 or
                record["hypotheses_sha256"] != EMPTY_HYPOTHESES_SHA256):
            raise ValueError(f"{target}: expected theorem is not closed")
        if record["global_axiom_count"] != 3:
            raise ValueError(f"{target}: expected theorem must use three axioms")
    _validate_post_state(target, expected["post_state"])
    axiom_identities = {
        (record["global_axioms_sha256"], record["global_axiom_count"])
        for record in records
    }
    state_axiom = (expected["post_state"]["global_axioms_sha256"],
                   expected["post_state"]["global_axiom_count"])
    if axiom_identities != {state_axiom}:
        raise ValueError(f"{target}: theorem/post-state axiom identity mismatch")
    return expected


def _reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key in identity approval: {key}")
        result[key] = value
    return result


def _canonical_sha256(value):
    encoded = json.dumps(
        value, ensure_ascii=True, separators=(",", ":"), sort_keys=True,
    ).encode("ascii")
    return hashlib.sha256(encoded).hexdigest()


def _decode_replay_json(source, label):
    try:
        value = json.loads(
            source.decode("utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"malformed {label} JSON artifact") from error
    if not isinstance(value, dict):
        raise ValueError(f"malformed {label} JSON artifact")
    return value


def _replay_reference_run(target, run, artifact_sources, expected_identity,
                          policy):
    """Mechanically replay one exact v7 candidate and bind its semantics."""
    # Imported only on the approved path.  reference_fingerprints imports the
    # committed regression manifest, not this generator module, so this does
    # not create an import cycle during ordinary unapproved regeneration.
    import reference_fingerprints as reference  # pylint: disable=import-outside-toplevel

    candidate = _decode_replay_json(
        artifact_sources["candidate"], f"{target['name']} candidate")
    plan = _decode_replay_json(
        artifact_sources["plan"], f"{target['name']} plan")
    try:
        request = artifact_sources["request"].decode("utf-8")
        transcript = artifact_sources["transcript"].decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(
            f"{target['name']}: non-UTF-8 reference request/transcript") from error
    source_contract = _decode_replay_json(
        artifact_sources["source_contract"],
        f"{target['name']} source contract")
    expected_source_contract = {
        "schema": "candle-s1-reference-source-contract-v1", **policy}
    if source_contract != expected_source_contract:
        raise ValueError(f"{target['name']}: replay source contract mismatch")

    if set(plan) != {
            "schema", "status", "session_nonce", "fresh_process_contract",
            "reference", "input", "request"}:
        raise ValueError(f"{target['name']}: malformed replay plan fields")
    if (plan["schema"] != reference.PLAN_SCHEMA or
            plan["status"] != "planned_not_executed" or
            plan["session_nonce"] != run["session_nonce"]):
        raise ValueError(f"{target['name']}: replay plan session mismatch")
    plan_reference = plan["reference"]
    if (not isinstance(plan_reference, dict) or set(plan_reference) != {
            "root", "git_head", "git_status", "runtime_executable",
            "runtime_interpreter", "runtime_stublib", "runtime_library_tree",
            "runtime_stub_files", "dynamic_libraries", "ocamlc", "findlib",
            "hol_ml", "generated_boot_files", "ocaml_library_tree",
            "external_runtime"} or
            not isinstance(plan_reference.get("root"), str) or
            not Path(plan_reference["root"]).is_absolute() or
            plan_reference.get("git_head") != run["reference_git_head"] or
            plan_reference.get("git_status") != []):
        raise ValueError(f"{target['name']}: replay reference head mismatch")
    fresh = plan["fresh_process_contract"]
    if (not isinstance(fresh, dict) or set(fresh) != {
            "required", "preloaded_checkpoint_allowed", "working_directory",
            "environment_policy", "runtime_argv", "runtime_environment"} or
            fresh["required"] is not True or
            fresh["preloaded_checkpoint_allowed"] is not False or
            fresh["working_directory"] != plan_reference["root"]):
        raise ValueError(f"{target['name']}: replay process contract mismatch")
    try:
        reference.validate_reference_runtime_provenance(plan)
    except reference.CollectionError as error:
        raise ValueError(
            f"{target['name']}: replay external-runtime mismatch: {error}",
        ) from error
    plan_input = plan["input"]
    theorem_names = [
        theorem["name"] for theorem in target["fingerprint_request"]["theorems"]]
    if (not isinstance(plan_input, dict) or set(plan_input) != {
            "collector", "collector_repository", "manifest",
            "manifest_schema_version", "target", "load_files",
            "theorem_names", "mapping_status", "serializer", "source_mode",
            "source_contract"} or
            plan_input.get("target") != target["name"] or
            plan_input.get("theorem_names") != theorem_names or
            plan_input.get("mapping_status") != "audited" or
            plan_input.get("source_mode") != "manifest-exact"):
        raise ValueError(f"{target['name']}: replay target contract mismatch")
    collector = plan_input["collector"]
    collector_repository = plan_input["collector_repository"]
    if (not isinstance(collector, dict) or
            collector.get("sha256") !=
            _sha256(ROOT / "candle/reference_fingerprints.py") or
            not isinstance(collector.get("path"), str) or
            not isinstance(collector_repository, dict) or
            collector_repository.get("git_status") != [] or
            collector_repository.get("collector_matches_head") is not True):
        raise ValueError(f"{target['name']}: replay collector mismatch")
    serializer = plan_input.get("serializer")
    if (not isinstance(serializer, dict) or
            serializer.get("sha256") != expected_identity["serializer_sha256"] or
            not isinstance(serializer.get("path"), str)):
        raise ValueError(f"{target['name']}: replay serializer mismatch")
    plan_sources = plan_input.get("load_files")
    if not isinstance(plan_sources, list) or len(plan_sources) != len(
            target["load_files"]):
        raise ValueError(f"{target['name']}: replay source list mismatch")
    for relative, source_record in zip(target["load_files"], plan_sources):
        if (not isinstance(source_record, dict) or
                source_record.get("relative_path") != relative or
                source_record.get("path") != str(
                    Path(plan_reference["root"]) / relative) or
                source_record.get("sha256") !=
                target["load_file_sha256"][relative] or
                source_record.get("source_role") != "selected-manifest-source"):
            raise ValueError(f"{target['name']}: replay source identity mismatch")
    plan_contract = plan_input.get("source_contract")
    if (not isinstance(plan_contract, dict) or
            plan_contract.get("sha256") !=
            hashlib.sha256(artifact_sources["source_contract"]).hexdigest() or
            {key: plan_contract.get(key) for key in policy} != policy):
        raise ValueError(f"{target['name']}: replay plan source contract mismatch")
    expected_request = reference._request_source(
        target, serializer["path"], run["session_nonce"])
    if (request != expected_request or not isinstance(plan["request"], dict) or
            set(plan["request"]) != {"source", "sha256"} or
            plan["request"].get("source") != request or
            plan["request"].get("sha256") !=
            hashlib.sha256(request.encode("utf-8")).hexdigest()):
        raise ValueError(f"{target['name']}: replay request mismatch")
    try:
        reference.validate_candidate(candidate, plan, request, transcript)
    except reference.CollectionError as error:
        raise ValueError(
            f"{target['name']}: reference candidate replay failed: {error}") from error
    if (candidate.get("session_nonce") != run["session_nonce"] or
            candidate.get("plan_pins", {}).get("reference", {}).get(
                "git_head") != run["reference_git_head"]):
        raise ValueError(f"{target['name']}: replay candidate provenance mismatch")
    observed = candidate.get("candidate_identities")
    if (not isinstance(observed, dict) or set(observed) != {
            "status", "mapping_status", "expected_identities_present",
            "serializer", "theorems", "post_state", "approval_sha256"} or
            observed["status"] != "observed_uncompared" or
            observed["mapping_status"] != "audited" or
            observed["expected_identities_present"] is not False or
            observed["approval_sha256"] is not None):
        raise ValueError(f"{target['name']}: malformed replay identity result")
    projection = {
        "serializer_sha256": observed.get("serializer", {}).get("sha256"),
        "theorems": observed["theorems"],
        "post_state": observed["post_state"],
    }
    if projection != expected_identity or _canonical_sha256(projection) != \
            run["identity_sha256"]:
        raise ValueError(f"{target['name']}: replay identity projection mismatch")


def _inventory_contract(targets):
    projection = {
        "schema": "candle-great100-inventory-contract-v1",
        "target_count": len(targets),
        "covered_source_count": len({
            path for target in targets for path in target["load_files"]}),
        "theorem_request_count": sum(
            len(target["fingerprint_request"]["theorems"])
            for target in targets),
        "targets": [{
            "name": target["name"],
            "load_files": target["load_files"],
            "load_file_sha256": target["load_file_sha256"],
            "mapping_status": target["fingerprint_request"]["mapping_status"],
            "theorem_names": [
                theorem["name"]
                for theorem in target["fingerprint_request"]["theorems"]
            ],
        } for target in targets],
    }
    if (projection["target_count"], projection["covered_source_count"],
            projection["theorem_request_count"]) != (65, 66, 97):
        raise ValueError("Great 100 canonical inventory is not 65/66/97")
    return projection, _canonical_sha256(projection)


def _read_evidence_record(record, label):
    if not isinstance(record, dict) or set(record) != {"path", "bytes", "sha256"}:
        raise ValueError(f"malformed {label} artifact")
    if not isinstance(record["path"], str):
        raise ValueError(f"unsafe {label} artifact path")
    relative = Path(record["path"])
    if (relative.is_absolute() or ".." in relative.parts or
            relative.as_posix() != record["path"]):
        raise ValueError(f"unsafe {label} artifact path")
    path = ROOT / relative
    metadata = path.lstat()
    if (path.is_symlink() or not path.is_file() or metadata.st_nlink != 1):
        raise ValueError(f"missing ordinary {label} artifact")
    source = path.read_bytes()
    if (isinstance(record["bytes"], bool) or record["bytes"] != len(source) or
            not _is_sha256(record["sha256"]) or
            record["sha256"] != hashlib.sha256(source).hexdigest()):
        raise ValueError(f"changed {label} artifact")
    return source


def _load_collection_evidence(approval, targets):
    evidence = approval["collection_evidence"]
    if (not isinstance(evidence, dict) or
            set(evidence) != COLLECTION_EVIDENCE_FIELDS):
        raise ValueError("malformed reference collection evidence")
    sources = {
        name: _read_evidence_record(evidence[name], f"collection {name}")
        for name in COLLECTION_EVIDENCE_FIELDS
    }
    try:
        contract = json.loads(
            sources["contract"].decode("utf-8"),
            object_pairs_hook=_reject_duplicate_keys)
        receipt = json.loads(
            sources["receipt"].decode("utf-8"),
            object_pairs_hook=_reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError("malformed reference collection JSON") from error
    if (not isinstance(contract, dict) or set(contract) != {
            "schema", "kind", "approval_status", "promotion_allowed",
            "sweep_count", "target_count", "total_target_runs", "source_mode",
            "project", "candle", "reference", "runtime", "external_runtime",
            "deadlines", "inventory", "controller"} or
            contract["schema"] != 2 or
            contract["kind"] !=
            "candle-great100-two-sweep-reference-collection" or
            contract["approval_status"] !=
            "candidate_collection_only_unapproved" or
            contract["promotion_allowed"] is not False or
            contract["sweep_count"] != 2 or contract["target_count"] != 65 or
            contract["total_target_runs"] != 130 or
            contract["source_mode"] != "manifest-exact"):
        raise ValueError("malformed reference collection contract")
    inventory = contract["inventory"]
    if (not isinstance(inventory, dict) or
            inventory.get("target_count") != 65 or
            inventory.get("source_count") != 66 or
            inventory.get("request_count") != 97 or
            not isinstance(inventory.get("targets"), list) or
            [item.get("name") for item in inventory["targets"]
             if isinstance(item, dict)] != [target["name"] for target in targets]):
        raise ValueError("reference collection inventory differs from manifest")
    contract_record = receipt.get("contract") if isinstance(receipt, dict) else None
    if (not isinstance(receipt, dict) or set(receipt) != {
            "schema", "kind", "contract_sha256", "contract", "sweep_count",
            "target_count", "total_target_runs", "completed_target_runs",
            "pending_target_runs", "failure_attempt_count", "failures",
            "publication_interruptions", "outcome", "closed", "approval_status",
            "promotion_allowed", "sweeps"} or
            receipt["schema"] != 1 or
            receipt["kind"] !=
            "candle-great100-two-sweep-reference-receipt" or
            receipt["contract_sha256"] != _canonical_sha256(contract) or
            not isinstance(contract_record, dict) or
            contract_record.get("path") != "collection-contract.json" or
            contract_record.get("bytes") != len(sources["contract"]) or
            contract_record.get("sha256") !=
            hashlib.sha256(sources["contract"]).hexdigest() or
            receipt["sweep_count"] != 2 or receipt["target_count"] != 65 or
            receipt["total_target_runs"] != 130 or
            receipt["completed_target_runs"] != 130 or
            receipt["pending_target_runs"] != 0 or
            receipt["outcome"] != "complete" or receipt["closed"] is not True or
            receipt["approval_status"] != "candidates_unapproved" or
            receipt["promotion_allowed"] is not False or
            type(receipt["failure_attempt_count"]) is not int or
            receipt["failure_attempt_count"] < 0 or
            not isinstance(receipt["failures"], list) or
            len(receipt["failures"]) != receipt["failure_attempt_count"] or
            not isinstance(receipt["publication_interruptions"], list)):
        raise ValueError("reference collection receipt is not closed and exact")
    sweeps = receipt["sweeps"]
    if not isinstance(sweeps, list) or len(sweeps) != 2:
        raise ValueError("reference collection receipt lacks two sweeps")
    successes = {}
    for sweep_number, sweep in enumerate(sweeps, 1):
        if (not isinstance(sweep, dict) or set(sweep) != {
                "sweep", "target_count", "completed_count", "pending_count",
                "targets"} or sweep["sweep"] != sweep_number or
                sweep["target_count"] != 65 or sweep["completed_count"] != 65 or
                sweep["pending_count"] != 0 or
                not isinstance(sweep["targets"], list) or
                len(sweep["targets"]) != 65):
            raise ValueError("malformed closed reference sweep")
        for target_number, (target, row) in enumerate(
                zip(targets, sweep["targets"]), 1):
            if (not isinstance(row, dict) or set(row) != {
                    "index", "name", "state", "attempt_count", "success",
                    "attempts"} or row["index"] != target_number or
                    row["name"] != target["name"] or row["state"] != "complete" or
                    type(row["attempt_count"]) is not int or
                    row["attempt_count"] < 1 or
                    not isinstance(row["attempts"], list) or
                    len(row["attempts"]) != row["attempt_count"] or
                    not isinstance(row["success"], dict)):
                raise ValueError("malformed reference collection target success")
            success = row["success"]
            if (set(success) != {
                    "attempt", "receipt_path", "receipt", "session_nonce",
                    "artifacts"} or
                    not isinstance(success["attempt"], str) or
                    re.fullmatch(r"attempt-[0-9]{4}", success["attempt"]) is None or
                    success["receipt_path"] !=
                    (f"sweep-{sweep_number}/target-{target_number:03d}/"
                     f"{success['attempt']}/success.json") or
                    not _is_sha256(success["session_nonce"]) or
                    not isinstance(success["receipt"], dict) or
                    not isinstance(success["artifacts"], dict)):
                raise ValueError("malformed aggregate collection success")
            successes[(sweep_number, target_number)] = success
    return contract, successes


def _load_identity_approval(targets):
    approval_metadata = IDENTITY_APPROVAL.lstat()
    if (IDENTITY_APPROVAL.is_symlink() or not IDENTITY_APPROVAL.is_file() or
            approval_metadata.st_nlink != 1):
        raise ValueError("identity approval is not an ordinary single-link file")
    source = IDENTITY_APPROVAL.read_bytes()
    try:
        approval = json.loads(
            source.decode("utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError("malformed Great 100 identity approval artifact") from error
    approval_sha256 = hashlib.sha256(source).hexdigest()
    if approval == {
            "schema": "candle-s1-identity-approval-v1",
            "artifact_kind":
                "independently-reviewed-ocaml-reference-identities",
            "approval_status": "unapproved", "promotion_allowed": False,
            "inventory_contract_sha256": None, "serializer_sha256": None,
            "reference_policy": None, "review": None, "targets": []}:
        _, inventory_sha256 = _inventory_contract(targets)
        return approval, approval_sha256, {}, inventory_sha256
    if isinstance(approval, dict) and approval.get("approval_status") == "unapproved":
        raise ValueError("unapproved identity artifact carries promotable data")
    if not isinstance(approval, dict) or set(approval) != APPROVAL_FIELDS:
        raise ValueError("malformed Great 100 identity approval fields")
    if (approval["schema"] != "candle-s1-identity-approval-v2" or
            approval["artifact_kind"] !=
            "independently-reviewed-ocaml-reference-identities"):
        raise ValueError("unsupported Great 100 identity approval artifact")
    _, inventory_sha256 = _inventory_contract(targets)
    if approval["approval_status"] != "approved" or \
            approval["promotion_allowed"] is not True:
        raise ValueError("identity approval is not fail-closed")
    if approval["inventory_contract_sha256"] != inventory_sha256:
        raise ValueError("identity approval inventory contract mismatch")
    serializer_sha256 = _sha256(ROOT / "candle/fingerprint.ml")
    if approval["serializer_sha256"] != serializer_sha256:
        raise ValueError("identity approval serializer mismatch")
    policy = approval["reference_policy"]
    if not isinstance(policy, dict) or set(policy) != {
            "historical_upstream_commit", "exact_source_reference_commit",
            "compatibility_deltas"}:
        raise ValueError("malformed identity reference policy")
    if (policy["historical_upstream_commit"] != HISTORICAL_REFERENCE_COMMIT or
            policy["exact_source_reference_commit"] !=
            EXACT_SOURCE_REFERENCE_COMMIT):
        raise ValueError("identity reference commits are not pinned")
    source_contract = json.loads(
        REFERENCE_SOURCE_CONTRACT.read_text(encoding="utf-8"),
        object_pairs_hook=_reject_duplicate_keys)
    if (not isinstance(source_contract, dict) or set(source_contract) != {
            "schema", "historical_upstream_commit",
            "exact_source_reference_commit", "compatibility_deltas"} or
            source_contract["schema"] !=
            "candle-s1-reference-source-contract-v1" or
            source_contract["historical_upstream_commit"] !=
            HISTORICAL_REFERENCE_COMMIT or
            source_contract["exact_source_reference_commit"] !=
            EXACT_SOURCE_REFERENCE_COMMIT or
            policy != {key: source_contract[key] for key in (
                "historical_upstream_commit", "exact_source_reference_commit",
                "compatibility_deltas")}):
        raise ValueError("identity approval differs from source contract")
    deltas = policy["compatibility_deltas"]
    if not isinstance(deltas, list) or len(deltas) != 3:
        raise ValueError("identity reference policy must review three source deltas")
    expected_delta_paths = {
        "100/e_is_transcendental.ml", "100/euler.ml", "100/lagrange.ml"}
    observed_delta_paths = set()
    for delta in deltas:
        if not isinstance(delta, dict) or set(delta) != {
                "path", "historical_sha256", "selected_sha256", "reason"}:
            raise ValueError("malformed identity reference source delta")
        observed_delta_paths.add(delta["path"])
        if (not _is_sha256(delta["historical_sha256"]) or
                not _is_sha256(delta["selected_sha256"]) or
                not isinstance(delta["reason"], str) or not delta["reason"]):
            raise ValueError("malformed identity reference source delta value")
    if observed_delta_paths != expected_delta_paths:
        raise ValueError("identity reference source delta set mismatch")
    review = approval["review"]
    if not isinstance(review, dict) or set(review) != {
            "reviewer", "approved_utc", "review_commit", "decision"}:
        raise ValueError("malformed independent identity review")
    if (not isinstance(review["reviewer"], str) or not review["reviewer"] or
            not isinstance(review["decision"], str) or
            review["decision"] !=
            "two-reference-runs-identical-and-source-deltas-reviewed" or
            not isinstance(review["review_commit"], str) or
            COMMIT_RE.fullmatch(review["review_commit"]) is None):
        raise ValueError("identity approval lacks an independent review")
    try:
        approved_time = datetime.fromisoformat(review["approved_utc"])
    except (TypeError, ValueError) as error:
        raise ValueError("malformed identity approval time") from error
    if approved_time.tzinfo is None:
        raise ValueError("identity approval time lacks timezone")

    collection_contract, collection_successes = \
        _load_collection_evidence(approval, targets)

    approved_targets = approval["targets"]
    if not isinstance(approved_targets, list) or len(approved_targets) != 65:
        raise ValueError("identity approval does not cover 65 targets")
    expected = {}
    artifact_owners = {}
    for target, approved in zip(targets, approved_targets):
        if not isinstance(approved, dict) or set(approved) != {
                "name", "reference_runs", "expected_identity"}:
            raise ValueError("malformed approved target identity")
        if approved["name"] != target["name"]:
            raise ValueError("approved target order mismatch")
        approved_identity = approved["expected_identity"]
        identity_with_approval = (
            dict(approved_identity) if isinstance(approved_identity, dict) else {})
        identity_with_approval["approval_sha256"] = approval_sha256
        _validate_expected_identity_object(
            target["name"],
            [item["name"] for item in
             target["fingerprint_request"]["theorems"]],
            identity_with_approval, approval_sha256)
        runs = approved["reference_runs"]
        if not isinstance(runs, list) or len(runs) != 2:
            raise ValueError(f"{target['name']}: two reference runs required")
        nonces = set()
        identities = set()
        independent_artifacts = {
            name: set() for name in
            ("candidate", "plan", "request", "transcript",
             "controller_success", "collector_stdout", "collector_stderr",
             "validator_stdout", "validator_stderr")}
        for run_index, run in enumerate(runs, 1):
            if not isinstance(run, dict) or set(run) != REFERENCE_RUN_FIELDS:
                raise ValueError(f"{target['name']}: malformed reference run")
            if run["sweep"] != run_index:
                raise ValueError(f"{target['name']}: malformed reference sweep")
            if (not isinstance(run["reference_git_head"], str) or
                    COMMIT_RE.fullmatch(run["reference_git_head"]) is None or
                    run["reference_git_head"] !=
                    policy["exact_source_reference_commit"]):
                raise ValueError(f"{target['name']}: malformed reference head")
            for field in ("session_nonce", "identity_sha256"):
                if not _is_sha256(run[field]):
                    raise ValueError(f"{target['name']}: malformed reference run hash")
            artifacts = run["artifacts"]
            if not isinstance(artifacts, dict) or set(artifacts) != \
                    REFERENCE_ARTIFACT_NAMES:
                raise ValueError(f"{target['name']}: malformed reference artifacts")
            artifact_sources = {}
            for artifact_name, record in artifacts.items():
                if not isinstance(record, dict) or set(record) != {
                        "path", "bytes", "sha256"}:
                    raise ValueError(
                        f"{target['name']}: malformed {artifact_name} artifact")
                if not isinstance(record["path"], str):
                    raise ValueError(
                        f"{target['name']}: unsafe {artifact_name} artifact path")
                relative = Path(record["path"])
                if (relative.is_absolute() or
                        ".." in relative.parts or relative.as_posix() != record["path"]):
                    raise ValueError(
                        f"{target['name']}: unsafe {artifact_name} artifact path")
                artifact_path = ROOT / relative
                if artifact_path.resolve() == IDENTITY_APPROVAL.resolve():
                    raise ValueError(
                        f"{target['name']}: approval reused as {artifact_name}")
                metadata = artifact_path.lstat()
                if (artifact_path.is_symlink() or not artifact_path.is_file() or
                        metadata.st_nlink != 1):
                    raise ValueError(
                        f"{target['name']}: missing ordinary {artifact_name} artifact")
                source = artifact_path.read_bytes()
                artifact_sources[artifact_name] = source
                if (isinstance(record["bytes"], bool) or
                        record["bytes"] != len(source) or
                        not _is_sha256(record["sha256"]) or
                        record["sha256"] != hashlib.sha256(source).hexdigest()):
                    raise ValueError(
                        f"{target['name']}: changed {artifact_name} artifact")
                if artifact_name in independent_artifacts:
                    independent_artifacts[artifact_name].add(
                        (record["path"], record["sha256"]))
                previous = artifact_owners.get(record["path"])
                if previous is not None and (
                        artifact_name != "source_contract" or
                        previous != (artifact_name, record["sha256"])):
                    raise ValueError(
                        f"{target['name']}: reused {artifact_name} artifact path")
                artifact_owners[record["path"]] = (
                    artifact_name, record["sha256"])
            _replay_reference_run(
                target, run, artifact_sources, approved_identity, policy)
            try:
                success_receipt = json.loads(
                    artifact_sources["controller_success"].decode("utf-8"),
                    object_pairs_hook=_reject_duplicate_keys)
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValueError(
                    f"{target['name']}: malformed controller success") from error
            target_index = len(expected) + 1
            aggregate_success = collection_successes[(run_index, target_index)]
            aggregate_receipt = aggregate_success["receipt"]
            success_record = artifacts["controller_success"]
            if (not isinstance(aggregate_receipt, dict) or
                    aggregate_receipt.get("bytes") != success_record["bytes"] or
                    aggregate_receipt.get("sha256") != success_record["sha256"] or
                    aggregate_success["session_nonce"] != run["session_nonce"]):
                raise ValueError(
                    f"{target['name']}: aggregate receipt does not bind run")
            if (not isinstance(success_receipt, dict) or
                    set(success_receipt) != {
                        "schema", "kind", "sweep", "target_index", "target",
                        "session_nonce", "artifacts", "collector_stdout",
                        "collector_stderr", "validator_stdout",
                        "validator_stderr", "deadlines", "approval_status",
                        "promotion_allowed"} or
                    success_receipt["schema"] != 1 or
                    success_receipt["kind"] !=
                    "candle-reference-attempt-success" or
                    success_receipt["sweep"] != run_index or
                    success_receipt["target_index"] != target_index or
                    success_receipt["target"] != target["name"] or
                    success_receipt["session_nonce"] != run["session_nonce"] or
                    success_receipt["deadlines"] !=
                    collection_contract["deadlines"] or
                    success_receipt["approval_status"] !=
                    "candidate_unapproved" or
                    success_receipt["promotion_allowed"] is not False or
                    not isinstance(success_receipt["artifacts"], dict) or
                    set(success_receipt["artifacts"]) != {
                        "candidate", "plan", "request", "transcript"}):
                raise ValueError(
                    f"{target['name']}: malformed controller success")
            for artifact_name in (
                    "candidate", "plan", "request", "transcript"):
                receipt_record = success_receipt["artifacts"][artifact_name]
                aggregate_record = aggregate_success["artifacts"].get(
                    artifact_name)
                approval_record = artifacts[artifact_name]
                if (not isinstance(receipt_record, dict) or
                        set(receipt_record) != {"path", "bytes", "sha256"} or
                        receipt_record.get("bytes") != approval_record["bytes"] or
                        receipt_record.get("sha256") != approval_record["sha256"] or
                        aggregate_record != receipt_record):
                    raise ValueError(
                        f"{target['name']}: controller receipt does not bind "
                        f"{artifact_name}")
            for artifact_name in (
                    "collector_stdout", "collector_stderr", "validator_stdout",
                    "validator_stderr"):
                receipt_record = success_receipt[artifact_name]
                approval_record = artifacts[artifact_name]
                if (not isinstance(receipt_record, dict) or
                        set(receipt_record) != {"path", "bytes", "sha256"} or
                        receipt_record.get("bytes") != approval_record["bytes"] or
                        receipt_record.get("sha256") != approval_record["sha256"]):
                    raise ValueError(
                        f"{target['name']}: controller receipt does not bind "
                        f"{artifact_name}")
            plan = json.loads(
                artifact_sources["plan"].decode("utf-8"),
                object_pairs_hook=_reject_duplicate_keys)
            candle_contract = collection_contract["candle"]
            reference_contract = collection_contract["reference"]
            external_contract = collection_contract["external_runtime"]
            external_plan = plan["reference"]["external_runtime"]
            if (plan["input"]["collector"]["sha256"] !=
                    candle_contract["collector"]["sha256"] or
                    plan["input"]["collector_repository"]["git_head"] !=
                    candle_contract["git_head"] or
                    plan["input"]["collector_repository"][
                        "support_at_head_sha256"] !=
                    candle_contract["protocol"]["sha256"] or
                    plan["input"]["manifest"]["sha256"] !=
                    candle_contract["manifest"]["sha256"] or
                    plan["input"]["serializer"]["sha256"] !=
                    candle_contract["serializer"]["sha256"] or
                    plan["reference"]["root"] != reference_contract["root"] or
                    plan["reference"]["git_head"] !=
                    reference_contract["git_head"]):
                raise ValueError(
                    f"{target['name']}: collection contract does not bind plan")
            if (external_plan["policy"] != external_contract["policy"] or
                    any(external_plan[key]["argument_path"] !=
                        external_contract[key]["argument_path"] or
                        external_plan[key]["resolved_executable"]["path"] !=
                        external_contract[key]["path"] or
                        external_plan[key]["resolved_executable"]["sha256"] !=
                        external_contract[key]["sha256"]
                        for key in ("command_shell", "pari_gp")) or
                    external_plan["package_archive"] != {
                        "path": external_contract["package_archive"]["path"],
                        "sha256":
                            external_contract["package_archive"]["sha256"]} or
                    external_plan["package_tree"] !=
                    external_contract["package_tree"] or
                    external_plan["configuration"] != {
                        "path": external_contract["configuration"]["path"],
                        "sha256": external_contract["configuration"]["sha256"]} or
                    external_plan["data_tree"] != external_contract["data_tree"] or
                    any(plan["fresh_process_contract"]["runtime_environment"].get(
                        key) != value for key, value in
                        external_contract["runtime_environment"].items())):
                raise ValueError(
                    f"{target['name']}: collection contract does not bind "
                    "external runtime")
            nonces.add(run["session_nonce"])
            identities.add(run["identity_sha256"])
        if len(nonces) != 2 or len(identities) != 1:
            raise ValueError(f"{target['name']}: reference runs are not independent/equal")
        if any(len(records) != 2 for records in independent_artifacts.values()):
            raise ValueError(
                f"{target['name']}: reference run artifacts are not independent")
        identity = identity_with_approval
        if _canonical_sha256(approved_identity) != next(iter(identities)):
            raise ValueError(f"{target['name']}: approved identity evidence mismatch")
        expected[target["name"]] = identity
    return approval, approval_sha256, expected, inventory_sha256


# Observations are evidence, not acceptance-policy exceptions.  Keep expected
# status "pass" and link failures to a minimized compatibility-ledger entry.
BASELINE_OBSERVATIONS = {
    "100/bertrand-primerecip": {
        "status": "fail",
        "phase": "parse",
        "compatibility_category": "OCaml float-literal syntax",
        "ledger_id": "CANDLE-OCAML-FLOAT-LITERAL-001",
        "diagnostic": "Expected to be at EOF; Parsing failed at let num_of_float",
        "first_source_location": "100/bertrand.ml:18",
        "wall_seconds": 212.6,
        "peak_rss_kib": None,
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "compatibility_paths_match_audited_base": True,
        },
    },
    "100/ceva": {
        "status": "fail",
        "phase": "dependency_load",
        "compatibility_category": "missing numeric helper",
        "ledger_id": "CANDLE-OCAML-NUM-ROUNDING-001",
        "diagnostic": "undefined value round_num while loading Examples/sos.ml",
        "first_source_location": "Examples/sos.ml",
        "wall_seconds": 1428.4,
        "peak_rss_kib": None,
        "anchor_candidate": "218c7c9",
        "isolated_numeric_validation": {
            "status": "pass",
            "selected_case_count": 15,
            "oracle": "candle/compatibility/test_num_rationals.py",
            "source_commit": "870c408a7fe6fe78bbb57962690b3f52d8fb78cd",
            "target_status": "pending_remaining_sos_compatibility",
        },
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/constructible": {
        "status": "fail",
        "phase": "parse",
        "compatibility_category": "OCaml multiline string literal",
        "diagnostic": "LEXER ERROR; Parsing failed inside the multiline define_type string",
        "first_source_location": "100/constructible.ml:115",
        "log_active_seconds_approx": 3730.4,
        "peak_rss_kib": None,
        "upstream_remedy": {
            "repository": "CakeML/cakeml",
            "commit": "c26aa71d2b1007d43cecd1ef7f843530b32ad4fc",
            "status": "present_in_audited_source_base; compiled Candle rebuild required",
        },
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/cubedissection": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 3794.6,
        "observed_process_rss_kib": 6413644,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/cubic": {
        "status": "fail",
        "phase": "dependency_elaboration",
        "compatibility_category": "polymorphic comparison",
        "ledger_id": "CANDLE-OCAML-POLYMORPHIC-COMPARISON-001",
        "diagnostic": (
            "SEMIRING_NORMALIZERS_CONV comparator inferred as term -> term -> bool "
            "where int -> int -> bool was expected"
        ),
        "first_source_location": "Complex/complexnumbers.ml:720",
        "log_active_seconds_approx": 192.0,
        "peak_rss_kib": None,
        "anchor_candidate": "5c44565",
        "isolated_source_validation": {
            "source_normalization_commit": "75d4062",
            "status": "pass",
            "fingerprint_status": "observed_uncompared",
            "artifact": "candle/compatibility/cubic_target_observation.json",
        },
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/desargues": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 1379.9,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/descartes": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 4108.9,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/dirichlet": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 3759.4,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/div3": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 169.0,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/divharmonic": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 193.8,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/e_is_transcendental": {
        "status": "fail",
        "phase": "parse",
        "compatibility_category": "trailing semicolon in argument expression",
        "ledger_id": "CANDLE-OCAML-TRAILING-SEMICOLON-001",
        "diagnostic": (
            "Expected to be at EOF; parsing rejects the enclosing "
            "Pm_eqn4_rhs module phrase"
        ),
        "diagnostic_pointer": "100/e_is_transcendental.ml:921",
        "first_incompatible_source_location": "100/e_is_transcendental.ml:995",
        "log_active_seconds_approx": 246.7,
        "peak_rss_kib": None,
        "anchor_candidate": "badbd63",
        "isolated_source_validation": {
            "source_normalization_commit": "6ce6fc1",
            "status": "pass",
            "fingerprint_status": "observed_uncompared",
            "fingerprint_value_path": "Finale.TRANSCENDENTAL_E",
            "artifact": (
                "candle/compatibility/"
                "e_is_transcendental_target_observation.json"
            ),
        },
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/euler": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 153.5,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/feuerbach": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 1560.6,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/fourier": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 3977.2,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/four_squares": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 182.1,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/friendship": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 182.0,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/fta": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 158.3,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/gcd": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 162.2,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/green": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 4437.4,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
}


def _great_100_targets(text):
    """Return the tokens assigned to GREAT_100_THEOREMS in Make syntax."""
    lines = iter(text.splitlines())
    for line in lines:
        match = re.match(r"^GREAT_100_THEOREMS\s*:=\s*(.*)$", line)
        if match:
            break
    else:
        raise ValueError("GREAT_100_THEOREMS is absent from holtest.mk")

    targets = []
    fragment = match.group(1)
    while True:
        continued = fragment.rstrip().endswith("\\")
        if continued:
            fragment = fragment.rstrip()[:-1]
        targets.extend(fragment.split())
        if not continued:
            break
        try:
            fragment = next(lines)
        except StopIteration as exc:
            raise ValueError("unterminated GREAT_100_THEOREMS assignment") from exc
    return targets


def _sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _direct_needs(load_files):
    dependencies = []
    for load_file in load_files:
        source = (ROOT / load_file).read_text(encoding="utf-8")
        for dependency in NEEDS_RE.findall(source):
            if dependency not in dependencies:
                dependencies.append(dependency)
    return dependencies


def _theorem_request(target, load_files):
    """Resolve every requested OCaml binding in target load order."""
    requested_names = TARGET_THEOREMS.get(target)
    if not requested_names:
        raise ValueError(f"{target}: no named theorem request")

    declarations = {}
    for path in load_files:
        source = (ROOT / path).read_text(encoding="utf-8")
        for match in LET_BINDING_RE.finditer(source):
            name = match.group(1)
            declarations.setdefault(name, []).append({
                "path": path,
                "line": source.count("\n", 0, match.start()) + 1,
            })

    theorems = []
    for name in requested_names:
        declaration_name = name.rsplit(".", 1)[-1]
        occurrences = declarations.get(declaration_name, [])
        if not occurrences:
            raise ValueError(
                f"{target}: requested theorem binding is absent: {name}")
        theorem = {
            "name": name,
            "resolved_declaration": occurrences[-1],
            "shadowed_declarations": occurrences[:-1],
        }
        if "." in name:
            references = []
            reference_re = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(name)}"
                                      rf"(?![A-Za-z0-9_'])")
            for path in load_files:
                source = (ROOT / path).read_text(encoding="utf-8")
                references.extend({
                    "path": path,
                    "line": source.count("\n", 0, match.start()) + 1,
                } for match in reference_re.finditer(source))
            if not references:
                raise ValueError(
                    f"{target}: qualified theorem is never referenced: {name}")
            theorem["qualified_references"] = references
        theorems.append(theorem)

    review_note = MANUAL_REVIEW_MAPPINGS.get(target)
    return {
        "mapping_status": "manual_review" if review_note else "audited",
        "mapping_basis": AUDITED_MAPPING_RATIONALES.get(
            target, "named result declarations in ordered load files"),
        "review_note": review_note,
        "theorems": theorems,
        "identity_contract": {
            "serializer_wire": "candle structural fingerprint v2",
            "theorem": "canonical structural theorem serialization",
            "hypotheses": "canonical sorted structural term serializations",
            "assumptions": "canonical sorted global HOL axiom serializations",
            "post_state": (
                "canonical sorted type declarations, term declarations, "
                "primitive definition theorems, and global axioms"
            ),
        },
        "expected_identities": None,
    }


def build_manifest():
    names = _great_100_targets((ROOT / "holtest.mk").read_text(encoding="utf-8"))
    unknown_mapping_targets = set(TARGET_THEOREMS) - set(names)
    if unknown_mapping_targets:
        raise ValueError(
            "named theorem requests are not Great 100 targets: "
            + ", ".join(sorted(unknown_mapping_targets)))
    targets = []
    covered_sources = set()
    for name in names:
        load_files = SPECIAL_LOAD_FILES.get(name, [f"{name}.ml"])
        missing = [path for path in load_files if not (ROOT / path).is_file()]
        if missing:
            raise ValueError(f"{name}: missing load files: {', '.join(missing)}")
        covered_sources.update(load_files)
        observation = BASELINE_OBSERVATIONS.get(name)
        fingerprint_status = (
            "not_reached"
            if observation and observation["status"] != "pass"
            else "missing"
        )
        fingerprint_request = _theorem_request(name, load_files)
        targets.append({
            "name": name,
            "load_files": load_files,
            "load_file_sha256": {
                path: _sha256(ROOT / path) for path in load_files
            },
            "direct_needs": _direct_needs(load_files),
            "expected_status": "pass",
            "skip": None,
            "fingerprint_request": {
                **fingerprint_request,
                "expected_identities": None,
            },
            "fingerprints": {
                "status": fingerprint_status,
                "theorems": None,
                "assumptions": None,
                "post_state": None,
            },
            "baseline_observation": observation,
        })

    approval, approval_sha256, expected_identities, inventory_sha256 = \
        _load_identity_approval(targets)
    for target in targets:
        target["fingerprint_request"]["expected_identities"] = \
            expected_identities.get(target["name"])

    all_sources = {
        path.relative_to(ROOT).as_posix() for path in (ROOT / "100").glob("*.ml")
    }
    exclusions = [{
        "path": path,
        "reason": "absent_from_upstream_GREAT_100_THEOREMS",
        "approval_status": "unreviewed",
        "flyspeck_dependency_impact": "unassessed",
    } for path in sorted(all_sources - covered_sources)]

    return {
        "schema_version": 1,
        "suite": "HOL Light Great 100",
        "suite_semantics": (
            "The historical Great 100 suite has 65 clean-process execution "
            "targets over 66 source files; the name does not imply 100 runner entries."
        ),
        "audited_tree_base": AUDITED_BASE_COMMIT,
        "inventory_source": {
            "path": "holtest.mk",
            "variable": "GREAT_100_THEOREMS",
        },
        "dependency_scan": "direct literal needs \"path\";; calls in load_files",
        "inventory_contract": {
            "schema": "candle-great100-inventory-contract-v1",
            "sha256": inventory_sha256,
            "target_count": 65,
            "covered_source_count": 66,
            "theorem_request_count": 97,
        },
        "identity_approval": {
            "path": IDENTITY_APPROVAL.relative_to(ROOT).as_posix(),
            "sha256": approval_sha256,
            "schema": approval["schema"],
            "approval_status": approval["approval_status"],
            "promotion_allowed": approval["promotion_allowed"],
        },
        "execution_contract": {
            "baseline": "hol.ml",
            "isolation": "fresh Candle process per target",
            "cache_policy": "no theorem-state reuse between targets",
            "recorded_live_baseline_timeout_policy": {
                "boot_inactivity_timeout_seconds": 30,
                "load_inactivity_timeout_seconds": 1800,
                "inactivity_resets_on": (
                    "each recognized Loading, val, or Finished progress event"
                ),
                "total_wall_timeout_seconds": None,
                "wall_policy": "unbounded",
                "note": (
                    "The live runner left boot at pexpect's 30-second default. "
                    "Its --timeout 1800 applied to every subsequent expect "
                    "wait, so progress reset the load inactivity clock and no "
                    "total per-target deadline applied."
                ),
            },
        },
        "target_count": len(targets),
        "covered_source_count": len(covered_sources),
        "targets": targets,
        "excluded_100_sources": exclusions,
    }


def _render(payload):
    return json.dumps(payload, indent=2, ensure_ascii=False) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true", help="regenerate the manifest")
    action.add_argument("--check", action="store_true", help="verify the committed manifest")
    args = parser.parse_args()

    expected = _render(build_manifest())
    if args.write:
        MANIFEST.write_text(expected, encoding="utf-8")
        print(f"wrote {MANIFEST}")
        return 0

    try:
        actual = MANIFEST.read_text(encoding="utf-8")
    except FileNotFoundError:
        print(f"missing manifest: {MANIFEST}", file=sys.stderr)
        return 1
    if actual != expected:
        print(
            f"stale manifest: run {Path(__file__).name} --write",
            file=sys.stderr,
        )
        return 1
    payload = json.loads(actual)
    print(
        f"manifest ok: {payload['target_count']} targets, "
        f"{payload['covered_source_count']} source files, "
        f"{len(payload['excluded_100_sources'])} exclusion(s)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
