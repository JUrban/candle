"""Stdlib-only structural fingerprint request and parsing contract."""

import hashlib
import json
from pathlib import Path
import re


CANDLE_ROOT = Path(__file__).resolve().parent.parent
FINGERPRINT_MARKER = "CANDLE_FINGERPRINT_V2"
STATE_FINGERPRINT_MARKER = "CANDLE_STATE_FINGERPRINT_V2"
PROCESS_MARKER = "CANDLE_GREAT100_PROCESS_V1"
FINGERPRINT_HELPER = CANDLE_ROOT / "candle" / "fingerprint.ml"
OCAML_VALUE_PATH_RE = re.compile(
    r"^[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)*$")
EMPTY_HYPOTHESES_WIRE = b"4:list1:0"


class LoadFailure(Exception):
    """A structural fingerprint transcript is invalid."""


def _fingerprint_request_source(theorem_names, suite_nonce=None,
                                process_nonce=None):
    lines = []
    for name in theorem_names:
        if not OCAML_VALUE_PATH_RE.fullmatch(name):
            raise ValueError(f"unsafe theorem value path in manifest: {name!r}")
        lines.append(f'candle_s1_emit_fingerprint "{name}" {name};;')
    lines.append("candle_s1_emit_state_fingerprint ();;")
    if suite_nonce is not None or process_nonce is not None:
        if (not re.fullmatch(r"[0-9a-f]{64}", suite_nonce or "") or
                not re.fullmatch(r"[0-9a-f]{64}", process_nonce or "")):
            raise ValueError("invalid Great 100 process marker nonce")
        marker = f"{PROCESS_MARKER}\t{suite_nonce}\t{process_nonce}\tCOMPLETE"
        lines.append(f"print_endline ({json.dumps(marker)});;")
    return "\n".join(lines) + "\n"


def _decode_fingerprint_hex(field, label):
    """Decode one fail-closed lowercase-hex wire field."""
    if not re.fullmatch(r"(?:[0-9a-f]{2})*", field):
        raise LoadFailure(f"malformed hexadecimal fingerprint field: {label}")
    return bytes.fromhex(field)


def _identity_sha256(serialized):
    return hashlib.sha256(serialized).hexdigest()


def _match_expected_identities(records, post_state, expected_identities,
                               serializer_sha256, mapping_status):
    """Fail closed unless every approved structural identity matches exactly."""
    if expected_identities is None:
        return "observed_uncompared", False
    if mapping_status != "audited":
        raise LoadFailure(
            "expected fingerprints cannot approve a manual-review mapping")
    if set(expected_identities) != {
            "approval_sha256", "serializer_sha256", "theorems", "post_state"}:
        raise LoadFailure("malformed expected fingerprint identity object")
    if not re.fullmatch(r"[0-9a-f]{64}", expected_identities["approval_sha256"]):
        raise LoadFailure("malformed expected fingerprint approval identity")
    if expected_identities["serializer_sha256"] != serializer_sha256:
        raise LoadFailure("expected fingerprint serializer identity mismatch")
    if expected_identities["theorems"] != records:
        raise LoadFailure("observed theorem or global-axiom fingerprint mismatch")
    if expected_identities["post_state"] != post_state:
        raise LoadFailure("observed post-load kernel-state fingerprint mismatch")
    return "matched", True


def _read_fingerprint_records(log_path, theorem_names, mapping_status,
                              expected_identities=None):
    """Parse structural identities emitted by candle/fingerprint.ml."""
    lines = Path(log_path).read_text(encoding="utf-8").splitlines()
    records = {}
    state_records = []
    for line in lines:
        if not line.startswith(FINGERPRINT_MARKER + "\t"):
            continue
        fields = line.split("\t")
        if len(fields) != 8:
            raise LoadFailure(
                f"malformed {FINGERPRINT_MARKER} record with "
                f"{len(fields)} fields")
        (_, name_hex, theorem_hex, hypotheses_hex, conclusion_hex,
         assumptions_hex, hypothesis_count, assumption_count) = fields
        name_bytes = _decode_fingerprint_hex(name_hex, "name")
        try:
            name = name_bytes.decode("ascii")
        except UnicodeDecodeError as error:
            raise LoadFailure("non-ASCII theorem name in fingerprint") from error
        if name in records:
            raise LoadFailure(f"duplicate theorem fingerprint: {name}")
        theorem = _decode_fingerprint_hex(theorem_hex, "theorem")
        hypotheses = _decode_fingerprint_hex(hypotheses_hex, "hypotheses")
        conclusion = _decode_fingerprint_hex(conclusion_hex, "conclusion")
        assumptions = _decode_fingerprint_hex(assumptions_hex, "assumptions")
        try:
            parsed_hypothesis_count = int(hypothesis_count)
            parsed_assumption_count = int(assumption_count)
        except ValueError as error:
            raise LoadFailure(
                f"non-numeric fingerprint count for {name}") from error
        if (parsed_hypothesis_count != 0 or
                hypotheses != EMPTY_HYPOTHESES_WIRE):
            raise LoadFailure(f"Great 100 theorem is not closed: {name}")
        if parsed_assumption_count != 3:
            raise LoadFailure(
                f"Great 100 theorem does not use exactly three axioms: {name}")
        records[name] = {
            "name": name,
            "theorem_sha256": _identity_sha256(theorem),
            "hypotheses_sha256": _identity_sha256(hypotheses),
            "conclusion_sha256": _identity_sha256(conclusion),
            "global_axioms_sha256": _identity_sha256(assumptions),
            "hypothesis_count": parsed_hypothesis_count,
            "global_axiom_count": parsed_assumption_count,
        }
    for line in lines:
        if not line.startswith(STATE_FINGERPRINT_MARKER + "\t"):
            continue
        fields = line.split("\t")
        if len(fields) != 10:
            raise LoadFailure(
                f"malformed {STATE_FINGERPRINT_MARKER} record with "
                f"{len(fields)} fields")
        serialized = [
            _decode_fingerprint_hex(field, label)
            for field, label in zip(fields[1:6], (
                "kernel state", "type constants", "term constants",
                "definitions", "state axioms"))
        ]
        try:
            counts = [int(field) for field in fields[6:10]]
        except ValueError as error:
            raise LoadFailure("non-numeric post-state fingerprint count") from error
        if any(count < 0 for count in counts):
            raise LoadFailure("negative post-state fingerprint count")
        state_records.append({
            "kernel_state_sha256": _identity_sha256(serialized[0]),
            "type_constants_sha256": _identity_sha256(serialized[1]),
            "term_constants_sha256": _identity_sha256(serialized[2]),
            "definitions_sha256": _identity_sha256(serialized[3]),
            "global_axioms_sha256": _identity_sha256(serialized[4]),
            "type_constant_count": counts[0],
            "term_constant_count": counts[1],
            "definition_count": counts[2],
            "global_axiom_count": counts[3],
        })

    expected = list(theorem_names)
    missing = [name for name in expected if name not in records]
    unexpected = [name for name in records if name not in expected]
    if missing or unexpected:
        raise LoadFailure(
            "fingerprint request mismatch: "
            f"missing={missing}, unexpected={unexpected}")

    axiom_identities = {
        (record["global_axioms_sha256"], record["global_axiom_count"])
        for record in records.values()
    }
    if len(axiom_identities) != 1:
        raise LoadFailure("global axiom identity changed between theorem requests")
    if len(state_records) != 1:
        raise LoadFailure(
            f"expected exactly one post-state fingerprint; got {len(state_records)}")
    post_state = state_records[0]
    if next(iter(axiom_identities)) != (
            post_state["global_axioms_sha256"],
            post_state["global_axiom_count"]):
        raise LoadFailure("theorem and post-state global axiom identity mismatch")
    if post_state["global_axiom_count"] != 3:
        raise LoadFailure("post-state does not contain exactly three global axioms")

    serializer_sha256 = hashlib.sha256(FINGERPRINT_HELPER.read_bytes()).hexdigest()
    ordered_records = [records[name] for name in expected]
    status, expected_present = _match_expected_identities(
        ordered_records, post_state, expected_identities, serializer_sha256,
        mapping_status)
    return {
        "status": status,
        "mapping_status": mapping_status,
        "expected_identities_present": expected_present,
        "serializer": {
            "path": FINGERPRINT_HELPER.relative_to(CANDLE_ROOT).as_posix(),
            "sha256": serializer_sha256,
        },
        "theorems": ordered_records,
        "post_state": post_state,
        "approval_sha256": (
            expected_identities["approval_sha256"]
            if expected_identities is not None else None),
    }

