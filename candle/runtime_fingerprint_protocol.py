"""Stdlib-only V3 fingerprint protocol for final Candle Great100 runs.

Native reference collection retains aggregate V3 records so its existing
candidate evidence can be replayed byte for byte.  Candle emits the identical
logical state wire in bounded chunks, avoiding construction and hex expansion
of one very large aggregate state string in the CakeML runtime.
"""

import hashlib
import json
from pathlib import Path
import re


CANDLE_ROOT = Path(__file__).resolve().parent.parent
FINGERPRINT_MARKER = "CANDLE_FINGERPRINT_V3"
STATE_FINGERPRINT_MARKER = "CANDLE_STATE_FINGERPRINT_V3_STREAM_BEGIN"
PROCESS_MARKER = "CANDLE_GREAT100_PROCESS_V1"
FINGERPRINT_HELPER = CANDLE_ROOT / "candle" / "fingerprint.ml"
STATE_STREAM_HELPER = CANDLE_ROOT / "candle" / "fingerprint_v3_state_stream.ml"
OCAML_VALUE_PATH_RE = re.compile(
    r"^[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)*$")
EMPTY_HYPOTHESES_WIRE = b"4:list1:0"
DECIMAL_RE = re.compile(r"(?:0|[1-9][0-9]*)")
LOWER_HEX_RE = re.compile(r"(?:[0-9a-f]{2})+")
STREAM_COMPONENT_BEGIN = "CANDLE_STATE_FINGERPRINT_V3_STREAM_COMPONENT_BEGIN"
STREAM_CHUNK = "CANDLE_STATE_FINGERPRINT_V3_STREAM_CHUNK"
STREAM_COMPONENT_END = "CANDLE_STATE_FINGERPRINT_V3_STREAM_COMPONENT_END"
STREAM_END = "CANDLE_STATE_FINGERPRINT_V3_STREAM_END"
STREAM_COMPONENTS = (
    "type_constants", "term_constants", "definitions", "global_axioms")
STATE_STREAM_MARKERS = (
    STATE_FINGERPRINT_MARKER, STREAM_COMPONENT_BEGIN, STREAM_CHUNK,
    STREAM_COMPONENT_END, STREAM_END)


class LoadFailure(Exception):
    """A structural fingerprint transcript is invalid."""


def _fingerprint_request_source(theorem_names, suite_nonce=None,
                                process_nonce=None):
    lines = []
    for name in theorem_names:
        if not OCAML_VALUE_PATH_RE.fullmatch(name):
            raise ValueError(f"unsafe theorem value path in manifest: {name!r}")
        lines.append(f'candle_s1_emit_fingerprint "{name}" {name};;')
    lines.append("candle_s1_emit_state_fingerprint_v3_stream ();;")
    if suite_nonce is not None or process_nonce is not None:
        if (not re.fullmatch(r"[0-9a-f]{64}", suite_nonce or "") or
                not re.fullmatch(r"[0-9a-f]{64}", process_nonce or "")):
            raise ValueError("invalid Great 100 process marker nonce")
        marker = f"{PROCESS_MARKER}\t{suite_nonce}\t{process_nonce}\tCOMPLETE"
        lines.append(f"print_endline ({json.dumps(marker)});;")
    return "\n".join(lines) + "\n"


def _decode_fingerprint_hex(field, label):
    if not re.fullmatch(r"(?:[0-9a-f]{2})*", field):
        raise LoadFailure(f"malformed hexadecimal fingerprint field: {label}")
    return bytes.fromhex(field)


def _identity_sha256(serialized):
    return hashlib.sha256(serialized).hexdigest()


def _field_wire(value):
    return str(len(value)).encode("ascii") + b":" + value


def _nonnegative(value, label):
    if not isinstance(value, str) or DECIMAL_RE.fullmatch(value) is None:
        raise LoadFailure(f"noncanonical decimal in {label}")
    return int(value)


def _is_supported_state_fingerprint_line(line):
    return line == STREAM_END or any(
        line.startswith(marker + "\t") for marker in STATE_STREAM_MARKERS[:-1])


class _StateStreamReader:
    def __init__(self):
        self.started = False
        self.ended = False
        self.lengths = None
        self.counts = None
        self.kernel_length = None
        self.kernel_digest = hashlib.sha256()
        self.kernel_bytes = 0
        self.component_index = 0
        self.active = None
        self.component_identities = {}

    def begin(self, fields):
        if self.started or len(fields) != 10:
            raise LoadFailure("malformed or duplicate V3 stream begin")
        values = [
            _nonnegative(field, f"V3 stream begin field {index}")
            for index, field in enumerate(fields[1:], 1)
        ]
        self.kernel_length, *rest = values
        self.lengths = dict(zip(STREAM_COMPONENTS, rest[:4]))
        self.counts = dict(zip((
            "type_constant_count", "term_constant_count",
            "definition_count", "global_axiom_count"), rest[4:]))
        header = _field_wire(b"kernel-state") + _field_wire(b"4")
        self.kernel_digest.update(header)
        self.kernel_bytes = len(header)
        self.started = True

    def component_begin(self, fields):
        if (not self.started or self.ended or self.active is not None or
                len(fields) != 3 or
                self.component_index >= len(STREAM_COMPONENTS)):
            raise LoadFailure("malformed V3 component begin")
        name = fields[1]
        expected_name = STREAM_COMPONENTS[self.component_index]
        if name != expected_name:
            raise LoadFailure(
                f"out-of-order V3 component: {name!r}, expected {expected_name!r}")
        length = _nonnegative(fields[2], f"{name} length")
        if length != self.lengths[name]:
            raise LoadFailure(f"V3 {name} begin length mismatch")
        prefix = str(length).encode("ascii") + b":"
        self.kernel_digest.update(prefix)
        self.kernel_bytes += len(prefix)
        self.active = {
            "name": name,
            "length": length,
            "received": 0,
            "chunks": 0,
            "digest": hashlib.sha256(),
        }

    def chunk(self, fields):
        if self.active is None or len(fields) != 4:
            raise LoadFailure("V3 chunk outside a component")
        name = fields[1]
        if name != self.active["name"]:
            raise LoadFailure("V3 chunk component mismatch")
        sequence = _nonnegative(fields[2], f"{name} chunk sequence")
        if sequence != self.active["chunks"]:
            raise LoadFailure(f"V3 {name} chunk sequence mismatch")
        if LOWER_HEX_RE.fullmatch(fields[3]) is None:
            raise LoadFailure(f"malformed or empty V3 {name} chunk")
        raw = bytes.fromhex(fields[3])
        self.active["received"] += len(raw)
        if self.active["received"] > self.active["length"]:
            raise LoadFailure(f"V3 {name} exceeds declared length")
        self.active["chunks"] += 1
        self.active["digest"].update(raw)
        self.kernel_digest.update(raw)
        self.kernel_bytes += len(raw)

    def component_end(self, fields):
        if self.active is None or len(fields) != 4:
            raise LoadFailure("V3 component end without begin")
        name = fields[1]
        length = _nonnegative(fields[2], f"{name} end length")
        chunks = _nonnegative(fields[3], f"{name} end chunk count")
        if (name != self.active["name"] or length != self.active["length"] or
                length != self.active["received"] or
                chunks != self.active["chunks"]):
            raise LoadFailure(f"V3 {name} component end mismatch")
        self.component_identities[name + "_sha256"] = \
            self.active["digest"].hexdigest()
        self.active = None
        self.component_index += 1

    def end(self, fields):
        if (len(fields) != 1 or not self.started or self.ended or
                self.active is not None or
                self.component_index != len(STREAM_COMPONENTS)):
            raise LoadFailure("malformed V3 stream end")
        self.ended = True

    def finish(self):
        if not self.started or not self.ended:
            raise LoadFailure("incomplete V3 state stream")
        if self.kernel_bytes != self.kernel_length:
            raise LoadFailure("V3 reconstructed kernel length mismatch")
        return {
            "kernel_state_sha256": self.kernel_digest.hexdigest(),
            **self.component_identities,
            **self.counts,
        }


def _match_expected_identities(records, post_state, expected_identities,
                               serializer_sha256, mapping_status):
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
    """Hash exact V3 theorem records and reconstruct the chunked state wire."""
    records = {}
    state = _StateStreamReader()
    with Path(log_path).open("r", encoding="utf-8") as source:
        for number, raw_line in enumerate(source, 1):
            line = raw_line.rstrip("\r\n")
            if line.startswith(FINGERPRINT_MARKER + "\t"):
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
                    raise LoadFailure(
                        "non-ASCII theorem name in fingerprint") from error
                if name in records:
                    raise LoadFailure(f"duplicate theorem fingerprint: {name}")
                theorem = _decode_fingerprint_hex(theorem_hex, "theorem")
                hypotheses = _decode_fingerprint_hex(
                    hypotheses_hex, "hypotheses")
                conclusion = _decode_fingerprint_hex(conclusion_hex, "conclusion")
                assumptions = _decode_fingerprint_hex(
                    assumptions_hex, "assumptions")
                parsed_hypotheses = _nonnegative(
                    hypothesis_count, f"hypothesis count for {name}")
                parsed_assumptions = _nonnegative(
                    assumption_count, f"axiom count for {name}")
                if parsed_hypotheses != 0 or hypotheses != EMPTY_HYPOTHESES_WIRE:
                    raise LoadFailure(f"Great 100 theorem is not closed: {name}")
                if parsed_assumptions != 3:
                    raise LoadFailure(
                        f"Great 100 theorem does not use exactly three axioms: {name}")
                records[name] = {
                    "name": name,
                    "theorem_sha256": _identity_sha256(theorem),
                    "hypotheses_sha256": _identity_sha256(hypotheses),
                    "conclusion_sha256": _identity_sha256(conclusion),
                    "global_axioms_sha256": _identity_sha256(assumptions),
                    "hypothesis_count": parsed_hypotheses,
                    "global_axiom_count": parsed_assumptions,
                }
            elif line.startswith(STATE_FINGERPRINT_MARKER + "\t"):
                state.begin(line.split("\t"))
            elif line.startswith(STREAM_COMPONENT_BEGIN + "\t"):
                state.component_begin(line.split("\t"))
            elif line.startswith(STREAM_CHUNK + "\t"):
                state.chunk(line.split("\t"))
            elif line.startswith(STREAM_COMPONENT_END + "\t"):
                state.component_end(line.split("\t"))
            elif line == STREAM_END:
                state.end([line])
            elif line.startswith("CANDLE_FINGERPRINT_V"):
                raise LoadFailure(
                    f"unsupported theorem fingerprint record at line {number}")
            elif line.startswith("CANDLE_STATE_FINGERPRINT_V"):
                raise LoadFailure(
                    f"unsupported state fingerprint record at line {number}")

    expected = list(theorem_names)
    missing = [name for name in expected if name not in records]
    unexpected = [name for name in records if name not in expected]
    if missing or unexpected:
        raise LoadFailure(
            f"fingerprint request mismatch: missing={missing}, "
            f"unexpected={unexpected}")
    post_state = state.finish()
    axiom_identities = {
        (record["global_axioms_sha256"], record["global_axiom_count"])
        for record in records.values()
    }
    if len(axiom_identities) != 1:
        raise LoadFailure("global axiom identity changed between theorem requests")
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
