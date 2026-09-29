#!/usr/bin/env python3
"""Validate and render an untrusted action-296 preparation-group schedule."""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re


RESULT_MARKER = "CANDLE_CV_ACTION296_BOUNDED_GROUPED_POLICY_RESULT"
OK_MARKER = "CANDLE_CV_ACTION296_BOUNDED_GROUPED_POLICY_OK DEVELOPMENT_NON_RELEASE"
RESULT_MARKERS = (
    RESULT_MARKER,
    "CANDLE_CV_ACTION296_FIXED_OUTER_GROUPED_DISCOVERY_RESULT",
)
OK_MARKERS = (
    OK_MARKER,
    "CANDLE_CV_ACTION296_FIXED_OUTER_GROUPED_DISCOVERY_OK DEVELOPMENT_NON_RELEASE",
)
RESULT_RE = re.compile(
    rf"^(?:{'|'.join(map(re.escape, RESULT_MARKERS))}) "
    r"original_leaves=(?P<original_leaves>\d+) "
    r"final_cells=(?P<final_cells>\d+) "
    r"attempts=(?P<attempts>\d+) "
    r"successful_groups=(?P<successful_groups>\d+) "
    r"group_sizes=(?P<group_sizes>\d+(?:,\d+)*) "
    r"theorem_digest=(?P<theorem_digest>[0-9a-f]{32})$"
)


@dataclass(frozen=True)
class GroupSchedule:
    original_leaves: int
    final_cells: int
    attempts: int
    successful_groups: int
    group_sizes: tuple[int, ...]
    theorem_digest: str


def parse_result(line: str) -> GroupSchedule:
    positions = [
        line.find(marker) for marker in RESULT_MARKERS if marker in line
    ]
    where = -1 if not positions else min(positions)
    if where < 0:
        raise ValueError("line does not contain a grouped-policy result")
    match = RESULT_RE.fullmatch(line[where:].strip())
    if match is None:
        raise ValueError(f"malformed grouped-policy result: {line.rstrip()}")
    schedule = GroupSchedule(
        original_leaves=int(match["original_leaves"]),
        final_cells=int(match["final_cells"]),
        attempts=int(match["attempts"]),
        successful_groups=int(match["successful_groups"]),
        group_sizes=tuple(
            int(value) for value in match["group_sizes"].split(",")
        ),
        theorem_digest=match["theorem_digest"],
    )
    validate_schedule(schedule)
    return schedule


def validate_schedule(schedule: GroupSchedule) -> None:
    if schedule.original_leaves <= 0:
        raise ValueError("group schedule has no original leaves")
    if schedule.final_cells < schedule.original_leaves:
        raise ValueError("group schedule has too few final cells")
    if any(size <= 0 for size in schedule.group_sizes):
        raise ValueError("group schedule contains a nonpositive size")
    if len(schedule.group_sizes) != schedule.successful_groups:
        raise ValueError("group schedule success count mismatch")
    if sum(schedule.group_sizes) != schedule.original_leaves:
        raise ValueError("group schedule leaf count mismatch")
    if schedule.attempts < schedule.successful_groups:
        raise ValueError("group schedule attempt count mismatch")


def read_schedule(path: Path) -> GroupSchedule:
    text = path.read_text(encoding="utf-8", errors="strict")
    if not any(marker in text for marker in OK_MARKERS):
        raise ValueError(f"incomplete grouped-policy log: {path}")
    results = [
        parse_result(line)
        for line in text.splitlines()
        if any(marker in line for marker in RESULT_MARKERS)
    ]
    if len(results) != 1:
        raise ValueError(
            f"expected one grouped-policy result, found {len(results)}"
        )
    return results[0]


def render_ml(schedule: GroupSchedule) -> str:
    sizes = ";".join(str(size) for size in schedule.group_sizes)
    return (
        "(* Generated untrusted action-296 preparation-group schedule. *)\n"
        f"let candle_action296_generated_group_sizes = [{sizes}];;\n"
    )


def _identity(path: Path) -> dict[str, object]:
    data = path.read_bytes()
    return {
        "path": str(path.resolve()),
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def render_json(schedule: GroupSchedule, path: Path) -> str:
    payload = {
        "schema": "candle-action296-untrusted-group-schedule-v1",
        "status": "development-non-release",
        "claim": "untrusted plan only; reflected replay remains authoritative",
        "discovery_log": _identity(path),
        "schedule": asdict(schedule),
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-ml", type=Path, required=True)
    args = parser.parse_args()
    schedule = read_schedule(args.log)
    args.output_json.write_text(
        render_json(schedule, args.log), encoding="utf-8"
    )
    args.output_ml.write_text(render_ml(schedule), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
