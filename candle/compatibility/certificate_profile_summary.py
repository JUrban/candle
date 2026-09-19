#!/usr/bin/env python3
"""Summarize a certificate_phase_profile.py JSON result."""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import statistics


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("profile", type=Path)
    args = parser.parse_args()
    profile = json.loads(args.profile.read_text())
    if profile.get("schema") != "candle-certificate-phase-profile-v1":
        raise SystemExit("unsupported profile schema")

    grouped: dict[tuple[str, str], list[dict[str, object]]] = defaultdict(list)
    for phase in profile["phases"]:
        scope = str(phase["scope"])
        scope_class = "terminal-*" if scope.startswith("terminal-") else scope
        grouped[(scope_class, str(phase["phase"]))].append(phase)

    print(
        "PROFILE_TOTAL "
        f"duration_seconds={profile['duration_seconds']:.6f} "
        f"peak_rss_gib={profile['peak_sampled_rss_kib'] / 1024 / 1024:.6f} "
        f"events={len(profile['events'])} phases={len(profile['phases'])} "
        f"stop_seen={str(profile['stop_seen']).lower()}"
    )
    for (scope, phase_name), rows in sorted(grouped.items()):
        walls = [float(row["wall_seconds"]) for row in rows]
        cpus = [float(row["cpu_seconds"]) for row in rows]
        print(
            "PROFILE_PHASE "
            f"scope={scope} phase={phase_name} count={len(rows)} "
            f"wall_sum={sum(walls):.6f} wall_median={statistics.median(walls):.6f} "
            f"wall_min={min(walls):.6f} wall_max={max(walls):.6f} "
            f"cpu_sum={sum(cpus):.6f} cpu_median={statistics.median(cpus):.6f}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
