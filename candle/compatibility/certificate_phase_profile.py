#!/usr/bin/env python3
"""Externally time flushed Candle certificate phase markers.

Candle's selected runtime intentionally has no nondeterministic clock or GC
telemetry.  This observer timestamps log markers and samples Linux /proc.  It
never writes to the proof process or its checkpoint.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import time


MARKER = re.compile(
    r"CANDLE_CERT_PROFILE lane=(?P<lane>\S+) scope=(?P<scope>.*?) "
    r"phase=(?P<phase>\S+) event=(?P<event>begin|end|fail)"
)


def proc_sample(pid: int, ticks: int) -> dict[str, float | int] | None:
    try:
        stat_fields = Path(f"/proc/{pid}/stat").read_text().split()
        status = Path(f"/proc/{pid}/status").read_text().splitlines()
    except (FileNotFoundError, ProcessLookupError):
        return None
    values: dict[str, int] = {}
    for line in status:
        if line.startswith(("VmRSS:", "VmHWM:", "VmSize:")):
            name, value, _unit = line.split()
            values[name[:-1]] = int(value)
    return {
        "cpu_seconds": (int(stat_fields[13]) + int(stat_fields[14])) / ticks,
        "rss_kib": values.get("VmRSS", 0),
        "hwm_kib": values.get("VmHWM", 0),
        "vmsize_kib": values.get("VmSize", 0),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pid", type=int, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--poll-seconds", type=float, default=0.05)
    parser.add_argument(
        "--stop-key",
        help="stop after lane/scope/phase end, for example lp/certificate/total",
    )
    parser.add_argument("--wait-for-log-seconds", type=float, default=60.0)
    args = parser.parse_args()

    deadline = time.monotonic() + args.wait_for_log_seconds
    while not args.log.exists():
        if time.monotonic() >= deadline:
            raise SystemExit(f"log did not appear: {args.log}")
        time.sleep(min(args.poll_seconds, 0.1))

    ticks = os.sysconf("SC_CLK_TCK")
    start_ns = time.monotonic_ns()
    events: list[dict[str, object]] = []
    samples: list[dict[str, object]] = []
    peak_rss_kib = 0
    phase_begins: dict[tuple[str, str, str], dict[str, object]] = {}
    phases: list[dict[str, object]] = []
    stop_seen = False

    with args.log.open("r", encoding="utf-8", errors="replace") as log:
        while True:
            where = log.tell()
            line = log.readline()
            now_ns = time.monotonic_ns()
            proc = proc_sample(args.pid, ticks)
            if proc is not None:
                peak_rss_kib = max(peak_rss_kib, int(proc["rss_kib"]))
                samples.append(
                    {
                        "elapsed_seconds": (now_ns - start_ns) / 1e9,
                        **proc,
                    }
                )
            if line:
                match = MARKER.search(line)
                if match:
                    item: dict[str, object] = {
                        **match.groupdict(),
                        "elapsed_seconds": (now_ns - start_ns) / 1e9,
                        "utc": dt.datetime.now(dt.timezone.utc).isoformat(),
                        "log_offset": where,
                        "process": proc,
                    }
                    events.append(item)
                    key = (match["lane"], match["scope"], match["phase"])
                    if match["event"] == "begin":
                        if key in phase_begins:
                            raise SystemExit(f"duplicate open phase: {key}")
                        phase_begins[key] = item
                    elif match["event"] in {"end", "fail"}:
                        begin = phase_begins.pop(key, None)
                        if begin is None:
                            raise SystemExit(f"phase ended without begin: {key}")
                        begin_proc = begin.get("process") or {}
                        end_proc = proc or {}
                        phases.append(
                            {
                                "lane": key[0],
                                "scope": key[1],
                                "phase": key[2],
                                "result": match["event"],
                                "wall_seconds": float(item["elapsed_seconds"])
                                - float(begin["elapsed_seconds"]),
                                "cpu_seconds": float(end_proc.get("cpu_seconds", 0.0))
                                - float(begin_proc.get("cpu_seconds", 0.0)),
                                "rss_begin_kib": int(begin_proc.get("rss_kib", 0)),
                                "rss_end_kib": int(end_proc.get("rss_kib", 0)),
                            }
                        )
                    if (
                        args.stop_key
                        and match["event"] == "end"
                        and "/".join(key) == args.stop_key
                    ):
                        stop_seen = True
                continue

            if stop_seen:
                break
            if proc is None:
                # Drain anything written immediately before process exit.
                time.sleep(args.poll_seconds)
                line = log.readline()
                if not line:
                    break
                log.seek(where)
                continue
            time.sleep(args.poll_seconds)

    result = {
        "schema": "candle-certificate-phase-profile-v1",
        "pid": args.pid,
        "log": str(args.log.resolve()),
        "poll_seconds": args.poll_seconds,
        "stop_key": args.stop_key,
        "stop_seen": stop_seen,
        "duration_seconds": (time.monotonic_ns() - start_ns) / 1e9,
        "peak_sampled_rss_kib": peak_rss_kib,
        "events": events,
        "phases": phases,
        "unclosed_phases": ["/".join(key) for key in phase_begins],
        "samples": samples,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    temporary.replace(args.output)
    print(
        f"profile={args.output} events={len(events)} phases={len(phases)} "
        f"peak_rss_kib={peak_rss_kib}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
