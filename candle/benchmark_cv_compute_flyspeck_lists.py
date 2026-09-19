#!/usr/bin/env python3
"""Wall-clock the two theorem-producing list_of_faces paths in one clean REPL.

Candle's Sys.time is intentionally deterministic, so this controller measures
only the interval between a command write and its unique completion marker.
The HOL file has already warmed and compared both paths before emitting READY.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import selectors
import statistics
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent.parent
BINARY = Path(os.environ.get("CANDLE_BINARY", ROOT / "candle/build/cake"))
RUNTIME_CWD = Path(os.environ.get("CANDLE_RUNTIME_CWD", ROOT))
SUPPORT_ROOT = Path(os.environ.get("CANDLE_SUPPORT_ROOT", ROOT))
REPETITIONS = int(os.environ.get("CANDLE_CV_REPETITIONS", "50"))
TIMEOUT = float(os.environ.get("CANDLE_CV_TIMEOUT_SECONDS", "1800"))


def quote(value: Path) -> str:
    return str(value).replace("\\", "\\\\").replace('"', '\\"')


def main() -> int:
    process = subprocess.Popen(
        [str(BINARY), "--candle"],
        cwd=RUNTIME_CWD,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        bufsize=0,
    )
    assert process.stdin is not None
    assert process.stdout is not None
    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ)
    pending = bytearray()
    transcript_tail = bytearray()

    def send(source: str) -> None:
        process.stdin.write(source.encode())
        process.stdin.flush()

    def await_marker(marker: str, deadline: float) -> None:
        target = marker.encode()
        while target not in pending:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(f"timeout waiting for {marker!r}")
            events = selector.select(min(remaining, 1.0))
            if not events:
                if process.poll() is not None:
                    raise RuntimeError(
                        f"Candle exited {process.returncode} before {marker!r}"
                    )
                continue
            chunk = os.read(process.stdout.fileno(), 65536)
            if not chunk:
                raise RuntimeError(f"Candle closed stdout before {marker!r}")
            pending.extend(chunk)
            transcript_tail.extend(chunk)
            if len(transcript_tail) > 131072:
                del transcript_tail[:-131072]
        end = pending.index(target) + len(target)
        del pending[:end]

    def sample(label: str, function: str, ordinal: int) -> float:
        marker = f"CANDLE_CV_BENCH_DONE:{label}:{ordinal}"
        source = (
            f'let _ = candle_cv_repeat {REPETITIONS} {function} '
            "candle_cv_adapter_input (REFL candle_cv_adapter_input) in "
            f'print_endline "{marker}";;\n'
        )
        started = time.perf_counter()
        send(source)
        await_marker(marker, time.monotonic() + TIMEOUT)
        return time.perf_counter() - started

    try:
        send(
            f'Cakeml.loadPath := ["{quote(ROOT)}"; '
            f'"{quote(SUPPORT_ROOT)}"; Filename.currentDir];;\n'
            '#use "hol.ml";;\n'
            f'#use "{quote(ROOT / "candle/test_cv_compute_flyspeck_lists_adapter.ml")}";;\n'
        )
        await_marker(
            "CANDLE_CV_FLYSPECK_LIST_BENCH_READY",
            time.monotonic() + TIMEOUT,
        )

        existing: list[float] = []
        reflected: list[float] = []
        schedule = [
            ("existing", "eval_list_of_faces"),
            ("reflected", "candle_cv_list_of_faces_conv"),
            ("reflected", "candle_cv_list_of_faces_conv"),
            ("existing", "eval_list_of_faces"),
            ("existing", "eval_list_of_faces"),
            ("reflected", "candle_cv_list_of_faces_conv"),
        ]
        counts = {"existing": 0, "reflected": 0}
        for label, function in schedule:
            counts[label] += 1
            elapsed = sample(label, function, counts[label])
            (existing if label == "existing" else reflected).append(elapsed)

        existing_median = statistics.median(existing)
        reflected_median = statistics.median(reflected)
        result = {
            "schema": 1,
            "claim": "development/non-release focused wall-clock benchmark",
            "input": {
                "faces": 18,
                "total_face_list_length": 58,
            },
            "repetitions_per_sample": REPETITIONS,
            "samples_seconds": {
                "existing": existing,
                "reflected": reflected,
            },
            "median_seconds": {
                "existing": existing_median,
                "reflected": reflected_median,
            },
            "reflected_over_existing": reflected_median / existing_median,
        }
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    except Exception as error:
        sys.stderr.write(f"benchmark failed: {error}\n")
        sys.stderr.write(transcript_tail.decode(errors="replace"))
        return 1
    finally:
        if process.poll() is None:
            process.stdin.close()
            try:
                process.wait(timeout=30)
            except subprocess.TimeoutExpired:
                process.terminate()
                process.wait(timeout=30)


if __name__ == "__main__":
    raise SystemExit(main())
