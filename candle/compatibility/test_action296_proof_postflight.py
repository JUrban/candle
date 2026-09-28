import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import action296_proof_postflight as postflight
import action296_group_schedule


DIGEST = "0123456789abcdef0123456789abcdef"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_manifest(path: Path, targets: list[Path]) -> None:
    path.write_text(
        "".join(f"{sha256(target)}  {target.resolve()}\n" for target in targets),
        encoding="utf-8",
    )


class Action296ProofPostflightTests(unittest.TestCase):
    def make_run(self, root: Path, mode: str, digest: str = DIGEST) -> Path:
        run = root / mode
        run.mkdir()
        fragment = run / "fragment.ml"
        fragment.write_text("let fixture = 1;;\n", encoding="utf-8")
        fragments = run / "fragments.sha256"
        write_manifest(fragments, [fragment])
        stdin = run / "stdin.ml"
        stdin.write_text("#use \"fragment.ml\";;\n", encoding="utf-8")
        if mode == "sequential":
            result = (
                "CANDLE_CV_ACTION296_POLICY_ADAPTIVE_PROOF_RESULT "
                f"original_leaves=8 final_cells=12 theorem_digest={digest}"
            )
            ok = postflight.SEQUENTIAL_OK
        else:
            result = (
                "CANDLE_CV_ACTION296_BOUNDED_GROUPED_POLICY_RESULT "
                "original_leaves=8 final_cells=12 attempts=5 "
                "successful_groups=3 group_sizes=4,2,2 "
                f"theorem_digest={digest}"
            )
            ok = action296_group_schedule.OK_MARKER
        log = run / "candle.log"
        log.write_text(f"# {result}\n# {ok}\n", encoding="utf-8")
        write_manifest(run / "result-files.sha256", [fragments, stdin, log])
        nonce = "a" * 64
        fragment_hash = sha256(fragments)
        (run / "input-ack.started").write_text(
            f"nonce={nonce}\nfragment_set_sha256={fragment_hash}\n"
            "started_utc=2026-09-28T00:00:00Z\n",
            encoding="utf-8",
        )
        (run / "input-ack.receipt").write_text(
            f"nonce={nonce}\nfragment_set_sha256={fragment_hash}\n"
            "ack_line=1\nmarker_line=2\n"
            "completed_utc=2026-09-28T00:01:00Z\n",
            encoding="utf-8",
        )
        (run / "phase-profile.json").write_text(json.dumps({
            "schema": "candle-certificate-phase-profile-v1",
            "log": str(log.resolve()),
            "stop_key": postflight.STOP_KEYS[mode],
            "stop_seen": True,
            "unclosed_phases": [],
            "events": [{"event": "begin"}, {"event": "end"}],
            "phases": [{"result": "end"}],
            "duration_seconds": 1.0,
            "peak_sampled_rss_kib": 100,
        }), encoding="utf-8")
        return run

    def test_valid_pair_matches(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sequential = postflight.validate_run(
                self.make_run(root, "sequential"),
                "sequential", 8, 12, DIGEST,
            )
            grouped = postflight.validate_run(
                self.make_run(root, "grouped"),
                "grouped", 8, 12, DIGEST,
            )
            self.assertEqual(
                sequential["result"]["theorem_digest"],
                grouped["result"]["theorem_digest"],
            )
            self.assertEqual(grouped["result"]["group_sizes"], (4, 2, 2))

    def test_changed_result_bytes_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            run = self.make_run(Path(directory), "sequential")
            with (run / "candle.log").open("a", encoding="utf-8") as log:
                log.write("changed\n")
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                postflight.validate_run(run, "sequential", 8, 12, DIGEST)

    def test_unclosed_profile_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            run = self.make_run(Path(directory), "grouped")
            profile_path = run / "phase-profile.json"
            profile = json.loads(profile_path.read_text(encoding="utf-8"))
            profile["unclosed_phases"] = ["fixture/open"]
            profile_path.write_text(json.dumps(profile), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "unclosed phases"):
                postflight.validate_run(run, "grouped", 8, 12, DIGEST)

    def test_wrong_expected_digest_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            run = self.make_run(Path(directory), "sequential")
            with self.assertRaisesRegex(ValueError, "theorem digest mismatch"):
                postflight.validate_run(
                    run, "sequential", 8, 12, "f" * 32,
                )


if __name__ == "__main__":
    unittest.main()
