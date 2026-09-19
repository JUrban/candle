#!/usr/bin/env python3

import json
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path("/project/worktrees/flyspeck-v13-source")
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_verifier_closure as subject


class NonlinearVerifierClosureTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = subject.build_closure(ROOT, FLYSPECK_ROOT)
        cls.published = json.loads(
            (ROOT / subject.OUTPUT).read_text(encoding="utf-8")
        )

    def test_published_closure_is_current(self) -> None:
        self.assertEqual(self.published, self.payload)

    def test_exact_bounded_closure(self) -> None:
        counts = self.payload["counts"]
        self.assertEqual(self.payload["root"], subject.VERIFIER_ROOT.key)
        self.assertEqual(counts["selected_source_nodes"], 90)
        self.assertEqual(counts["selected_by_repository"], {
            "candle": 28,
            "flyspeck": 62,
        })
        self.assertEqual(counts["already_in_direct_manifest"], 34)
        self.assertEqual(counts["identity_extension"], 56)
        self.assertEqual(counts["identity_extension_by_repository"], {
            "candle": 0,
            "flyspeck": 56,
        })

    def test_every_source_action_is_exactly_resolved(self) -> None:
        selected = set(self.payload["source_nodes"])
        for key, node in self.payload["source_nodes"].items():
            self.assertIn(node["repository"], {"candle", "flyspeck"})
            self.assertEqual(len(node["md5"]), 32)
            self.assertEqual(len(node["sha256"]), 64)
            for dependency in node["dependencies"]:
                if dependency["status"] == "runtime-library":
                    self.assertEqual(dependency["kind"], "#load")
                else:
                    self.assertEqual(dependency["status"], "resolved")
                    self.assertIn(dependency["selected"], selected, key)

    def test_extension_has_logical_identity_and_two_hashes(self) -> None:
        direct = set(self.payload["direct_manifest_overlap"])
        extension = self.payload["identity_extension"]
        self.assertEqual(len(extension), 56)
        self.assertTrue(all(item["source_key"] not in direct for item in extension))
        self.assertTrue(all(
            item["source_key"] ==
            f'{item["repository"]}:{item["logical_relative_path"]}'
            for item in extension
        ))

    def test_runtime_compatibility_members_are_accounted_for(self) -> None:
        compatibility = self.payload["compatibility"]
        self.assertEqual(compatibility["unsupported_use_count"], 0)
        self.assertEqual(compatibility["unsupported_uses"], [])
        members = {
            (use["module"], use["member"])
            for use in compatibility["qualified_uses"]
        }
        self.assertTrue({
            ("Array", "to_list"),
            ("Big_int", "eq_big_int"),
            ("Big_int", "mult_big_int"),
            ("Big_int", "sqrt_big_int"),
            ("Format", "std_formatter"),
            ("Stdlib", "abs_float"),
            ("Stdlib", "ignore"),
        } <= members)
        self.assertIn("abs_float", compatibility["toplevel_members"])
        self.assertTrue(any(
            use["source"] == "flyspeck:formal_ineqs/trig/exp_eval.hl" and
            use["identifier"] == "abs_float" and use["line"] == 345
            for use in compatibility["toplevel_uses"]
        ))


if __name__ == "__main__":
    unittest.main()
