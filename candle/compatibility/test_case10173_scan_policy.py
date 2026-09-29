#!/usr/bin/env python3

import tempfile
import unittest
from pathlib import Path

import case10173_parent_scan as parent_scan
import case10173_scan_policy as subject


def root(index: int, flags: tuple[bool, ...]) -> parent_scan.RootVerdict:
    return parent_scan.RootVerdict(label="test", index=index, flags=flags)


class Case10173ScanPolicyTest(unittest.TestCase):
    def fixtures(self):
        parents = [
            root(0, (True,)),
            root(1, (False,)),
            root(2, (False,)),
        ]
        axis4 = (False, False, False, False, False, False,
                 True, True, False, False, False, False)
        children = [
            root(1, (False,) + axis4),
            root(2, (False,) + (False,) * 12),
        ]
        depth2 = [
            subject.Depth2Verdict(
                label="depth2", index=2, first_axis=4, branch=0,
                flags=(True, True) + (False,) * 10,
            ),
            subject.Depth2Verdict(
                label="depth2", index=2, first_axis=4, branch=1,
                flags=(False, False, True, True) + (False,) * 8,
            ),
        ]
        return parents, children, depth2

    def test_staged_plan_and_rendering(self) -> None:
        parents, children, depth2 = self.fixtures()
        initial = subject.build_plans(parents, children)
        self.assertEqual(subject.unresolved_work(initial), [(2, 4, 0), (2, 4, 1)])
        self.assertEqual(subject.required_depth2_work(children),
                         [(2, 4, 0), (2, 4, 1)])
        plans = subject.build_plans(parents, children, depth2)
        self.assertEqual([plan.depth for plan in plans], [0, 1, 2])
        self.assertEqual([plan.final_cells for plan in plans], [1, 2, 4])
        rendered = subject.render_policy_ml(plans, "candle_test_case10173")
        self.assertIn("(0,Candle_action296_forest_leaf)", rendered)
        self.assertIn("Candle_action296_forest_split (4,", rendered)
        self.assertIn("let candle_test_case10173_final_cells = 7;;", rendered)
        self.assertIn("let candle_test_case10173_expected_digest = None;;", rendered)
        schedule = subject.render_singleton_schedule_ml(plans)
        self.assertIn(
            "let candle_action296_generated_group_sizes = [1;1;1];;",
            schedule,
        )

    def test_large_outputs_use_bounded_source_lists(self) -> None:
        plans = [
            subject.RootPlan(
                index=index,
                depth=0,
                final_cells=1,
                first_axis=None,
                depth1_flags=None,
                depth2_axes=(),
            )
            for index in range(subject.ML_LIST_CHUNK_SIZE + 1)
        ]
        policy = subject.render_policy_ml(plans, "candle_test_large")
        schedule = subject.render_singleton_schedule_ml(plans)
        self.assertIn("let candle_test_large_roots_chunk_000 =", policy)
        self.assertIn("let candle_test_large_roots =\n  List.flatten", policy)
        self.assertIn("group_sizes = map (fun _ -> 1)", schedule)
        self.assertEqual(policy.count("Candle_action296_forest_leaf"), 129)

    def test_depth2_log_validation(self) -> None:
        record = (
            f"{subject.BRANCH_MARKER} label=d index=2 first_axis=4 "
            "branch=0 flags=1,1,0,0,0,0,0,0,0,0,0,0\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "candle.log"
            path.write_text(
                record
                + f"{subject.RESULT_MARKER} label=d branches=1 verdicts=12 "
                  "theorem_authority=none\n"
                + subject.OK_MARKER + "\n",
                encoding="utf-8",
            )
            parsed = subject.read_depth2_logs([path])
            subject.validate_depth2_work(parsed, [(2, 4, 0)])
            with self.assertRaisesRegex(ValueError, "depth-two scan mismatch"):
                subject.validate_depth2_work(parsed, [(2, 4, 1)])
            path.write_text("incomplete\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "incomplete"):
                subject.read_depth2_logs([path])

    def test_child_contract_and_chunks(self) -> None:
        parents, children, _ = self.fixtures()
        subject.validate_child_scans(parents, children)
        self.assertEqual(
            subject.work_chunks([(1, 4, 0), (2, 4, 0), (2, 4, 1)], 2),
            [[(1, 4, 0)], [(2, 4, 0), (2, 4, 1)]],
        )
        rendered = subject.render_depth2_ml([(2, 4, 0)], "test-depth2")
        self.assertIn("[(2,4,0)]", rendered)
        bad_children = [root(1, (True,) + (False,) * 12), children[1]]
        with self.assertRaisesRegex(ValueError, "unexpectedly accepted"):
            subject.validate_child_scans(parents, bad_children)

    def test_axis4_closures_merge_with_full_fallback(self) -> None:
        parents = [root(0, (True,)), root(1, (False,)), root(2, (False,))]
        axis4 = [
            root(1, (False, True, True)),
            root(2, (False, True, False)),
        ]
        full = [root(2, (False,) + (False,) * 6 + (True, True)
                     + (False,) * 4)]
        merged = subject.merge_axis4_child_scans(parents, axis4, full)
        self.assertEqual([item.index for item in merged], [1, 2])
        self.assertEqual(len(merged[0].flags), 13)
        self.assertEqual(merged[0].flags[7:9], (True, True))
        self.assertEqual(subject._viable_axes(merged[0].flags[1:]), [4])


if __name__ == "__main__":
    unittest.main()
