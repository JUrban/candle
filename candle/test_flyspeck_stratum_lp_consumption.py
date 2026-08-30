#!/usr/bin/env python3

import copy
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flyspeck_stratum_runtime as subject


class LpConsumptionTests(unittest.TestCase):
    nonce = "a" * 32
    boundary = "05-lp_support-through-184"
    action_count = 185

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.runtime = []
        for index in range(39):
            basename = f"cert-{index:02d}.dat"
            path = root / basename
            contents = f"certificate-{index}\n".encode()
            path.write_bytes(contents)
            self.runtime.append({
                "class": (
                    "lp-certificate-prepared" if index == 20 else
                    "lp-certificate"
                ),
                "relative": f"formal_lp/glpk/binary/{basename}",
                "path": str(path),
                "bytes": len(contents),
                "sha256": hashlib.sha256(contents).hexdigest(),
                "md5": hashlib.md5(
                    contents, usedforsecurity=False,
                ).hexdigest(),
            })
        self.contract = subject.build_lp_consumption_contract(
            self.nonce, self.runtime,
        )

    def valid_lines(self) -> list[str]:
        bindings = list(reversed(self.contract["bindings"]))
        lines = [
            "\t".join((
                subject.LP_CONSUMPTION_PREFIX, self.nonce, "CONSUMED",
                str(index), binding["binding_id"],
            ))
            for index, binding in enumerate(bindings)
        ]
        lines.append("\t".join((
            subject.LP_CONSUMPTION_PREFIX, self.nonce, "TERMINAL", "39", "39",
        )))
        return lines

    def log_text(self, records: list[str]) -> str:
        split = next((
            index for index, line in enumerate(records)
            if "\tCONSUMED\t" not in line
        ), len(records))
        return "\n".join([
            f"{subject.PREFLIGHT_MARKER} {self.nonce}",
            *records[:split],
            (f"{subject.SUCCESS_MARKER} {self.nonce} {self.boundary} "
             f"{self.action_count}"),
            *records[split:],
            (f"{subject.SOURCE_TRACE_PREFIX}\t{self.nonce}\t"
             "TERMINAL\t0"),
        ]) + "\n"

    def validate_lines(self, records: list[str]) -> dict:
        return subject.validate_lp_consumption_log(
            self.log_text(records), self.contract, self.boundary,
            self.action_count,
        )

    def test_contract_and_reverse_runtime_events_close_exactly(self) -> None:
        observation = self.validate_lines(self.valid_lines())
        self.assertEqual(observation["event_count"], 39)
        self.assertEqual(observation["record_count"], 39)
        self.assertTrue(all(
            record["event_count"] == 1 for record in observation["records"]
        ))
        self.assertEqual(
            [record["relative"] for record in observation["records"]],
            [binding["relative"] for binding in self.contract["bindings"]],
        )
        self.assertFalse(observation["pft_used"])
        self.assertFalse(observation["s2_s3_evidence"])

    def test_missing_duplicate_unknown_and_post_terminal_events_reject(self) -> None:
        cases = []
        missing = self.valid_lines()
        missing.pop(0)
        missing[-1] = missing[-1].replace("\t39\t39", "\t38\t39")
        cases.append(("missing", missing))
        duplicate_id = self.valid_lines()
        fields = duplicate_id[1].split("\t")
        fields[3] = "0"
        duplicate_id[1] = "\t".join(fields)
        cases.append(("duplicate", duplicate_id))
        duplicate_binding = self.valid_lines()
        fields = duplicate_binding[1].split("\t")
        fields[4] = duplicate_binding[0].split("\t")[4]
        duplicate_binding[1] = "\t".join(fields)
        cases.append(("duplicate binding", duplicate_binding))
        unknown = self.valid_lines()
        fields = unknown[0].split("\t")
        fields[4] = "f" * 64
        unknown[0] = "\t".join(fields)
        cases.append(("unknown", unknown))
        post_terminal = self.valid_lines()
        post_terminal.append(post_terminal[0])
        cases.append(("post-terminal", post_terminal))
        for label, lines in cases:
            with self.subTest(label=label), self.assertRaises(subject.ContractError):
                self.validate_lines(lines)

    def test_terminal_nonce_failure_and_namespace_mutations_reject(self) -> None:
        cases = []
        no_terminal = self.valid_lines()[:-1]
        cases.append(("no terminal", no_terminal))
        wrong_nonce = self.valid_lines()
        wrong_nonce[0] = wrong_nonce[0].replace(self.nonce, "b" * 32)
        cases.append(("nonce", wrong_nonce))
        failure = self.valid_lines()[:-1] + ["\t".join((
            subject.LP_CONSUMPTION_PREFIX, self.nonce, "FAILURE", "read",
        ))]
        cases.append(("failure", failure))
        malformed_namespace = self.valid_lines()
        malformed_namespace[0] = malformed_namespace[0].replace(
            subject.LP_CONSUMPTION_PREFIX + "\t",
            subject.LP_CONSUMPTION_PREFIX + " ",
        )
        cases.append(("namespace", malformed_namespace))
        for label, lines in cases:
            with self.subTest(label=label), self.assertRaises(subject.ContractError):
                self.validate_lines(lines)

    def test_consumption_records_are_bound_to_exact_runtime_interval(self) -> None:
        records = self.valid_lines()
        preflight = f"{subject.PREFLIGHT_MARKER} {self.nonce}"
        boundary = (
            f"{subject.SUCCESS_MARKER} {self.nonce} {self.boundary} "
            f"{self.action_count}"
        )
        source_terminal = (
            f"{subject.SOURCE_TRACE_PREFIX}\t{self.nonce}\tTERMINAL\t0"
        )
        relocated = (
            [*records[:-1], preflight, boundary, records[-1], source_terminal],
            [preflight, boundary, *records, source_terminal],
            [preflight, *records, boundary, source_terminal],
            [preflight, *records[:-1], boundary, source_terminal, records[-1]],
        )
        for index, lines in enumerate(relocated):
            with self.subTest(index=index), self.assertRaisesRegex(
                subject.ContractError, "exact runtime interval",
            ):
                subject.validate_lp_consumption_log(
                    "\n".join(lines), self.contract, self.boundary,
                    self.action_count,
                )

    def test_contract_rejects_order_class_path_digest_and_types(self) -> None:
        cases = []
        reordered = copy.deepcopy(self.contract)
        reordered["bindings"][0], reordered["bindings"][1] = (
            reordered["bindings"][1], reordered["bindings"][0]
        )
        reordered["ordered_binding_sha256"] = subject.canonical_sha256(
            reordered["bindings"]
        )
        cases.append(("order", reordered))
        wrong_class = copy.deepcopy(self.contract)
        wrong_class["bindings"][0]["class"] = "lp-certificate-prepared"
        cases.append(("class", wrong_class))
        for namespace in ("pft", "pft-results", "pft_trace"):
            pft = copy.deepcopy(self.contract)
            pft["bindings"][0]["relative"] = (
                f"formal_lp/{namespace}/cert-00.dat"
            )
            cases.append((f"relative {namespace}", pft))
            absolute_pft = copy.deepcopy(self.contract)
            absolute_pft["bindings"][0]["path"] = (
                f"/authenticated/{namespace}/cert-00.dat"
            )
            absolute_pft["ordered_binding_sha256"] = subject.canonical_sha256(
                absolute_pft["bindings"]
            )
            cases.append((f"absolute {namespace}", absolute_pft))
        duplicate_basename = copy.deepcopy(self.contract)
        duplicate_basename["bindings"][1]["relative"] = (
            "another/cert-00.dat"
        )
        duplicate_basename["bindings"][1]["path"] = (
            str(Path(self.temporary.name) / "another" / "cert-00.dat")
        )
        duplicate_basename["bindings"][1]["binding_id"] = (
            subject.canonical_sha256({
                field: duplicate_basename["bindings"][1][field]
                for field in (
                    "index", "class", "relative", "bytes", "sha256", "md5",
                )
            })
        )
        duplicate_basename["ordered_binding_sha256"] = subject.canonical_sha256(
            duplicate_basename["bindings"]
        )
        cases.append(("duplicate basename", duplicate_basename))
        forged = copy.deepcopy(self.contract)
        forged["bindings"][0]["binding_id"] = "f" * 64
        forged["ordered_binding_sha256"] = subject.canonical_sha256(
            forged["bindings"]
        )
        cases.append(("digest", forged))
        boolean = copy.deepcopy(self.contract)
        boolean["record_count"] = True
        cases.append(("bool", boolean))
        for label, contract in cases:
            with self.subTest(label=label), self.assertRaises(subject.ContractError):
                subject.validate_lp_consumption_contract(contract)

        for namespace in ("pft-results", "pft_trace"):
            runtime = copy.deepcopy(self.runtime)
            runtime[0]["relative"] = (
                f"formal_lp/{namespace}/cert-00.dat"
            )
            with self.subTest(builder=namespace), self.assertRaisesRegex(
                subject.ContractError, "PFT namespace",
            ):
                subject.build_lp_consumption_contract(self.nonce, runtime)

    def test_observation_is_exact_unapproved_and_cannot_be_relabelled(self) -> None:
        observation = self.validate_lines(self.valid_lines())
        subject.validate_lp_consumption_observation(self.contract, observation)
        for field, value in (
            ("approved_reference_present", True),
            ("pft_used", True),
            ("s2_s3_evidence", True),
            ("unmatched_event_count", 1),
            ("record_count", 39.0),
        ):
            forged = copy.deepcopy(observation)
            forged[field] = value
            with self.subTest(field=field), self.assertRaises(subject.ContractError):
                subject.validate_lp_consumption_observation(
                    self.contract, forged,
                )

    def test_runtime_config_and_postlude_enable_only_explicit_contract(self) -> None:
        prepared = {
            "source_trace_contract": {
                "nonce": self.nonce, "bindings": [], "binding_count": 0,
            },
            "attempt_nonce": self.nonce,
            "flyspeck_root": "/snapshot/flyspeck",
            "overlay_root": "/snapshot/overlay",
            "generated_root": "/snapshot/generated",
            "boundary": {"boundary_id": "05-lp"},
            "actions": [],
            "normalized_runtime": [],
            "source_alias_runtime": [],
            "generated_runtime": [],
            "lp_certificate_runtime": self.runtime,
            "process_runtime": [],
        }
        config = Path(self.temporary.name) / "config.ml"
        with mock.patch.object(
            subject, "validate_source_trace_contract", side_effect=lambda value: value,
        ):
            subject.write_config(
                config, Path("/snapshot/candle"), prepared,
                Path("/snapshot/program.ml"), "0" * 32,
            )
            disabled = config.read_text(encoding="utf-8")
            self.assertIn("candle_flyspeck_lp_consumption_enabled = false", disabled)
            self.assertNotIn(self.contract["bindings"][0]["binding_id"], disabled)
            prepared["lp_consumption_contract"] = self.contract
            subject.write_config(
                config, Path("/snapshot/candle"), prepared,
                Path("/snapshot/program.ml"), "0" * 32,
            )
        enabled = config.read_text(encoding="utf-8")
        self.assertIn("candle_flyspeck_lp_consumption_enabled = true", enabled)
        for binding in self.contract["bindings"]:
            self.assertIn(binding["binding_id"], enabled)
            self.assertIn(binding["path"], enabled)

        postlude = Path(self.temporary.name) / "postlude.ml"
        arguments = (
            postlude, Path("/snapshot/candle"), "05-lp", [], self.nonce,
            {"records": [], "record_count": 0, "ordered_record_sha256": "0" * 64},
        )
        subject.write_postlude(*arguments)
        self.assertNotIn(
            "finish_lp_certificate_consumption",
            postlude.read_text(encoding="utf-8"),
        )
        subject.write_postlude(*arguments, lp_consumption_enabled=True)
        rendered = postlude.read_text(encoding="utf-8")
        self.assertLess(
            rendered.index("finish_lp_certificate_consumption"),
            rendered.index("requestSourceTraceFinish"),
        )


if __name__ == "__main__":
    unittest.main()
