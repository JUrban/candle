import copy
import hashlib
import io
import json
import os
import tarfile
import tempfile
import unittest
from unittest import mock
from pathlib import Path

import flyspeck_prepare_inputs


class FlyspeckPreparedInputTests(unittest.TestCase):
    def fixture(self, root: Path) -> tuple[Path, Path, dict, bytes]:
        source_root = root / "source"
        source_root.mkdir()
        archive_path = source_root / "input.tar.gz"
        payload = b"authenticated certificate bytes\x00\xff"
        with tarfile.open(archive_path, "w:gz") as archive:
            member = tarfile.TarInfo("hard_7.dat")
            member.size = len(payload)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(payload))
        contract = {
            "schema": 1,
            "flyspeck_commit": "a" * 40,
            "archive": {
                "path": "input.tar.gz",
                "bytes": archive_path.stat().st_size,
                "sha256": hashlib.sha256(archive_path.read_bytes()).hexdigest(),
                "format": "tar.gz",
            },
            "members": [{
                "archive_name": "hard_7.dat",
                "output_path": "formal_lp/glpk/binary/hard_7.dat",
                "kind": "regular-file",
                "mode": 0o644,
                "bytes": len(payload),
                "sha256": hashlib.sha256(payload).hexdigest(),
            }],
            "policy": {
                "archive_member_set": "exact",
                "links": "forbidden",
                "absolute_or_parent_paths": "forbidden",
                "output_root": "new separate generated-input tree",
                "overwrite": "forbidden; atomic no-replace publication after validation",
                "runtime_shell_or_extraction": "forbidden",
            },
        }
        contract_path = root / "contract.json"
        contract_path.write_text(json.dumps(contract), encoding="utf-8")
        return source_root, contract_path, contract, payload

    def run_with_head(self, function, *arguments):
        original = flyspeck_prepare_inputs._git_head
        flyspeck_prepare_inputs._git_head = lambda _: "a" * 40
        try:
            return function(*arguments)
        finally:
            flyspeck_prepare_inputs._git_head = original

    def test_materializes_exact_authenticated_member(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, contract, payload = self.fixture(root)
            output = root / "output"
            receipt = self.run_with_head(
                flyspeck_prepare_inputs.materialize,
                contract_path, source, output,
            )
            path = output / contract["members"][0]["output_path"]
            self.assertEqual(path.read_bytes(), payload)
            self.assertEqual(path.stat().st_mode & 0o777, 0o644)
            self.assertEqual(receipt["outputs"][0]["sha256"], hashlib.sha256(payload).hexdigest())
            self.assertEqual(receipt["schema"], 2)
            self.assertEqual(
                receipt["publication"],
                flyspeck_prepare_inputs.PUBLICATION_RECORD,
            )

    def test_archive_digest_drift_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, _, _ = self.fixture(root)
            with (source / "input.tar.gz").open("ab") as archive:
                archive.write(b"drift")
            with self.assertRaisesRegex(ValueError, "archive digest"):
                self.run_with_head(
                    flyspeck_prepare_inputs.evaluate, contract_path, source,
                )

    def test_member_digest_drift_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, contract, _ = self.fixture(root)
            contract["members"][0]["sha256"] = "0" * 64
            contract_path.write_text(json.dumps(contract), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "certificate digest"):
                self.run_with_head(
                    flyspeck_prepare_inputs.evaluate, contract_path, source,
                )

    def test_extra_archive_member_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, contract, payload = self.fixture(root)
            archive_path = source / "input.tar.gz"
            with tarfile.open(archive_path, "w:gz") as archive:
                for name in ("hard_7.dat", "extra"):
                    member = tarfile.TarInfo(name)
                    member.size = len(payload)
                    member.mode = 0o644
                    archive.addfile(member, io.BytesIO(payload))
            contract["archive"]["bytes"] = archive_path.stat().st_size
            contract["archive"]["sha256"] = hashlib.sha256(archive_path.read_bytes()).hexdigest()
            contract_path.write_text(json.dumps(contract), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "member set"):
                self.run_with_head(
                    flyspeck_prepare_inputs.evaluate, contract_path, source,
                )

    def test_output_inside_source_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, _, _ = self.fixture(root)
            with self.assertRaisesRegex(ValueError, "separate from pinned source"):
                self.run_with_head(
                    flyspeck_prepare_inputs.materialize,
                    contract_path, source, source / "generated",
                )

    def test_output_symlink_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, _, _ = self.fixture(root)
            output = root / "output"
            output.symlink_to(source, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "output symlink"):
                self.run_with_head(
                    flyspeck_prepare_inputs.materialize,
                    contract_path, source, output,
                )

    def test_existing_output_root_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, _, _ = self.fixture(root)
            output = root / "output"
            output.mkdir()
            (output / "unexpected").write_text("must not survive")
            with self.assertRaisesRegex(ValueError, "already exists"):
                self.run_with_head(
                    flyspeck_prepare_inputs.materialize,
                    contract_path, source, output,
                )
            self.assertEqual(
                (output / "unexpected").read_text(), "must not survive"
            )

    def test_publication_race_preserves_colliding_destination(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, _, _ = self.fixture(root)
            output = root / "output"
            rename_noreplace = flyspeck_prepare_inputs._rename_noreplace

            def collide(source_path, destination_path):
                destination_path.mkdir()
                (destination_path / "unrelated").write_text("preserved")
                rename_noreplace(source_path, destination_path)

            with mock.patch.object(
                flyspeck_prepare_inputs, "_rename_noreplace",
                side_effect=collide,
            ), self.assertRaises(FileExistsError):
                self.run_with_head(
                    flyspeck_prepare_inputs.materialize,
                    contract_path, source, output,
                )
            self.assertEqual((output / "unrelated").read_text(), "preserved")
            staging = list(root.glob(".output.tmp.*"))
            self.assertEqual(len(staging), 1)
            self.assertFalse(
                (staging[0] / flyspeck_prepare_inputs.RECEIPT_NAME).exists()
            )
            self.assertTrue(
                (staging[0] / flyspeck_prepare_inputs.PENDING_RECEIPT_NAME).is_file()
            )

    def test_materialization_modes_ignore_permissive_umask(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, contract, _ = self.fixture(root)
            output = root / "output"
            original_umask = os.umask(0)
            try:
                self.run_with_head(
                    flyspeck_prepare_inputs.materialize,
                    contract_path, source, output,
                )
            finally:
                os.umask(original_umask)
            generated = output / contract["members"][0]["output_path"]
            self.assertEqual(output.stat().st_mode & 0o777, 0o555)
            self.assertEqual(generated.stat().st_mode & 0o777, 0o644)
            self.assertEqual(
                (output / flyspeck_prepare_inputs.RECEIPT_NAME).stat().st_mode
                & 0o777,
                0o444,
            )
            for parent in generated.parents:
                if parent == output:
                    break
                self.assertEqual(parent.stat().st_mode & 0o777, 0o555)

    def test_receipt_hashes_the_contract_bytes_that_were_parsed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, contract_path, _, _ = self.fixture(root)
            contract_bytes = contract_path.read_bytes()
            original_validate = flyspeck_prepare_inputs._validate_source

            def validate_then_swap(contract, source_root):
                result = original_validate(contract, source_root)
                contract_path.write_text("{}", encoding="utf-8")
                return result

            with mock.patch.object(
                flyspeck_prepare_inputs, "_validate_source",
                side_effect=validate_then_swap,
            ):
                receipt = self.run_with_head(
                    flyspeck_prepare_inputs.materialize,
                    contract_path, source, root / "output",
                )
            self.assertEqual(
                receipt["contract_sha256"],
                hashlib.sha256(contract_bytes).hexdigest(),
            )


if __name__ == "__main__":
    unittest.main()
