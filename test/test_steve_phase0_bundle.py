#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "steve_phase0_bundle.py"
SPEC = importlib.util.spec_from_file_location("steve_phase0_bundle", SCRIPT)
assert SPEC and SPEC.loader
bundle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bundle)


class StevePhase0BundleTests(unittest.TestCase):
    def write_spec(self, root: Path, objects: list[dict[str, str]]) -> Path:
        spec = root / "spec.json"
        spec.write_text(
            json.dumps({"source_revision": "deadbeef", "objects": objects}),
            encoding="utf-8",
        )
        return spec

    def test_root_is_deterministic_across_spec_order(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "a.bin").write_bytes(b"alpha")
            (root / "b.bin").write_bytes(b"beta")
            store = root / "store"

            first = self.write_spec(
                root,
                [
                    {"name": "b", "kind": "proof-certificate", "path": "b.bin"},
                    {"name": "a", "kind": "llvm-artifact", "path": "a.bin"},
                ],
            )
            digest1 = bundle.build_bundle(first, store, None)

            second = root / "spec2.json"
            second.write_text(
                json.dumps(
                    {
                        "source_revision": "deadbeef",
                        "objects": [
                            {"name": "a", "kind": "llvm-artifact", "path": "a.bin"},
                            {"name": "b", "kind": "proof-certificate", "path": "b.bin"},
                        ],
                    }
                ),
                encoding="utf-8",
            )
            digest2 = bundle.build_bundle(second, store, None)

            self.assertEqual(digest1, digest2)
            manifest = bundle.verify_bundle(store, digest1)
            self.assertEqual([x["name"] for x in manifest["objects"]], ["a", "b"])

    def test_content_change_changes_root(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            object_path = root / "artifact.bin"
            object_path.write_bytes(b"one")
            store = root / "store"
            spec = self.write_spec(
                root,
                [{"name": "artifact", "kind": "assurance", "path": "artifact.bin"}],
            )
            digest1 = bundle.build_bundle(spec, store, None)
            object_path.write_bytes(b"two")
            digest2 = bundle.build_bundle(spec, store, None)
            self.assertNotEqual(digest1, digest2)
            bundle.verify_bundle(store, digest1)
            bundle.verify_bundle(store, digest2)

    def test_tampered_object_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "artifact.bin").write_bytes(b"authoritative")
            store = root / "store"
            spec = self.write_spec(
                root,
                [{"name": "artifact", "kind": "assurance", "path": "artifact.bin"}],
            )
            digest = bundle.build_bundle(spec, store, None)
            manifest = bundle.verify_bundle(store, digest)
            object_digest = manifest["objects"][0]["sha256"]
            bundle.object_path(store, object_digest).write_bytes(b"tampered")
            with self.assertRaises(bundle.BundleError):
                bundle.verify_bundle(store, digest)

    def test_duplicate_logical_name_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "a").write_bytes(b"a")
            (root / "b").write_bytes(b"b")
            spec = self.write_spec(
                root,
                [
                    {"name": "same", "kind": "a", "path": "a"},
                    {"name": "same", "kind": "b", "path": "b"},
                ],
            )
            with self.assertRaises(bundle.BundleError):
                bundle.build_bundle(spec, root / "store", None)


if __name__ == "__main__":
    unittest.main()
