"""Protect graph repeatability and the distinction between execution and proof evidence."""

import json
import os
import re
import subprocess
import tempfile
import tomllib
import unittest
from pathlib import Path
from unittest.mock import patch

import build
import collect
import common
import graph
import render
import taxonomy
from common import HERE, ROOT, write_json


class GraphTests(unittest.TestCase):
    def test_import_order_does_not_move_nodes_and_new_modules_are_included(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            files = []
            for name in ("a", "b"):
                crate = root / "crates" / name
                (crate / "src").mkdir(parents=True)
                (crate / "Cargo.toml").write_text(f'[package]\nname="{name}"\n')
                (crate / "src/lib.rs").write_text(
                    "use b::Value;\n" if name == "a" else "pub struct Value;\n"
                )
                files.append(
                    {
                        "id": f"crates/{name}/src/lib.rs",
                        "codeLines": 1,
                        "source": "fixture",
                    }
                )
            with patch.object(graph, "ROOT", root):
                first = graph.build({"files": files, "claims": []})
                reordered = graph.build({"files": list(reversed(files)), "claims": []})
                self.assertEqual(first, reordered)
                (root / "crates/a/src/new.rs").write_text("use b::Value;\n")
                files.append(
                    {"id": "crates/a/src/new.rs", "codeLines": 1, "source": "fixture"}
                )
                changed = graph.build({"files": files, "claims": []})
                self.assertIn(
                    "crates/a/src/new.rs", changed["views"]["modules"]["positions"]
                )
                self.assertTrue(
                    any(e["source"].endswith("/new.rs") for e in changed["imports"])
                )
                other_seed = graph.build({"files": files, "claims": []}, seed=10)
                self.assertNotEqual(
                    changed["views"]["modules"]["positions"],
                    other_seed["views"]["modules"]["positions"],
                )

    def test_new_crate_tests_use_the_cargo_package_name(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            crate = root / "crates/folder"
            (crate / "src").mkdir(parents=True)
            (crate / "Cargo.toml").write_text('[package]\nname="different-package"\n')
            (crate / "src/lib.rs").write_text("#[test]\nfn checks_a_value() {}\n")
            with patch.object(taxonomy, "ROOT", root):
                functions, _ = taxonomy.index_functions()
                test = taxonomy.find_function(
                    "different-package::checks_a_value", functions
                )
                self.assertEqual(test["path"], "crates/folder/src/lib.rs")

    def test_a_test_with_a_version_for_each_platform_is_found(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            crate = root / "crates/folder"
            (crate / "src").mkdir(parents=True)
            (crate / "Cargo.toml").write_text('[package]\nname="a-package"\n')
            # A neighbour's cfg, on an item with no braces, mustn't count as the test's.
            (crate / "src/lib.rs").write_text(
                "#[cfg(test)]\nmod tests {\n"
                "    #[cfg(windows)]\n    use std::os::windows as _;\n"
                "    #[cfg(unix)]\n    #[test]\n    fn quotes() {}\n"
                "    #[cfg(windows)]\n    #[test]\n    fn quotes() {}\n}\n"
            )
            with patch.object(taxonomy, "ROOT", root):
                functions, _ = taxonomy.index_functions()
                test = taxonomy.find_function("a-package::tests::quotes", functions)
            here = "#[cfg(windows)]" if os.name == "nt" else "#[cfg(unix)]"
            other = "#[cfg(unix)]" if os.name == "nt" else "#[cfg(windows)]"
            self.assertIn(here, test["attributes"])
            self.assertNotIn(other, test["attributes"])

    def test_new_roles_are_explicitly_unclassified(self):
        network = {
            "nodes": {
                "new": {"crate": "new-crate", "name": "something", "kind": "module"}
            }
        }
        self.assertEqual(
            build.assign_roles(network, {"nodeRoles": {}}), {"new": "other"}
        )


class EvidenceTests(unittest.TestCase):
    def test_catalog_references_current_sources_and_symbols(self):
        build.load_catalog()

    def test_catalog_covers_every_oracle_operation(self):
        catalog = build.load_catalog()
        handler = (ROOT / "formal/Musubi/ExecJson.lean").read_text().split(
            "def handle (", 1
        )[1]
        operations = set(re.findall(r'\| \.ok "([A-Za-z]+)" =>', handler))
        self.assertTrue(operations)
        self.assertEqual(operations, set(catalog["oracleModels"]))
        for models in catalog["oracleModels"].values():
            self.assertTrue(models)
            for model in models:
                self.assertTrue((ROOT / f"formal/Musubi/{model}.lean").is_file())

    def test_out_of_line_test_changes_invalidate_capture_harness(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            test = root / "crates/a/src/nested/io_tests.rs"
            test.parent.mkdir(parents=True)
            test.write_text("#[test] fn checks_reply() {}")
            with patch.object(common, "ROOT", root):
                before = common.harness_hashes("tests")
                test.write_text("#[test] fn checks_reply() { panic!(); }")
                self.assertNotEqual(before, common.harness_hashes("tests"))

    def test_capture_preserves_selection_and_extends_instrumented_timeouts(self):
        config = (ROOT / ".config/nextest.toml").read_text()
        before = tomllib.loads(config)
        after = tomllib.loads(collect.test_config(config, "default"))
        for name, original in before["profile"].items():
            updated = after["profile"][name]
            self.assertEqual(original.get("default-filter"), updated.get("default-filter"))
            for old, new in zip(
                [original] + original.get("overrides", []),
                [updated] + updated.get("overrides", []),
            ):
                if "slow-timeout" in old:
                    self.assertEqual(
                        new["slow-timeout"]["period"],
                        str(int(old["slow-timeout"]["period"][:-1]) * 4) + "s",
                    )
                    self.assertEqual(
                        old["slow-timeout"]["terminate-after"],
                        new["slow-timeout"]["terminate-after"],
                    )
        self.assertEqual(
            after["profile"]["default"]["scripts"][-1]["run-wrapper"], "assurance-record"
        )

    def test_build_inputs_are_part_of_the_capture_fingerprint(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            inputs = [
                "Cargo.toml",
                "Cargo.lock",
                "formal/lean-toolchain",
                "crates/a/build.rs",
                "crates/a/src/defaults.toml",
                "formal/lakefile.toml",
                "formal/lake-manifest.json",
            ]
            for name in inputs:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("original")
            with (
                patch.object(common, "ROOT", root),
                patch.object(common, "production_files", return_value=[]),
                patch.object(
                    common.subprocess, "check_output", return_value="revision"
                ),
            ):
                previous = common.source_identity()["sourceDigest"]
                for name in inputs[3:]:
                    (root / name).write_text("changed")
                    changed = common.source_identity()["sourceDigest"]
                    self.assertNotEqual(previous, changed, name)
                    previous = changed

    def test_resuming_export_refuses_a_different_compiler(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            write_json(
                root / "manifest.json", {"executionExitCode": 0, "rustc": "recorded"}
            )
            with (
                patch.object(collect, "llvm_tools", return_value=(root, "different")),
                self.assertRaisesRegex(ValueError, "exact rustc/LLVM"),
            ):
                collect.export_tests(root)

    def test_conformance_requires_observed_oracle_use_not_a_name(self):
        fn = {
            "path": "crates/a/src/lib.rs",
            "name": "looks_like_conformance",
            "body": "{}",
            "hegel": False,
        }
        self.assertNotIn(
            "conformance", taxonomy.classify("a::looks_like_conformance", fn, {}, [])
        )
        self.assertIn(
            "conformance", taxonomy.classify("a::unusual_name", fn, {}, ["names"])
        )

    def test_changed_source_cannot_reuse_old_coverage(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            write_json(
                root / "manifest.json",
                {"kind": "tests", "sourceDigest": "old", "ended": 1},
            )
            with (
                patch.object(
                    build, "source_identity", return_value={"sourceDigest": "new"}
                ),
                patch.object(build, "load_catalog", return_value={"claims": []}),
                patch.object(build, "inventory", return_value={}),
                patch.object(build.graph, "build", return_value={}),
                patch.object(build.taxonomy, "index_functions", return_value=({}, {})),
                self.assertRaisesRegex(ValueError, "source fingerprint differs"),
            ):
                build.build([root], root / "data.json")

    def test_unbuildable_changes_do_not_count_as_tests_noticing_a_bug(self):
        outcomes = []
        for status in ("CaughtMutant", "MissedMutant", "Unviable", "Timeout"):
            outcomes.append(
                {
                    "scenario": {
                        "Mutant": {
                            "file": "a.rs",
                            "name": status,
                            "span": {"start": {"line": 1}},
                        }
                    },
                    "summary": status,
                }
            )
        result = build.mutation_results({"outcomes": outcomes})["files"]["a.rs"]
        self.assertEqual(
            result, {"noticed": 1, "missed": 1, "unviable": 1, "timeout": 1}
        )

    def test_nextest_timeout_alone_is_not_a_detected_code_change(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            outcomes = []
            for i, summary in enumerate(
                ("18 passed, 1 timed out", "17 passed, 1 failed, 1 timed out")
            ):
                log = f"{i}.log"
                (root / log).write_text(f"Summary [ 120.00s] 19 tests run: {summary}\n")
                outcomes.append(
                    {
                        "scenario": {
                            "Mutant": {
                                "file": "a.rs",
                                "name": str(i),
                                "span": {"start": {"line": 1}},
                            }
                        },
                        "summary": "CaughtMutant",
                        "log_path": log,
                    }
                )
            result = build.mutation_results({"outcomes": outcomes}, root)["files"][
                "a.rs"
            ]
            self.assertEqual(result, {"noticed": 1, "timeout": 1})

    @unittest.skipUnless(os.name == "posix", "Oracle capture uses Unix executables")
    def test_oracle_relay_preserves_replies_and_records_actual_requests(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            child = root / "oracle"
            child.write_text(
                '#!/usr/bin/env python3\nimport sys\nfor line in sys.stdin: print(line,end="",flush=True)\n'
            )
            child.chmod(0o755)
            request = '{"op":"names","machines":[]}\n'
            env = dict(
                os.environ,
                ASSURANCE_TEST_DIR=str(root),
                ASSURANCE_REAL_ORACLE=str(child),
            )
            p = subprocess.run(
                ["python3", str(HERE / "oracle.py")],
                input=request,
                text=True,
                capture_output=True,
                env=env,
                check=True,
            )
            self.assertEqual(p.stdout, request)
            self.assertTrue((root / "oracle-ops/names").is_file())

    def test_rendering_the_same_saved_dataset_is_identical(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            data = {
                "roles": [],
                "nodeRoles": {},
                "mechanisms": [
                    {
                        "id": "unit",
                        "name": "Old display name",
                        "description": "Old description",
                        "tests": 3,
                    },
                    {
                        "id": "historical-only",
                        "name": "Historical category",
                        "description": "Historical description",
                        "tests": 4,
                    },
                ],
                "sourceCommit": "canonical-source-commit",
                "claims": [],
                "evidence": [],
                "network": {
                    "nodes": {},
                    "imports": [],
                    "views": {},
                    "measurement": "",
                    "assurance": "",
                },
                "measured": {
                    "sourceRevision": "abc",
                    "sourceDigest": "digest",
                    "duration": 1,
                    "effort": 1,
                    "captureId": "capture",
                    "fuzzCheckpoints": 0,
                    "fuzzInputs": 0,
                    "coverageGroups": [],
                    "passed": 0,
                    "failed": 0,
                    "events": [],
                    "files": {},
                    "mutation": {"files": {}, "sites": []},
                },
            }
            write_json(root / "data.json", data)
            render.render(root / "data.json", root / "one.html")
            render.render(root / "data.json", root / "two.html")
            self.assertEqual(
                (root / "one.html").read_bytes(), (root / "two.html").read_bytes()
            )
            inline = json.loads(
                re.search(
                    r'<script type="application/json" id="ng-data">\s*(.*?)\s*</script>',
                    (root / "one.html").read_text(),
                    re.DOTALL,
                )[1]
            )
            current = next(
                item
                for item in json.loads((HERE / "catalog.json").read_text())["mechanisms"]
                if item["id"] == "unit"
            )
            self.assertEqual(inline["mechanisms"][0]["name"], current["name"])
            self.assertEqual(
                inline["mechanisms"][0]["description"], current["description"]
            )
            self.assertEqual(inline["mechanisms"][0]["tests"], 3)
            self.assertEqual(inline["mechanisms"][1], data["mechanisms"][1])
            self.assertEqual(
                inline["measured"]["sourceRevision"], "canonical-source-commit"
            )
            self.assertEqual(json.loads((root / "data.json").read_text()), data)

    def test_checked_in_snapshots_render_without_collecting_current_sources(self):
        with tempfile.TemporaryDirectory() as work:
            snapshots = sorted((HERE / "data").glob("*/snapshot.json"))
            self.assertTrue(snapshots)
            with patch.object(
                common, "source_identity", side_effect=AssertionError("Fresh collection")
            ):
                for i, snapshot in enumerate(snapshots):
                    output = Path(work) / f"{i}.html"
                    render.render(snapshot, output, standalone=True)
                    self.assertIn("Replay clock", output.read_text())
                    self.assertLess(output.stat().st_size, 1_000_000)


if __name__ == "__main__":
    unittest.main()
