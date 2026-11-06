"""Integration checks for seed-target.py; run just workspace-cache-install first."""

import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import time
import unittest


SCRIPT = Path(__file__).with_name("seed-target.py")


class SeedTargetTest(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix="musubi-cache-test-")
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        self.source = self.root / "target"
        (self.source / "debug/deps").mkdir(parents=True)
        (self.source / "debug/.cargo-lock").touch()
        self.artifact = self.source / "debug/deps/libexample-1234.rlib"
        self.artifact.write_bytes(b"a" * (2 * 1024 * 1024))
        self.destination = self.root / "other-target"

    def seed(self, destination=None):
        return subprocess.run(
            [sys.executable, SCRIPT, self.source, destination or self.destination],
            text=True,
            capture_output=True,
        )

    def test_copies_are_independent_and_preserve_metadata(self):
        self.artifact.chmod(0o640)
        os.utime(self.artifact, ns=(1600000000000000000, 1600000000000000000))
        (self.source / "relative-link").symlink_to("debug/deps/libexample-1234.rlib")
        result = self.seed()
        self.assertEqual(result.returncode, 0, result.stderr)
        copied = self.destination / self.artifact.relative_to(self.source)
        self.assertEqual(copied.read_bytes(), self.artifact.read_bytes())
        self.assertNotEqual(copied.stat().st_ino, self.artifact.stat().st_ino)
        self.assertEqual(stat.S_IMODE(copied.stat().st_mode), 0o640)
        self.assertEqual(copied.stat().st_mtime_ns, self.artifact.stat().st_mtime_ns)
        with copied.open("r+b") as handle:
            handle.write(b"copy")
        self.assertEqual(self.artifact.read_bytes()[:4], b"aaaa")
        with self.artifact.open("r+b") as handle:
            handle.write(b"source")
        self.assertEqual(copied.read_bytes()[:4], b"copy")
        self.assertEqual((self.destination / "relative-link").read_bytes()[:4], b"copy")

    def test_refuses_existing_paths_and_nesting_without_touching_them(self):
        self.destination.mkdir()
        sentinel = self.destination / "sentinel"
        sentinel.write_text("keep")
        self.assertNotEqual(self.seed().returncode, 0)
        self.assertEqual(sentinel.read_text(), "keep")
        nested = self.source / "new-target"
        self.assertNotEqual(self.seed(nested).returncode, 0)
        self.assertFalse(nested.exists())
        broken = self.root / "broken"
        broken.symlink_to("missing")
        self.assertNotEqual(self.seed(broken).returncode, 0)
        self.assertTrue(broken.is_symlink())
        self.assertFalse((self.root / "missing").exists())

    def test_refuses_an_existing_staged_tree(self):
        staging = self.destination.with_name(self.destination.name + ".partial")
        staging.mkdir()
        sentinel = staging / "sentinel"
        sentinel.write_text("keep")
        self.assertNotEqual(self.seed().returncode, 0)
        self.assertEqual(sentinel.read_text(), "keep")
        self.assertFalse(self.destination.exists())

    def test_refuses_symlinks_that_would_retain_source_dependencies(self):
        link = self.source / "link"
        for target in (str(self.artifact), "../elsewhere"):
            with self.subTest(target=target):
                link.symlink_to(target)
                self.assertNotEqual(self.seed().returncode, 0)
                self.assertFalse(self.destination.exists())
                link.unlink()

    def test_live_cargo_build_is_refused(self):
        app = self.root / "app"
        (app / "src").mkdir(parents=True)
        (app / "Cargo.toml").write_text(
            '[package]\nname="cache-lock-test"\nversion="0.0.0"\nedition="2021"\n'
        )
        (app / "src/main.rs").write_text("fn main() {}\n")
        (app / "build.rs").write_text(
            'fn main() {\n'
            '    std::fs::write(std::env::var("CACHE_READY").unwrap(), "ready").unwrap();\n'
            '    let gate = std::env::var("CACHE_GATE").unwrap();\n'
            '    while !std::path::Path::new(&gate).exists() {\n'
            '        std::thread::sleep(std::time::Duration::from_millis(10));\n'
            '    }\n'
            '}\n'
        )
        ready, gate = self.root / "ready", self.root / "gate"
        env = dict(
            os.environ,
            CARGO_TARGET_DIR=str(self.source),
            CARGO_BUILD_JOBS="2",
            CACHE_READY=str(ready),
            CACHE_GATE=str(gate),
        )
        env.pop("CARGO_BUILD_BUILD_DIR", None)
        with (self.root / "build.log").open("w+") as log:
            cargo = subprocess.Popen(
                ["cargo", "build", "--offline"], cwd=app, env=env, stdout=log, stderr=log
            )
            try:
                deadline = time.monotonic() + 30
                while not ready.exists() and cargo.poll() is None and time.monotonic() < deadline:
                    time.sleep(0.01)
                log.seek(0)
                self.assertTrue(ready.exists(), log.read())
                result = self.seed()
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("seed between builds", result.stderr)
                self.assertFalse(self.destination.exists())
                self.assertFalse(self.destination.with_suffix(".partial").exists())
            finally:
                gate.touch()
                cargo.wait(timeout=30)
            self.assertEqual(cargo.returncode, 0)


if __name__ == "__main__":
    unittest.main()
