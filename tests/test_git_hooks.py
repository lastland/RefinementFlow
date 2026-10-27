"""Exercise the local hook through real Git commits in disposable repositories."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


WORKSPACE = Path(__file__).resolve().parents[1]


class GitHooksTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="git hooks tests ")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.repo = self.directory / "repository with spaces"
        self.repo.mkdir()
        self.runtime = self.directory / "runtime temp"
        self.runtime.mkdir()
        # A test may itself run under a pre-commit hook. Do not inherit its
        # repository, temporary index, identity, or configuration overrides.
        self.env = {
            name: value
            for name, value in os.environ.items()
            if not name.startswith("GIT_")
        }
        self.env.update(
            GIT_CONFIG_NOSYSTEM="1",
            GIT_CONFIG_SYSTEM=os.devnull,
            GIT_CONFIG_GLOBAL=os.devnull,
            TMPDIR=str(self.runtime),
        )
        self.git("init", "--quiet", "--template=")
        for relative in ("scripts/git_hooks.py", ".githooks/pre-commit"):
            destination = self.repo / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(WORKSPACE / relative, destination)
        # Git invokes only the installed launcher directly; the versioned hook
        # must also work when its executable bit is absent.
        (self.repo / ".githooks/pre-commit").chmod(0o644)
        self.hook = self.repo / ".git/hooks/pre-commit"

    def command(self, arguments, *, check=True, env=None, input=None):
        result = subprocess.run(
            arguments,
            cwd=self.repo,
            env=self.env if env is None else env,
            input=input,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=30,
        )
        if check:
            self.assertEqual(result.returncode, 0, result.stdout)
        return result

    def git(self, *arguments, **kwargs):
        return self.command(
            [
                "git",
                "-c", "user.name=Hook Test",
                "-c", "user.email=hook-test@example.invalid",
                *arguments,
            ],
            **kwargs,
        )

    def hook_command(self, command, **kwargs):
        return self.command(
            [sys.executable, str(self.repo / "scripts/git_hooks.py"), command],
            **kwargs,
        )

    def test_commit_checks_staged_files_and_isolates_build_and_nested_git(self):
        (self.repo / "Makefile").write_text(
            ".PHONY: check\n"
            "check:\n"
            "\t@python3 -c 'from pathlib import Path; "
            'assert Path("proof.txt").read_text() == "staged\\n"'
            "'\n"
            "\t@test ! -e untracked.txt\n"
            '\t@git init --quiet --template= "nested repo"\n'
            '\t@touch "nested repo/nested.txt"\n'
            '\t@git -C "nested repo" add nested.txt\n'
            '\t@test "$$(git -C "nested repo" ls-files)" = nested.txt\n'
            "\t@touch build-artifact\n"
            '\t@pwd > "$$SNAPSHOT_RECORD"\n'
            "\t@printf 'successful check output\\n'\n"
        )
        proof = self.repo / "proof.txt"
        proof.write_text("staged\n")
        self.git("add", ".")
        proof.write_text("unstaged\n")
        (self.repo / "untracked.txt").write_text("not in the snapshot\n")
        index_before = self.git("ls-files", "--stage", "-z").stdout
        config_before = (self.repo / ".git/config").read_bytes()
        self.hook_command("install")
        self.assertEqual(self.hook.stat().st_mode & 0o777, 0o755)
        # The launcher must find the repository at execution time rather than
        # embedding the installation path.
        moved = self.directory / "moved repository with spaces"
        self.repo.rename(moved)
        self.repo = moved
        self.hook = self.repo / ".git/hooks/pre-commit"
        proof = self.repo / "proof.txt"

        record = self.directory / "snapshot path"
        commit_env = dict(self.env)
        commit_env.update(
            GIT_DIR=str(self.repo / ".git"),
            GIT_WORK_TREE=str(self.repo),
            GIT_INDEX_FILE=str(self.repo / ".git/index"),
            SNAPSHOT_RECORD=str(record),
        )
        result = self.git("commit", "-m", "Check staged fixture", env=commit_env)

        self.assertIn("staged snapshot", result.stdout)
        self.assertIn("passed", result.stdout)
        self.assertNotIn("successful check output", result.stdout)
        self.assertEqual(self.git("show", "HEAD:proof.txt").stdout, "staged\n")
        self.assertEqual(proof.read_text(), "unstaged\n")
        self.assertTrue((self.repo / "untracked.txt").is_file())
        self.assertEqual(self.git("ls-files", "--stage", "-z").stdout, index_before)
        self.assertEqual((self.repo / ".git/config").read_bytes(), config_before)
        self.assertFalse((self.repo / "build-artifact").exists())
        self.assertFalse((self.repo / "nested repo").exists())
        self.assertFalse(Path(record.read_text().strip()).exists())
        self.assertEqual(list(self.runtime.iterdir()), [])

    def test_commit_rejects_bad_index_even_when_worktree_makefile_is_fixed(self):
        makefile = self.repo / "Makefile"
        makefile.write_text(
            ".PHONY: check\n"
            "check:\n"
            '\t@pwd > "$$SNAPSHOT_RECORD"\n'
            "\t@touch failed-build-artifact\n"
            "\t@printf 'staged Makefile failure\\n'\n"
            "\t@false\n"
        )
        self.git("add", ".")
        makefile.write_text(".PHONY: check\ncheck:\n\t@true\n")
        untracked = self.repo / "untracked.txt"
        untracked.write_text("preserve me\n")
        self.hook_command("install")
        index_before = self.git("ls-files", "--stage", "-z").stdout
        staged_before = self.git("diff", "--cached", "--binary").stdout
        status_before = self.git("status", "--porcelain=v1", "--untracked-files=all").stdout
        worktree_before = makefile.read_bytes()
        self.assertNotEqual(self.git("rev-parse", "--verify", "HEAD", check=False).returncode, 0)
        record = self.directory / "failed snapshot path"
        commit_env = dict(self.env, SNAPSHOT_RECORD=str(record))

        result = self.git("commit", "-m", "Reject staged fixture", env=commit_env, check=False)

        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("staged snapshot failed make check", result.stdout)
        self.assertIn("staged Makefile failure", result.stdout)
        self.assertNotEqual(self.git("rev-parse", "--verify", "HEAD", check=False).returncode, 0)
        self.assertEqual(self.git("ls-files", "--stage", "-z").stdout, index_before)
        self.assertEqual(self.git("diff", "--cached", "--binary").stdout, staged_before)
        self.assertEqual(
            self.git("status", "--porcelain=v1", "--untracked-files=all").stdout,
            status_before,
        )
        self.assertEqual(makefile.read_bytes(), worktree_before)
        self.assertEqual(untracked.read_text(), "preserve me\n")
        self.assertFalse((self.repo / "failed-build-artifact").exists())
        self.assertFalse(Path(record.read_text().strip()).exists())
        self.assertEqual(list(self.runtime.iterdir()), [])

    def test_install_is_idempotent_and_does_not_edit_git_config(self):
        config_before = (self.repo / ".git/config").read_bytes()
        self.hook_command("install")
        content = self.hook.read_bytes()
        metadata = self.hook.stat()

        result = self.hook_command("install")

        self.assertIn("already installed", result.stdout)
        self.assertEqual(self.hook.read_bytes(), content)
        self.assertEqual(self.hook.stat().st_ino, metadata.st_ino)
        self.assertEqual(self.hook.stat().st_mtime_ns, metadata.st_mtime_ns)
        self.assertEqual(self.hook.stat().st_mode & 0o777, 0o755)
        self.assertEqual((self.repo / ".git/config").read_bytes(), config_before)

    def test_install_refuses_and_preserves_an_existing_hook(self):
        self.hook.parent.mkdir()
        content = b"#!/bin/sh\n# The user's hook.\nexit 42\n"
        self.hook.write_bytes(content)
        self.hook.chmod(0o700)
        config_before = (self.repo / ".git/config").read_bytes()

        result = self.hook_command("install", check=False)

        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("refusing", result.stdout)
        self.assertEqual(self.hook.read_bytes(), content)
        self.assertEqual(self.hook.stat().st_mode & 0o777, 0o700)
        self.assertEqual((self.repo / ".git/config").read_bytes(), config_before)

    def test_install_refuses_hook_symlinks_even_to_managed_content(self):
        self.hook_command("install")
        managed = self.hook.read_bytes()
        self.hook.unlink()
        for kind in ("existing", "dangling", "managed"):
            with self.subTest(kind=kind):
                target = self.directory / (kind + " external hook")
                if kind != "dangling":
                    target.write_bytes(managed if kind == "managed" else b"user hook\n")
                    target.chmod(0o600)
                    before = target.read_bytes()
                self.hook.symlink_to(target)
                try:
                    result = self.hook_command("install", check=False)

                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn("refusing", result.stdout)
                    self.assertTrue(self.hook.is_symlink())
                    self.assertEqual(self.hook.readlink(), target)
                    if kind == "dangling":
                        self.assertFalse(target.exists())
                    else:
                        self.assertEqual(target.read_bytes(), before)
                        self.assertEqual(target.stat().st_mode & 0o777, 0o600)
                finally:
                    self.hook.unlink()

    def test_install_refuses_a_symlinked_hooks_directory(self):
        for dangling in (False, True):
            with self.subTest(dangling=dangling):
                target = self.directory / ("dangling hooks" if dangling else "external hooks")
                if not dangling:
                    target.mkdir()
                    (target / "sentinel").write_text("preserve me\n")
                self.hook.parent.symlink_to(target, target_is_directory=True)
                try:
                    result = self.hook_command("install", check=False)

                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn("refusing", result.stdout)
                    self.assertTrue(self.hook.parent.is_symlink())
                    self.assertFalse((target / "pre-commit").exists())
                    if dangling:
                        self.assertFalse(target.exists())
                    else:
                        self.assertEqual((target / "sentinel").read_text(), "preserve me\n")
                finally:
                    self.hook.parent.unlink()

    def test_install_refuses_a_directory_at_the_hook_path(self):
        self.hook.mkdir(parents=True)
        sentinel = self.hook / "sentinel"
        sentinel.write_text("preserve me\n")

        result = self.hook_command("install", check=False)

        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("refusing", result.stdout)
        self.assertEqual(sentinel.read_text(), "preserve me\n")

    def test_install_refuses_configured_hooks_path_without_changing_config(self):
        custom = self.directory / "custom hooks"
        custom.mkdir()
        existing = custom / "pre-commit"
        existing.write_text("user framework\n")
        config_before = (self.repo / ".git/config").read_bytes()
        for value in (str(custom), ""):
            with self.subTest(value=value):
                env = dict(self.env)
                env.update(
                    GIT_CONFIG_COUNT="1",
                    GIT_CONFIG_KEY_0="core.hooksPath",
                    GIT_CONFIG_VALUE_0=value,
                )

                result = self.hook_command("install", check=False, env=env)

                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("core.hooksPath", result.stdout)
                self.assertIn("refusing", result.stdout)
                self.assertFalse(self.hook.exists())
                self.assertEqual(existing.read_text(), "user framework\n")
                self.assertEqual((self.repo / ".git/config").read_bytes(), config_before)

    def test_missing_tools_report_clear_errors_and_clean_up_snapshots(self):
        (self.repo / "Makefile").write_text("check:\n\t@true\n")
        self.git("add", ".")
        tools = self.directory / "tools"
        tools.mkdir()
        env = dict(self.env, PATH=str(tools))

        result = self.hook_command("check", check=False, env=env)

        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Git is required", result.stdout)
        (tools / "git").symlink_to(shutil.which("git"))

        result = self.hook_command("check", check=False, env=env)

        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("opam is required", result.stdout)
        self.assertNotIn("Traceback", result.stdout)
        self.assertEqual(list(self.runtime.iterdir()), [])

    def test_check_refuses_unmerged_index_without_running_make(self):
        (self.repo / "Makefile").write_text("check:\n\t@printf 'must not run\\n'\n")
        self.git("add", ".")
        base, ours, theirs = [
            self.git("hash-object", "-w", "--stdin", input=value).stdout.strip()
            for value in ("base\n", "ours\n", "theirs\n")
        ]
        self.git(
            "update-index", "--index-info",
            input=(
                "0 {}\tMakefile\n".format("0" * len(base))
                + "100644 {} 1\tMakefile\n".format(base)
                + "100644 {} 2\tMakefile\n".format(ours)
                + "100644 {} 3\tMakefile\n".format(theirs)
            ),
        )
        index_before = self.git("ls-files", "--stage", "-z").stdout
        worktree_before = (self.repo / "Makefile").read_bytes()

        result = self.hook_command("check", check=False)

        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("cannot export staged snapshot", result.stdout)
        self.assertIn("unmerged", result.stdout)
        self.assertNotIn("must not run", result.stdout)
        self.assertEqual(self.git("ls-files", "--stage", "-z").stdout, index_before)
        self.assertEqual((self.repo / "Makefile").read_bytes(), worktree_before)
        self.assertEqual(list(self.runtime.iterdir()), [])

    def test_export_failure_reports_git_error_without_running_check(self):
        (self.repo / "Makefile").write_text("check:\n\t@printf 'must not run\\n'\n")
        self.git("add", ".")
        object_id = self.git("hash-object", "--stdin", input="length probe\n").stdout.strip()
        missing_object = "f" * len(object_id)
        self.git("update-index", "--add", "--cacheinfo", "100644,{},missing.txt".format(missing_object))
        index_before = self.git("ls-files", "--stage", "-z").stdout

        result = self.hook_command("check", check=False)

        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("checkout-index", result.stdout)
        self.assertIn("missing.txt", result.stdout)
        self.assertNotIn("must not run", result.stdout)
        self.assertNotIn("Traceback", result.stdout)
        self.assertEqual(self.git("ls-files", "--stage", "-z").stdout, index_before)
        self.assertEqual(list(self.runtime.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
