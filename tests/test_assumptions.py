"""Exercise the assumption guard without adding proof fixtures to the project."""

import importlib.util
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest


PROJECT_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = PROJECT_ROOT / "scripts" / "check_assumptions.py"
SPEC = importlib.util.spec_from_file_location("check_assumptions", SCRIPT)
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


def report(name, body="Closed under the global context"):
    return f"AUDIT-BEGIN {name}\n{body}\nAUDIT-END {name}\n"


class ManifestTests(unittest.TestCase):
    def test_comments_blanks_and_qualified_names_preserve_order(self):
        self.assertEqual(
            audit.parse_manifest(
                "\n# theorem names\nfirst\n\n Fixture.second' # comment\n_last\n"
            ),
            ["first", "Fixture.second'", "_last"],
        )

    def test_empty_manifests_are_rejected(self):
        for text in ("", " \n\t\n", "# only a comment\n\n"):
            with self.subTest(text=text):
                with self.assertRaisesRegex(audit.AuditError, "no audited names"):
                    audit.parse_manifest(text)

    def test_duplicate_names_identify_both_lines(self):
        with self.assertRaises(audit.AuditError) as failure:
            audit.parse_manifest("first\n# comment\nfirst # repeated\n", "names.txt")
        message = str(failure.exception)
        self.assertIn("names.txt:3", message)
        self.assertIn("duplicate name 'first'", message)
        self.assertIn("first listed on line 1", message)

    def test_malformed_names_are_rejected(self):
        for name in ("two names", "first.", ".first", "A..first", "3first",
                     "A/first", "_", "A._", '"first"', "first; Abort.",
                     "first (* comment *)"):
            with self.subTest(name=name):
                with self.assertRaisesRegex(audit.AuditError, "malformed Rocq name"):
                    audit.parse_manifest(name)


class ReportParserTests(unittest.TestCase):
    def test_positive_reports_in_manifest_order(self):
        self.assertEqual(
            audit.validate_reports(
                report("first") + report("Fixture.second'"),
                ["first", "Fixture.second'"],
            ),
            2,
        )

    def test_blank_lines_and_line_endings_are_allowed(self):
        output = "\r\n AUDIT-BEGIN first \r\n\r\n Closed under the global context \r\nAUDIT-END first\r\n\r\n"
        self.assertEqual(audit.validate_reports(output, ["first"]), 1)

    def test_axiom_reports_are_rejected(self):
        for body in ("Axioms:\nassumed : True",
                     "Closed under the global context\nAxioms:\nassumed : True"):
            with self.subTest(body=body):
                with self.assertRaisesRegex(audit.AuditError, "first: depends on axioms"):
                    audit.validate_reports(report("first", body), ["first"])

    def test_empty_output_is_rejected(self):
        for output in ("", " \n\t\n"):
            with self.subTest(output=output):
                with self.assertRaisesRegex(audit.AuditError, "first: missing assumptions report"):
                    audit.validate_reports(output, ["first"])

    def test_missing_reports_are_rejected(self):
        with self.assertRaisesRegex(audit.AuditError, "second: missing assumptions report"):
            audit.validate_reports(report("first"), ["first", "second"])

    def test_empty_report_is_rejected(self):
        with self.assertRaisesRegex(audit.AuditError, "first: empty assumptions report"):
            audit.validate_reports(report("first", " \n"), ["first"])

    def test_truncated_reports_are_rejected(self):
        for output in ("AUDIT-BEGIN first\n",
                       "AUDIT-BEGIN first\nClosed under the global context\n",
                       "AUDIT-BEGIN first\nAUDIT-BEGIN first\n"):
            with self.subTest(output=output):
                with self.assertRaisesRegex(audit.AuditError, "first: truncated"):
                    audit.validate_reports(output, ["first"])

    def test_duplicate_reports_are_rejected(self):
        for names in (["first"], ["first", "second"]):
            with self.subTest(names=names):
                with self.assertRaisesRegex(audit.AuditError, "duplicate"):
                    audit.validate_reports(report("first") * 2, names)

    def test_duplicate_closed_messages_are_rejected(self):
        with self.assertRaisesRegex(audit.AuditError, "first: unrecognized"):
            audit.validate_reports(
                report("first", "Closed under the global context\nClosed under the global context"),
                ["first"],
            )

    def test_malformed_markers_are_rejected(self):
        for output in (
            "AUDIT-BEGIN first extra\nClosed under the global context\nAUDIT-END first\n",
            "AUDIT-BEGIN\nClosed under the global context\nAUDIT-END first\n",
            "AUDIT-BEGIN first\nClosed under the global context\nAUDIT-END other\n",
            "AUDIT-END first\n",
        ):
            with self.subTest(output=output):
                with self.assertRaises(audit.AuditError):
                    audit.validate_reports(output, ["first"])

    def test_out_of_order_or_unexpected_names_are_rejected(self):
        for output in (report("second") + report("first"), report("other")):
            with self.subTest(output=output):
                with self.assertRaisesRegex(audit.AuditError, "first:.*out-of-order"):
                    audit.validate_reports(output, ["first", "second"])

    def test_opaque_or_unrecognized_report_bodies_are_rejected(self):
        for body in ("Opaque:\nfirst : True", "unknown report format",
                     "Closed under the global context\nextra output",
                     "Closed under the global context."):
            with self.subTest(body=body):
                with self.assertRaisesRegex(audit.AuditError, "first: unrecognized"):
                    audit.validate_reports(report("first", body), ["first"])

    def test_extra_output_outside_reports_is_rejected(self):
        for output in (
            "Closed under the global context\n" + report("first"),
            report("first") + "Closed under the global context\n",
            report("first") + "Axioms:\nhidden : True\n",
        ):
            with self.subTest(output=output):
                with self.assertRaisesRegex(audit.AuditError, "unexpected output outside"):
                    audit.validate_reports(output, ["first"])

    def test_empty_or_duplicate_expectations_are_rejected(self):
        for names in ([], ["first", "first"]):
            with self.subTest(names=names):
                with self.assertRaises(audit.AuditError):
                    audit.validate_reports(report("first") * len(names), names)


class CommandFailureTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="assumptions-cli-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "theories").mkdir()
        (self.root / "checks").mkdir()
        self.manifest = self.root / "checks" / "assumptions.txt"
        self.manifest.write_text("first\n", encoding="utf-8")

    def run_command(self, rocq, *options):
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--project-root", str(self.root),
             "--rocq", rocq, *options],
            capture_output=True,
            text=True,
            timeout=10,
        )

    def run_python(self, code, *options):
        command = shlex.join([sys.executable, "-c", code])
        return self.run_command(command, *options)

    def test_zero_exit_with_empty_output_fails(self):
        result = self.run_python("pass")
        self.assertEqual(result.returncode, 1)
        self.assertIn("first: missing assumptions report", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_nonzero_exit_is_preserved_even_with_closed_output(self):
        result = self.run_python(
            f"import sys; sys.stdout.write({report('first')!r}); "
            "sys.stderr.write('intentional command failure\\n'); sys.exit(7)"
        )
        self.assertEqual(result.returncode, 7)
        self.assertIn("Rocq exited with status 7", result.stderr)
        self.assertIn("intentional command failure", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_axiom_output_on_stderr_is_not_lost(self):
        result = self.run_python(
            "import sys; sys.stdout.write('AUDIT-BEGIN first\\n'); sys.stdout.flush(); "
            "sys.stderr.write('Axioms:\\nassumed : True\\n'); sys.stderr.flush(); "
            "sys.stdout.write('AUDIT-END first\\n')"
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("first: depends on axioms", result.stderr)
        self.assertIn("assumed : True", result.stderr)

    def test_missing_executable_has_clear_nonzero_result(self):
        result = self.run_command(shlex.join([str(self.root / "missing rocq")]))
        self.assertEqual(result.returncode, 127)
        self.assertIn("Rocq executable not found", result.stderr)

    def test_timeout_has_clear_nonzero_result(self):
        result = self.run_python("import time; time.sleep(3)", "--timeout", "0.2")
        self.assertEqual(result.returncode, 124)
        self.assertIn("Rocq timed out after 0.2 seconds", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_empty_or_malformed_commands_fail(self):
        for command, message in (("", "must not be empty"), ("'", "cannot parse --rocq")):
            with self.subTest(command=command):
                result = self.run_command(command)
                self.assertEqual(result.returncode, 1)
                self.assertIn(message, result.stderr)

    def test_missing_manifest_fails(self):
        result = self.run_python("pass", "--manifest", "absent.txt")
        self.assertEqual(result.returncode, 1)
        self.assertIn("cannot read manifest", result.stderr)
        self.assertIn("absent.txt", result.stderr)

    def test_non_utf8_manifest_fails(self):
        self.manifest.write_bytes(b"first\n\xff\n")
        result = self.run_python("pass")
        self.assertEqual(result.returncode, 1)
        self.assertIn("cannot read manifest", result.stderr)

    def test_invalid_module_fails(self):
        result = self.run_python("pass", "--module", "Fixture; Abort.")
        self.assertEqual(result.returncode, 1)
        self.assertIn("malformed Rocq module", result.stderr)

    def test_invalid_timeout_is_a_usage_error(self):
        for timeout in ("0", "-1", "nan", "inf", "invalid"):
            with self.subTest(timeout=timeout):
                result = self.run_python("pass", "--timeout", timeout)
                self.assertEqual(result.returncode, 2)
                self.assertIn("timeout must be a positive", result.stderr)


class RocqIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rocq = os.environ.get("ROCQ", "rocq")
        command = shlex.split(cls.rocq)
        if not command:
            raise RuntimeError("ROCQ must not be empty")
        if shutil.which(command[0]) is None:
            if "ROCQ" in os.environ:
                raise RuntimeError("ROCQ executable not found: " + command[0])
            raise unittest.SkipTest("Rocq is unavailable; run under opam exec")

        temporary = tempfile.TemporaryDirectory(prefix="assumptions-integration-")
        cls.addClassCleanup(temporary.cleanup)
        cls.root = Path(temporary.name) / "project with spaces"
        cls.theories = cls.root / "theories"
        cls.theories.mkdir(parents=True)
        fixture = cls.theories / "Fixture.v"
        fixture.write_text(
            "Axiom unused : False.\n"
            "Theorem closed : True.\n"
            "Proof. exact I. Qed.\n"
            "Theorem also_closed : True.\n"
            "Proof. exact I. Qed.\n"
            "Axiom assumed : True.\n"
            "Theorem uses_axiom : True.\n"
            "Proof. exact assumed. Qed.\n"
            "Theorem admitted : True.\n"
            "Admitted.\n",
            encoding="utf-8",
        )
        result = subprocess.run(
            command + ["compile", "-quiet", "-Q", str(cls.theories),
                       "RefineToITree", str(fixture)],
            cwd=cls.root,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=120,
        )
        if result.returncode:
            raise RuntimeError("Could not compile Rocq fixture:\n" + result.stdout)

    def run_audit(self, names, rocq=None, options=()):
        manifest = self.root / "assumptions.txt"
        manifest.write_text("\n".join(names) + "\n", encoding="utf-8")
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--project-root", str(self.root),
             "--manifest", str(manifest), "--module", "RefineToITree.Fixture",
             "--rocq", self.rocq if rocq is None else rocq, *options],
            cwd=self.root,
            capture_output=True,
            text=True,
            timeout=130,
        )

    def test_closed_passes_despite_unused_axioms(self):
        result = self.run_audit(["closed"])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("1 name closed under the global context", result.stdout)
        self.assertEqual(result.stderr, "")

    def test_manifest_determines_report_count(self):
        result = self.run_audit(["# comments are ignored", "closed", "", "also_closed"])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("2 names closed under the global context", result.stdout)

    def test_defaults_import_target_and_independent_parallel_library(self):
        with tempfile.TemporaryDirectory(prefix="assumptions-defaults-") as directory:
            root = Path(directory)
            theories = root / "theories"
            theories.mkdir()
            checks = root / "checks"
            checks.mkdir()
            names = []
            for module, theorem in (("FibonacciL4", "target_closed"),
                                    ("Parallel", "parallel_closed")):
                fixture = theories / f"{module}.v"
                fixture.write_text(
                    f"Theorem {theorem} : True.\nProof. exact I. Qed.\n",
                    encoding="utf-8",
                )
                result = subprocess.run(
                    shlex.split(self.rocq) + [
                        "compile", "-quiet", "-Q", str(theories),
                        "RefineToITree", str(fixture),
                    ],
                    cwd=root,
                    capture_output=True,
                    text=True,
                    timeout=120,
                )
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                names.append(f"RefineToITree.{module}.{theorem}")
            (checks / "assumptions.txt").write_text(
                "\n".join(names) + "\n", encoding="utf-8",
            )
            result = subprocess.run(
                [sys.executable, str(SCRIPT), "--project-root", str(root),
                 "--rocq", self.rocq],
                cwd=root,
                capture_output=True,
                text=True,
                timeout=130,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("2 names closed under the global context", result.stdout)
            self.assertEqual(result.stderr, "")

    def test_axiom_dependent_theorem_fails(self):
        result = self.run_audit(["closed", "uses_axiom"])
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("uses_axiom: depends on axioms", result.stderr)
        self.assertIn("assumed", result.stderr)
        self.assertIn("Axioms:", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_admitted_theorem_fails(self):
        result = self.run_audit(["admitted"])
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("admitted: depends on axioms", result.stderr)
        self.assertIn("Axioms:", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_missing_name_preserves_rocq_failure(self):
        result = self.run_audit(["closed", "does_not_exist"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Rocq exited with status", result.stderr)
        self.assertIn("does_not_exist", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_quoted_wrapper_and_repeated_modules_override_defaults(self):
        wrapper = shlex.join([
            sys.executable, "-c",
            "import os, sys; os.execvp(sys.argv[1], sys.argv[1:])",
            *shlex.split(self.rocq),
        ])
        result = self.run_audit(
            ["RefineToITree.Fixture.closed"], rocq=wrapper,
            options=("--module", "Corelib.Init.Logic"),
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("1 name closed under the global context", result.stdout)


if __name__ == "__main__":
    unittest.main()
