#!/usr/bin/env python3
"""Fail unless Rocq reports every manifest entry closed under the global context."""

import argparse
import math
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile
from typing import List, Optional, Sequence


PROJECT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MODULES = ("RefineToITree.FibonacciL4", "RefineToITree.Parallel")
CLOSED_REPORT = "Closed under the global context"
QUALIFIED_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


class AuditError(Exception):
    def __init__(self, message: str, exit_code: int = 1):
        super().__init__(message)
        self.exit_code = exit_code


def _valid_name(name: str) -> bool:
    return QUALIFIED_NAME.fullmatch(name) is not None and "_" not in name.split(".")


def parse_manifest(text: str, source: str = "manifest") -> List[str]:
    """Read ordered ASCII Rocq qualified names, allowing blanks and # comments."""
    names = []
    first_lines = {}
    for line_number, line in enumerate(text.splitlines(), 1):
        name = line.partition("#")[0].strip()
        if not name:
            continue
        if not _valid_name(name):
            raise AuditError(
                f"{source}:{line_number}: malformed Rocq name {name!r}"
            )
        if name in first_lines:
            raise AuditError(
                f"{source}:{line_number}: duplicate name {name!r} "
                f"(first listed on line {first_lines[name]})"
            )
        names.append(name)
        first_lines[name] = line_number
    if not names:
        raise AuditError(f"{source}: manifest contains no audited names")
    return names


def read_manifest(path: Path) -> List[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise AuditError(f"cannot read manifest {path}: {error}") from error
    return parse_manifest(text, str(path))


def validate_reports(output: str, names: Sequence[str]) -> int:
    """Require exactly one closed report per name, in manifest order."""
    if not names:
        raise AuditError("cannot validate an audit with no expected names")
    if len(set(names)) != len(names):
        raise AuditError("cannot validate duplicate expected names")
    completed = 0
    active: Optional[str] = None
    body: List[str] = []
    for line_number, line in enumerate(output.splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        if line.startswith("AUDIT-BEGIN"):
            if active is not None:
                raise AuditError(
                    f"{active}: truncated report or duplicate/nested begin marker "
                    f"at output line {line_number}: {line!r}"
                )
            if completed == len(names):
                raise AuditError(f"extra or duplicate assumptions report: {line!r}")
            expected = names[completed]
            if line != f"AUDIT-BEGIN {expected}":
                raise AuditError(
                    f"{expected}: missing, malformed, duplicate, or out-of-order report; "
                    f"expected 'AUDIT-BEGIN {expected}', got {line!r}"
                )
            active = expected
            body = []
        elif line.startswith("AUDIT-END"):
            if active is None:
                raise AuditError(
                    f"unexpected end marker at output line {line_number}: {line!r}"
                )
            if line != f"AUDIT-END {active}":
                raise AuditError(f"{active}: malformed end marker: {line!r}")
            if not body:
                raise AuditError(f"{active}: empty assumptions report")
            if body != [CLOSED_REPORT]:
                details = "\n".join(body)
                if any(item.startswith("Axioms") for item in body):
                    raise AuditError(f"{active}: depends on axioms:\n{details}")
                raise AuditError(
                    f"{active}: unrecognized assumptions report; expected exactly one "
                    f"{CLOSED_REPORT!r} line, got:\n{details}"
                )
            completed += 1
            active = None
        elif active is None:
            expected = names[completed] if completed < len(names) else "end of audit"
            raise AuditError(
                f"{expected}: unexpected output outside an assumptions report "
                f"at line {line_number}: {line!r}"
            )
        else:
            body.append(line)
    if active is not None:
        raise AuditError(
            f"{active}: truncated assumptions report (missing AUDIT-END {active})"
        )
    if completed != len(names):
        raise AuditError(
            f"{names[completed]}: missing assumptions report "
            f"(received {completed} of {len(names)})"
        )
    return completed


def _driver(names: Sequence[str], modules: Sequence[str]) -> str:
    lines = ["Require Import " + " ".join(modules) + "."]
    for name in names:
        lines.extend([
            f'Goal True. idtac "AUDIT-BEGIN {name}". Abort.',
            f"Print Assumptions {name}.",
            f'Goal True. idtac "AUDIT-END {name}". Abort.',
        ])
    return "\n".join(lines) + "\n"


def audit_assumptions(
    project_root: Path,
    manifest: Path,
    modules: Sequence[str],
    rocq: str,
    timeout: float = 120,
) -> int:
    names = read_manifest(manifest)
    if not modules or any(not _valid_name(module) for module in modules):
        raise AuditError(f"malformed Rocq module name(s): {list(modules)!r}")
    try:
        command = shlex.split(rocq)
    except ValueError as error:
        raise AuditError(f"cannot parse --rocq command: {error}") from error
    if not command:
        raise AuditError("--rocq command must not be empty")
    if not project_root.is_dir():
        raise AuditError(f"project root is not a directory: {project_root}")
    theories = project_root / "theories"
    if not theories.is_dir():
        raise AuditError(f"theories directory does not exist: {theories}")

    with tempfile.TemporaryDirectory(prefix="rocq-assumptions-") as directory:
        driver = Path(directory) / "AssumptionsAudit.v"
        driver.write_text(_driver(names, modules), encoding="utf-8")
        command += [
            "repl", "-q", "-batch", "-quiet", "-color", "no",
            "-Q", str(theories), "RefineToITree", "-l", str(driver),
        ]
        try:
            result = subprocess.run(
                command,
                cwd=project_root,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                timeout=timeout,
            )
        except FileNotFoundError as error:
            raise AuditError(f"Rocq executable not found: {command[0]!r}", 127) from error
        except subprocess.TimeoutExpired as error:
            output = error.stdout or ""
            if isinstance(output, bytes):
                output = output.decode("utf-8", errors="replace")
            raise AuditError(
                f"Rocq timed out after {timeout:g} seconds: {shlex.join(command)}"
                + (f"\n{output.rstrip()}" if output else ""),
                124,
            ) from error
        except OSError as error:
            raise AuditError(f"could not execute Rocq: {error}") from error
        if result.returncode:
            raise AuditError(
                f"Rocq exited with status {result.returncode}: {shlex.join(command)}\n"
                + (result.stdout.rstrip() or "(no Rocq output)"),
                result.returncode if result.returncode > 0 else 1,
            )
        return validate_reports(result.stdout, names)


def _positive_timeout(value: str) -> float:
    try:
        timeout = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(
            "timeout must be a positive number of seconds"
        ) from error
    if not math.isfinite(timeout) or timeout <= 0:
        raise argparse.ArgumentTypeError(
            "timeout must be a positive finite number of seconds"
        )
    return timeout


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rocq", default="rocq",
        help="Rocq command, including any wrapper (shell quoting supported)",
    )
    parser.add_argument(
        "--project-root", type=Path, default=PROJECT_ROOT,
        help="project containing theories/ (default: parent of scripts/)",
    )
    parser.add_argument(
        "--manifest", type=Path, default=Path("checks/assumptions.txt"),
        help="names to audit (relative paths use --project-root)",
    )
    parser.add_argument(
        "--module", action="append",
        help="module to import instead of defaults; repeatable "
             f"(default: {', '.join(DEFAULT_MODULES)})",
    )
    parser.add_argument(
        "--timeout", type=_positive_timeout, default=120, metavar="SECONDS",
        help="Rocq timeout (default: 120 seconds)",
    )
    arguments = parser.parse_args(argv)
    root = arguments.project_root.expanduser().resolve()
    manifest = arguments.manifest.expanduser()
    if not manifest.is_absolute():
        manifest = root / manifest
    try:
        count = audit_assumptions(
            root, manifest, arguments.module or DEFAULT_MODULES,
            arguments.rocq, arguments.timeout,
        )
    except AuditError as error:
        print(f"Assumptions audit failed: {error}", file=sys.stderr)
        return error.exit_code
    except (OSError, UnicodeError) as error:
        print(f"Assumptions audit failed: {error}", file=sys.stderr)
        return 1
    label = "name" if count == 1 else "names"
    print(f"Assumptions audit passed: {count} {label} closed under the global context.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
