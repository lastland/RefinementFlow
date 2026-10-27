#!/usr/bin/env python3
"""Regenerate and check the approved Rocq JSON-to-C fragment (Python 3.9+).

Build the theory .vo prerequisites first (normally with make check-c).  Direct
use re-extracts the actual production roots; --reuse-extraction is for a make
target that has just run extract-c.  All evidence and native artifacts stay in
build/c.  These execution/artifact checks are not a compiler correctness proof.
"""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
MODULES = ("Cost", "Array", "Binary", "Fibonacci", "FibonacciL2", "FibonacciL3", "FibonacciL4")
# Preserve the production extraction order and its registered helper names.
ENTRYPOINTS = {"fib_L3": "fib_l3", "fib_L4": "fib_l4", "fib_L1": "fib_l1", "fib_L2": "fib_l2"}
SUPPORTED_RANGE = (0, 91)
NATIVE_RANGES = {"fib_L3": (0, 91), "fib_L4": (0, 91), "fib_L1": (0, 30), "fib_L2": (0, 91)}
REGISTRY = (
    "bind", "function_entry", "cost_iter", "cost_add", "cost_mul", "cost_sub",
    "array_alloc", "array_read", "array_set", "add", "mul", "sub", "div2", "leb", "reSum_id",
)
FIXTURES = (
    "stateSwapFixture", "directArithmeticFixture", "sequencingFixture",
    "conditionalFixture", "branchInitializationFixture", "recursiveCountdownFixture",
)
WRAP_FIXTURES = ("costSubFixture", "pureSubFixture")
REJECTIONS = {
    "uninitializedFixture": r"init",
    "outOfBoundsReadFixture": r"bound|range",
    "outOfBoundsWriteFixture": r"bound|range",
    "dynamicReadFixture": r"static|dynamic|constant",
    "dynamicWriteFixture": r"static|dynamic|constant",
    "dynamicSizeFixture": r"static|dynamic|constant",
    "multipleAllocationFixture": r"alloc",
    "allocationInLoopFixture": r"alloc|loop",
    "allocationInBranchFixture": r"alloc|branch",
    "branchOnlyInitializationFixture": r"init",
    "loopOnlyInitializationFixture": r"init",
    "rawTauFixture": r"ret|tau|tree|constructor",
    "recursiveHelperFixture": r"unregistered|recursive|global|helper",
    "rawEffectFixture": r"unregistered|effect|trigger|global|tree|constructor",
}
SMALL_INPUTS = (0, 1, 2, 3, 4, 5, 7, 8, 10, 15, 16, 20)
SMALL_VALUES = (0, 1, 1, 2, 3, 5, 13, 21, 55, 610, 987, 6765)
L1_SMALL_INPUTS = (0, 1, 2, 3, 4, 5, 7, 8, 10)
L1_SMALL_VALUES = (0, 1, 1, 2, 3, 5, 13, 21, 55)
ROCQ_SAMPLES = {
    "fib_L3": (SMALL_INPUTS, SMALL_VALUES), "fib_L4": (SMALL_INPUTS, SMALL_VALUES),
    "fib_L1": (L1_SMALL_INPUTS, L1_SMALL_VALUES), "fib_L2": (SMALL_INPUTS, SMALL_VALUES),
}
STRICT_FLAGS = (
    "-std=c11", "-Wall", "-Wextra", "-Wpedantic", "-Werror", "-Wconversion",
    "-Wshadow", "-Wstrict-prototypes", "-Wmissing-prototypes", "-Wformat=2",
    "-Wundef", "-Wcast-qual", "-Wwrite-strings", "-Wvla",
)
SANITIZER_FLAGS = (
    "-O1", "-g", "-fno-omit-frame-pointer",
    "-fsanitize=address,undefined,unsigned-integer-overflow", "-fno-sanitize-recover=all",
)
SANITIZER_ENV = {
    "ASAN_OPTIONS": "halt_on_error=1:abort_on_error=1",
    "UBSAN_OPTIONS": "halt_on_error=1:print_stacktrace=1",
}


class CheckError(Exception):
    def __init__(self, message, exit_code=1):
        super().__init__(message)
        self.exit_code = exit_code


def require(condition, message):
    if not condition:
        raise CheckError(message)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command_words(value, option):
    try:
        words = shlex.split(value)
    except ValueError as error:
        raise CheckError(f"cannot parse {option}: {error}") from error
    require(words, f"{option} command must not be empty")
    return words


def positive_timeout(value):
    try:
        seconds = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("timeout must be a positive finite number") from error
    if not math.isfinite(seconds) or seconds <= 0:
        raise argparse.ArgumentTypeError("timeout must be a positive finite number")
    return seconds


class Commands:
    """Retain stdout, stderr, and the exact command, including failed attempts."""

    def __init__(self, directory, timeout):
        self.directory = directory
        self.timeout = timeout
        self.journal = []
        (directory / "logs").mkdir(exist_ok=True)
        write_json(directory / "commands.json", self.journal)

    def run(self, label, argv, environment=None, empty_stderr=False):
        argv = [str(word) for word in argv]
        environment = environment or {}
        env = dict(os.environ, **environment)
        started = time.monotonic()
        failure = None
        exit_code = 1
        try:
            result = subprocess.run(
                argv, cwd=ROOT, env=env, text=True, encoding="utf-8", errors="replace",
                capture_output=True, timeout=self.timeout,
            )
            stdout, stderr, returncode = result.stdout, result.stderr, result.returncode
        except subprocess.TimeoutExpired as error:
            def decoded(text):
                return text.decode("utf-8", errors="replace") if isinstance(text, bytes) else text or ""
            stdout, stderr, returncode = decoded(error.stdout), decoded(error.stderr), None
            failure = f"{label} timed out after {self.timeout:g} seconds"
            exit_code = 124
        except OSError as error:
            stdout, stderr, returncode = "", str(error), None
            failure = f"cannot execute {label} ({argv[0]!r}): {error}"
            exit_code = 127 if isinstance(error, FileNotFoundError) else 1
        stdout_path = f"logs/{label}.stdout.txt"
        stderr_path = f"logs/{label}.stderr.txt"
        (self.directory / stdout_path).write_text(stdout, encoding="utf-8")
        (self.directory / stderr_path).write_text(stderr, encoding="utf-8")
        self.journal.append({
            "label": label, "argv": argv, "cwd": str(ROOT), "environment": environment,
            "returncode": returncode, "seconds": round(time.monotonic() - started, 3),
            "stdout": stdout_path, "stderr": stderr_path,
        })
        write_json(self.directory / "commands.json", self.journal)
        if failure is None and returncode != 0:
            failure = f"{label} exited with status {returncode}"
        if failure is None and empty_stderr and stderr:
            failure = f"{label} produced unexpected stderr"
        if failure:
            details = "\n".join(text.rstrip() for text in (stdout, stderr) if text.strip())
            raise CheckError(
                f"{failure}: {shlex.join(argv)}\n{details}\n"
                f"Command logs: {self.directory / 'commands.json'}", exit_code,
            )
        return stdout


def declarations(document, label):
    require(isinstance(document, dict) and isinstance(document.get("declarations"), list),
            f"{label}: missing extraction declarations")
    result = {}
    for declaration in document["declarations"]:
        require(isinstance(declaration, dict), f"{label}: malformed declaration")
        # Nat primitives are recursive definitions, represented as fixgroup
        # items rather than top-level named term declarations by Rocq 9.2.
        members = declaration.get("fixlist") if declaration.get("what") == "decl:fixgroup" else [declaration]
        require(isinstance(members, list), f"{label}: malformed recursive declaration group")
        for member in members:
            require(isinstance(member, dict), f"{label}: malformed declaration group member")
            name = member.get("name")
            if name is not None:
                require(isinstance(name, str) and name not in result,
                        f"{label}: malformed or duplicate extracted name {name!r}")
                result[name] = member
    return result


def read_document(path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, ValueError) as error:
        raise CheckError(f"cannot read extraction JSON {path}: {error}") from error


def check_extraction_identity(production, fixtures):
    actual = declarations(production, "targets.json")
    independent = declarations(fixtures, "fixtures.json")
    for name in (*ENTRYPOINTS, *REGISTRY):
        require(name in actual and name in independent,
                f"missing production root/registered operation {name!r}")
        require(actual[name] == independent[name],
                f"fixture extraction changed production declaration/registry name {name!r}")
    for name in (*FIXTURES, *WRAP_FIXTURES, *REJECTIONS):
        require(name in independent, f"missing independently extracted fixture {name!r}")


def without_comments(text):
    return re.sub(r"/\*.*?\*/|//[^\n]*", "", text, flags=re.DOTALL)


def check_production_artifacts(source, header, metadata):
    """Check the actual public interface and direct scalar/local-array output."""
    code, interface = without_comments(source), without_comments(header)
    forbidden = (
        r"\b(?:itree\w*|node\w*|RetF|TauF|VisF|Ret|Tau|Vis|Go|trigger|event\w*|tick\w*|cost\w*|"
        r"function_entry|interp\w*|dispatch\w*|closure\w*|continuation\w*|"
        r"malloc|calloc|realloc|free|alloca|struct|union|static)\b"
    )
    match = re.search(forbidden, code + "\n" + interface, flags=re.IGNORECASE)
    require(match is None, f"generated artifacts retain runtime machinery: {match.group() if match else ''}")
    require(not re.search(r"\(\s*\*", code + interface), "generated artifact contains a function pointer")
    includes = re.findall(r'^\s*#\s*include\s*([<"].*?[>"])', code + "\n" + interface, re.MULTILINE)
    require(set(includes) <= {'"generated.h"', '<stdbool.h>', '<stdint.h>'},
            f"unexpected generated runtime dependency: {includes!r}")
    require('"generated.h"' in includes and '<stdint.h>' in includes,
            "generated C/header must include generated.h/stdint.h")
    prototype_pattern = r"\buint64_t\s+(\w+)\s*\(\s*uint64_t\s+input\s*\)\s*;"
    prototypes = re.findall(prototype_pattern, interface)
    require(sorted(prototypes) == sorted(ENTRYPOINTS.values()),
            f"unexpected value-only public prototypes: {prototypes!r}")
    require("[" not in interface, "public header exposes working arrays")
    public_remainder = re.sub(r"^\s*#.*$", "", interface, flags=re.MULTILINE)
    public_remainder = re.sub(prototype_pattern, "", public_remainder).strip()
    require(not public_remainder, f"unexpected additional public declarations: {public_remainder!r}")
    require(isinstance(metadata, dict) and set(metadata) == set(ENTRYPOINTS),
            "production lowering metadata does not describe exactly the actual L1-L4 roots")
    remainder = code
    for target, c_name in ENTRYPOINTS.items():
        item = metadata[target]
        expected_cells = 0 if target == "fib_L1" else 2
        require(isinstance(item, dict) and item.get("c_name") == c_name
                and type(item.get("array_cells")) is int and item["array_cells"] == expected_cells,
                f"{target}: expected {expected_cells}-cell private storage: {item!r}")
        loops = item.get("loops")
        require(type(loops) is int and loops >= 0,
                f"{target}: loop metadata must be a nonnegative integer, got {loops!r}")
        recursive_calls = item.get("recursive_calls")
        require(type(recursive_calls) is int and recursive_calls >= 0,
                f"{target}: self-call metadata must be a nonnegative integer, got {recursive_calls!r}")
        require(recursive_calls > 0 if target == "fib_L1" else recursive_calls == 0,
                f"{target}: unexpected recursive-call count {recursive_calls}")
        pattern = rf"\buint64_t\s+{c_name}\s*\(\s*uint64_t\s+input\s*\)\s*\{{"
        matches = list(re.finditer(pattern, remainder))
        require(len(matches) == 1, f"missing/duplicate generated definition of {c_name}")
        start = matches[0].end()
        depth, end = 1, start
        while depth and end < len(remainder):
            depth += (remainder[end] == "{") - (remainder[end] == "}")
            end += 1
        require(depth == 0, f"unbalanced definition of {c_name}")
        body = remainder[start:end - 1]
        arrays = re.findall(r"\buint64_t\s+\w+\s*\[\s*(\d+)\s*\]\s*;", body)
        if expected_cells:
            require(arrays == ["2"], f"{c_name}: expected one function-local two-cell array, got {arrays!r}")
        else:
            require("[" not in body, f"{c_name}: array-free L1 must not contain array storage/accesses")
        emitted_loops = len(re.findall(r"\b(?:for|while)\s*\(", body))
        require(loops == emitted_loops,
                f"{target}: loop metadata {loops} differs from {emitted_loops} emitted direct loops")
        emitted_self_calls = len(re.findall(rf"\b{re.escape(c_name)}\s*\(", body))
        require(recursive_calls == emitted_self_calls,
                f"{target}: self-call metadata {recursive_calls} differs from {emitted_self_calls} emitted self-calls")
        calls = set(re.findall(r"\b([A-Za-z_]\w*)\s*\(", body))
        allowed_calls = {"if", "for", "while", "switch", "return", "sizeof", "UINT64_C"}
        if recursive_calls > 0:
            allowed_calls.add(c_name)
        require(calls <= allowed_calls,
                f"{c_name}: unexpected runtime calls: {sorted(calls)}")
        remainder = remainder[:matches[0].start()] + remainder[end:]
    remainder = re.sub(r"^\s*#.*$", "", remainder, flags=re.MULTILINE).strip()
    require(not remainder, f"unexpected generated definitions outside the four entrypoints: {remainder!r}")


def write_generated(directory, generated, reuse=False):
    source, header, metadata = generated
    require(isinstance(source, str) and isinstance(header, str) and isinstance(metadata, dict),
            "generator API must return (C source, header, metadata)")
    directory.mkdir(parents=True, exist_ok=True)
    outputs = {"generated.c": source, "generated.h": header}
    for filename, text in outputs.items():
        path = directory / filename
        if reuse:
            require(path.is_file() and path.read_text(encoding="utf-8") == text,
                    f"{path} differs from fresh generator output; rerun make extract-c")
        else:
            path.write_text(text, encoding="utf-8")
    if reuse:
        require(read_document(directory / "lowering-metadata.json") == metadata,
                "production metadata differs from fresh generator output; rerun make extract-c")
    else:
        write_json(directory / "lowering-metadata.json", metadata)
    return source, header, metadata


def exact_reference():
    # Linear exact-integer recurrence, independent of every generator rule.
    values = []
    left, right = 0, 1
    for _ in range(SUPPORTED_RANGE[1] + 1):
        values.append(left)
        left, right = right, left + right
    for target, (inputs, expected) in ROCQ_SAMPLES.items():
        require(tuple(values[index] for index in inputs) == expected,
                f"independent reference disagrees with the known small Rocq examples for {target}")
    return values


def expected_fixture_rows():
    rows = []
    for value in range(92):
        swap = 21 if value % 2 == 0 else 12
        arithmetic = (value + 6) * 3 - value + value // 2
        sequencing = (value + 7) * 100 + value + 1
        chosen = value + 11 if value <= 4 else value * 3
        conditional = chosen + (100 if value == 0 else value - 1)
        initialized = value + 1 if value <= 4 else value * 2
        countdown = 7 + 3 * value
        rows.append([value, swap, arithmetic, sequencing, conditional, initialized, countdown])
    return rows


def check_rocq_comparison(output):
    """Check the separate known L1 subset and every actual execution marker."""
    lines = [line.strip() for line in output.splitlines()]
    blocks = (("INPUTS", SMALL_INPUTS), ("VALUES", SMALL_VALUES),
              ("L1 INPUTS", L1_SMALL_INPUTS), ("L1 VALUES", L1_SMALL_VALUES))
    markers = [f"C-CHECK ROCQ L{level} OK" for level in range(1, 5)]
    for label, _ in blocks:
        markers.extend((f"C-CHECK {label} BEGIN", f"C-CHECK {label} END"))
    for marker in markers:
        require(lines.count(marker) == 1, f"missing/duplicate Rocq comparison marker {marker!r}")
    for line in lines:
        require(not line.startswith("C-CHECK") or line in markers,
                f"malformed Rocq comparison marker {line!r}")
    for label, expected in blocks:
        begin = lines.index(f"C-CHECK {label} BEGIN")
        end = lines.index(f"C-CHECK {label} END")
        require(begin < end, f"out-of-order Rocq {label} list markers")
        body = "\n".join(lines[begin + 1:end]).strip()
        require(re.fullmatch(r"\[\s*[0-9]+(?:\s*;\s*[0-9]+)*\s*\]", body) is not None,
                f"malformed Rocq {label} decimal list: {body!r}")
        observed = tuple(int(value.strip()) for value in body[1:-1].split(";"))
        require(observed == expected,
                f"Rocq {label} list drift: got {observed}, expected {expected}")


def check_rows(label, output, expected):
    lines = output.splitlines()
    require(len(lines) == len(expected),
            f"{label}: expected {len(expected)} result rows, got {len(lines)}")
    rows = []
    for index, (line, wanted) in enumerate(zip(lines, expected)):
        require(re.fullmatch(r"[0-9]+(?: [0-9]+)*", line) is not None,
                f"{label}: malformed row {index}: {line!r}")
        row = [int(word) for word in line.split()]
        require(row == wanted, f"{label}: row {index}: got {row}, expected {wanted}")
        rows.append(row)
    return rows


def compile_and_run(commands, clang, directory, driver, label, expected, sanitized=False):
    binary = directory / label
    flags = SANITIZER_FLAGS if sanitized else ("-O2",)
    commands.run("compile-" + label, [
        *clang, *STRICT_FLAGS, *flags, "-I", directory,
        directory / "generated.c", ROOT / "tests/c" / driver, "-o", binary,
    ], empty_stderr=True)
    output = commands.run("execute-" + label, [binary],
                          SANITIZER_ENV if sanitized else None, empty_stderr=True)
    return check_rows(label, output, expected)


def run_checks(arguments, directory, commands):
    rocq = command_words(arguments.rocq, "--rocq")
    clang = command_words(arguments.clang, "--clang")
    for module in MODULES:
        source = ROOT / f"theories/{module}.v"
        compiled = source.with_suffix(".vo")
        require(compiled.is_file(), f"missing prerequisite {compiled}; run make all or make check-c first")
        require(compiled.stat().st_mtime_ns >= source.stat().st_mtime_ns,
                f"stale prerequisite {compiled}; run make all or make check-c first")
    require((ROOT / "scripts/extract_c.py").is_file(), "missing scripts/extract_c.py generator")
    versions = {
        "rocq": commands.run("rocq-version", [*rocq, "--version"]),
        "clang": commands.run("clang-version", [*clang, "--version"]),
    }
    require(re.search(r"version\s+9\.2(?:\D|$)", versions["rocq"]) is not None,
            "the extraction registry requires Rocq 9.2; see logs/rocq-version.stdout.txt")
    require("clang" in versions["clang"].lower(), "--clang must select Clang with sanitizer support")
    inputs = [ROOT / f"theories/{module}.{suffix}" for module in MODULES for suffix in ("v", "vo")]
    inputs += [ROOT / path for path in (
        "extraction/ExtractC.v", "tests/c/Fixtures.v", "tests/c/Compare.v",
        "tests/c/fib_driver.c", "tests/c/recursive_driver.c", "tests/c/fixture_driver.c", "tests/c/wrap_driver.c",
        "scripts/extract_c.py", "scripts/c_extraction_registry.json", "scripts/check_c.py",
    )]
    before = {str(path.relative_to(ROOT)): digest(path) for path in inputs}
    repl = [*rocq, "repl", "-q", "-batch", "-quiet", "-Q", "theories", "RefineToITree", "-l"]
    target_json = directory / "targets.json"
    if arguments.reuse_extraction:
        require(target_json.is_file(), "--reuse-extraction requires make extract-c first")
        extraction_inputs = [ROOT / "extraction/ExtractC.v"] + [
            ROOT / f"theories/{module}.{suffix}" for module in MODULES for suffix in ("v", "vo")
        ]
        require(target_json.stat().st_mtime_ns >= max(path.stat().st_mtime_ns for path in extraction_inputs),
                "production JSON predates extraction inputs; rerun make extract-c or omit --reuse-extraction")
    else:
        target_json.unlink(missing_ok=True)
        commands.run("extract-production", [*repl, "extraction/ExtractC.v"])
    (directory / "fixtures.json").unlink(missing_ok=True)
    commands.run("extract-fixtures", [*repl, "tests/c/Fixtures.v"])
    comparison = commands.run("rocq-comparison", [*repl, "tests/c/Compare.v"])
    check_rocq_comparison(comparison)
    production, fixtures = read_document(target_json), read_document(directory / "fixtures.json")
    check_extraction_identity(production, fixtures)

    # Import only at the generation boundary; direct --help also works before
    # the generator is installed.  Do not create a scripts/__pycache__ artifact.
    sys.dont_write_bytecode = True
    try:
        from extract_c import generate, Unsupported
    except ImportError as error:
        raise CheckError(f"cannot import scripts/extract_c.py: {error}") from error
    try:
        source, header, metadata = write_generated(
            directory, generate(production, list(ENTRYPOINTS), ENTRYPOINTS), arguments.reuse_extraction,
        )
        check_production_artifacts(source, header, metadata)
        _, _, fixture_metadata = write_generated(directory / "fixtures", generate(fixtures, list(FIXTURES)))
        write_generated(directory / "wrap", generate(fixtures, list(WRAP_FIXTURES)))
    except Unsupported as error:
        raise CheckError(f"generator rejected a supported source client: {error}") from error
    rejected = {}
    for name, diagnostic in REJECTIONS.items():
        try:
            generate(fixtures, [name])
        except Unsupported as error:
            require(re.search(diagnostic, str(error), re.IGNORECASE) is not None,
                    f"{name}: rejection did not identify its unsupported source construct: {error}")
            rejected[name] = str(error)
        else:
            raise CheckError(f"generator accepted unsupported source fixture {name}")

    reference = exact_reference()
    write_json(directory / "exact-reference.json", reference)
    expected_fib = [[value, result, result, result] for value, result in enumerate(reference)]
    l1_start, l1_end = NATIVE_RANGES["fib_L1"]
    expected_l1 = [[value, reference[value]] for value in range(l1_start, l1_end + 1)]
    expected_fixtures = expected_fixture_rows()
    for sanitized in (False, True):
        kind = "sanitized" if sanitized else "plain"
        compile_and_run(commands, clang, directory, "fib_driver.c", "fib-" + kind,
                        expected_fib, sanitized)
        compile_and_run(commands, clang, directory, "recursive_driver.c", "recursive-" + kind,
                        expected_l1, sanitized)
        compile_and_run(commands, clang, directory / "fixtures", "fixture_driver.c", "fixtures-" + kind,
                        expected_fixtures, sanitized)
    wrap_inputs = [0, 1, 2, 2**64 - 1]
    expected_wrap = [[value, (-value) % 2**64, (-value) % 2**64] for value in wrap_inputs]
    wrap_rows = compile_and_run(commands, clang, directory / "wrap", "wrap_driver.c", "wrap-plain", expected_wrap)
    changed = [str(path.relative_to(ROOT)) for path in inputs if digest(path) != before[str(path.relative_to(ROOT))]]
    require(not changed, f"source/compiled inputs changed during the gate; rerun it: {changed}")
    artifacts = (
        "targets.json", "fixtures.json", "generated.c", "generated.h", "lowering-metadata.json",
        "fixtures/generated.c", "fixtures/generated.h", "fixtures/lowering-metadata.json",
        "wrap/generated.c", "wrap/generated.h", "wrap/lowering-metadata.json",
    )
    return {
        "status": "passed", "assurance": "execution and artifact evidence; not an end-to-end correctness proof",
        "versions": versions, "commands": "commands.json", "supported_range_inclusive": SUPPORTED_RANGE,
        "entrypoints": ENTRYPOINTS, "caller_precondition": "input in 0..91; no runtime range guard",
        "production_extraction": "reused fresh make output" if arguments.reuse_extraction else "regenerated",
        "exact_comparisons_per_build": sum(end - start + 1 for start, end in NATIVE_RANGES.values()),
        "builds": ["plain", "sanitized"], "F91": reference[91],
        "native_coverage_per_root": {
            target: {"range_inclusive": bounds, "exact_comparisons_per_build": bounds[1] - bounds[0] + 1}
            for target, bounds in NATIVE_RANGES.items()
        },
        "rocq_coverage_per_root": {
            target: {"inputs": inputs, "expected_values": expected, "successful_observations": len(inputs),
                     "observation_fuel": 1000}
            for target, (inputs, expected) in ROCQ_SAMPLES.items()
        },
        "rocq_comparisons": sum(len(inputs) for inputs, _ in ROCQ_SAMPLES.values()),
        "target_metadata": metadata, "fixture_metadata": fixture_metadata,
        "native_fixtures": list(FIXTURES), "fixture_inputs_per_build": 92,
        "negative_fixtures_rejected": rejected,
        "unsigned_subtraction": {
            "mapping": "uint64_t subtraction modulo 2^64; differs from Nat.sub under underflow",
            "ordinary_only_fixtures": WRAP_FIXTURES, "rows_input_charged_pure": wrap_rows,
            "natural_zero_minus_one": 0, "native_zero_minus_one": 2**64 - 1,
            "deliberate_underflow_executed_under_sanitizers": False,
        },
        "strict_c_flags": STRICT_FLAGS, "sanitizer_flags": SANITIZER_FLAGS,
        "sanitizer_environment": SANITIZER_ENV, "sanitized_stderr_empty": True,
        "artifact_checks": ["four value-only public prototypes", "array-free L1; private two-cell arrays for L2/L3/L4",
                             "loop and self-call metadata match emitted control flow; no cross-calls or helpers",
                            "production AST/registry identity across extraction clients",
                            "no tree/event/cost/interpreter/closure/dynamic-allocation machinery",
                            "direct operations and standard-header-only runtime"],
        "inputs_sha256": before, "artifacts_sha256": {name: digest(directory / name) for name in artifacts},
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rocq", default="rocq", help="Rocq command (shell quoting/wrappers supported)")
    parser.add_argument("--clang", default="clang", help="Clang command (shell quoting/wrappers supported)")
    parser.add_argument("--build-dir", type=Path, default=Path("build/c"),
                        help="artifact directory; must resolve to this repository's build/c")
    parser.add_argument("--timeout", type=positive_timeout, default=120, metavar="SECONDS",
                        help="per-subprocess timeout (default: 120 seconds)")
    parser.add_argument("--reuse-extraction", action="store_true",
                        help="reuse fresh make extract-c output, checking JSON freshness and generator output identity")
    arguments = parser.parse_args(argv)
    directory = arguments.build_dir.expanduser()
    if not directory.is_absolute():
        directory = ROOT / directory
    directory = directory.resolve()
    report_path = None
    try:
        require(directory == (ROOT / "build/c").resolve(),
                "--build-dir must resolve to build/c, the tracked Rocq clients' output directory")
        directory.mkdir(parents=True, exist_ok=True)
        report_path = directory / "report.json"
        write_json(report_path, {"status": "running", "commands": "commands.json"})
        commands = Commands(directory, arguments.timeout)
        report = run_checks(arguments, directory, commands)
        write_json(report_path, report)
    except (CheckError, OSError, UnicodeError, ValueError, TypeError, KeyError) as error:
        if report_path is not None:
            try:
                write_json(report_path, {"status": "failed", "error": str(error), "commands": "commands.json"})
            except OSError:
                pass
        print(f"C acceptance failed: {error}", file=sys.stderr)
        return error.exit_code if isinstance(error, CheckError) else 1
    print("C acceptance passed: actual L1 on 0..30, L2/L3/L4 on 0..91, ordinary and sanitized;")
    print("307 exact native comparisons per build; Rocq execution: L1's 9 samples through 10, L2/L3/L4's 12 through 20.")
    print(f"{len(FIXTURES)} native fixtures, {len(REJECTIONS)} rejected source fixtures, ordinary-only unsigned underflow.")
    print(f"Evidence: {report_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
