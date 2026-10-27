#!/usr/bin/env python3
"""Build and measure the four actual generated Fibonacci targets (Python 3.9+).

Run make extract-c first. This optional, unsanitized experiment writes only to
build/c/benchmark-all; it does not run the correctness/sanitizer acceptance gate.
The constant-input batches include indirect-call, loop, and checksum overhead.
"""

import argparse
import csv
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import statistics
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "build/c/benchmark-all"
TARGETS = ("fib_l1", "fib_l2", "fib_l3", "fib_l4")
L1_INPUTS = (0, 1, 2, 3, 4, 5, 8, 10, 12, 15, 18, 20, 22, 25, 28, 30, 32, 35, 38, 40)
CONFIGURATIONS = [("fib_l1", n) for n in L1_INPUTS]
CONFIGURATIONS += [(target, n) for target in TARGETS[1:] for n in range(92)]
CONFIGURATIONS += [("identity", 17)]
SOURCES = ("build/c/generated.c", "build/c/generated.h", "scripts/benchmark_c.py",
           "tests/c/benchmark_driver.c", "tests/c/benchmark_identity.c")
SEED = 0x20261029BA5E1A11
REPEATS = 11
MIN_BATCH_NS = 12_000_000
L1_CAP_NS = 1_000_000_000
MASK = (1 << 64) - 1
FLAGS = ("-std=c11", "-Wall", "-Wextra", "-Wpedantic", "-Werror", "-Wconversion",
         "-Wshadow", "-Wstrict-prototypes", "-Wmissing-prototypes", "-Wformat=2",
         "-Wundef", "-Wcast-qual", "-Wwrite-strings", "-Wvla", "-O2", "-fno-lto",
         "-fno-sanitize=all", "-I", "build/c")
LINK_FLAGS = ("-O2", "-fno-lto", "-fno-sanitize=all")


class BenchmarkError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise BenchmarkError(message)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n", encoding="utf-8")


def hashes(paths):
    return {str(path): hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            for path in paths}


def relative(path):
    return str(path.relative_to(ROOT))


class Commands:
    def __init__(self, journal, timeout):
        self.journal = journal
        self.timeout = timeout

    def run(self, argv, required=True):
        argv = [str(word) for word in argv]
        started = time.monotonic()
        record = {"argv": argv, "shell": shlex.join(argv), "cwd": str(ROOT)}
        try:
            result = subprocess.run(argv, cwd=ROOT, text=True, encoding="utf-8",
                                    errors="replace", capture_output=True,
                                    timeout=self.timeout)
            record.update(returncode=result.returncode, stdout=result.stdout, stderr=result.stderr)
        except (OSError, subprocess.TimeoutExpired) as error:
            record.update(returncode=None, stdout="", stderr=str(error))
        record["elapsed_seconds"] = time.monotonic() - started
        self.journal.append(record)
        write_json(OUTPUT / "commands.json", self.journal)
        require(not required or record["returncode"] == 0,
                f"command failed: {record['shell']}\n{record['stderr']}\n"
                f"See {relative(OUTPUT / 'commands.json')}")
        return record["stdout"]


def environment(commands, clang):
    compiler = commands.run([*clang, "--version"]).strip()
    require("clang" in compiler.lower(), "--clang must select Clang")
    result = {"compiler": compiler, "python": sys.version, "platform": platform.platform(),
              "uname": dict(platform.uname()._asdict()), "logical_cpus": os.cpu_count(),
              "cpu": platform.processor() or "unknown"}
    if sys.platform == "darwin":
        result["cpu"] = commands.run(["sysctl", "-n", "machdep.cpu.brand_string"]).strip()
        result["hardware"] = commands.run([
            "sysctl", "hw.model", "hw.ncpu", "hw.physicalcpu", "hw.logicalcpu", "hw.memsize"])
        result["os_version"] = commands.run(["sw_vers"])
        result["power"] = commands.run(["pmset", "-g", "batt"], required=False)
    elif sys.platform.startswith("linux"):
        cpuinfo = Path("/proc/cpuinfo")
        if cpuinfo.is_file():
            for line in cpuinfo.read_text(encoding="utf-8").splitlines():
                name, separator, value = line.partition(":")
                if separator and name.strip() in ("model name", "Hardware"):
                    result["cpu"] = value.strip()
                    break
        if shutil.which("lscpu"):
            result["hardware"] = commands.run(["lscpu"], required=False)
    return result


def check_interface():
    require(all((ROOT / source).is_file() for source in SOURCES),
            "Missing benchmark/generated source; run make extract-c first.")
    header = (ROOT / "build/c/generated.h").read_text(encoding="utf-8")
    header = re.sub(r"/\*.*?\*/|//[^\n]*", "", header, flags=re.DOTALL)
    missing = [target for target in TARGETS if not re.search(
        rf"\buint64_t\s+{target}\s*\(\s*uint64_t(?:\s+\w+)?\s*\)\s*;", header)]
    require(not missing, "Generated API is not ready (missing " + ", ".join(missing)
            + "); run make extract-c after the four-level compiler update.")


def nm_symbols(text, definitions=False):
    return {words[-1].lstrip("_") for line in text.splitlines()
            if (words := line.split())
            and (not definitions or (len(words) >= 2 and words[-2] in ("T", "t")))}


def build(commands, clang):
    objects = []
    for source, name in ((SOURCES[0], "generated"), (SOURCES[3], "driver"),
                         (SOURCES[4], "identity")):
        output = OUTPUT / (name + ".o")
        commands.run([*clang, *FLAGS, "-c", source, "-o", output])
        objects.append(output)
    executable = OUTPUT / "run"
    commands.run([*clang, *LINK_FLAGS, *objects, "-o", executable])
    assembly_path = OUTPUT / "driver.s"
    commands.run([*clang, *FLAGS, "-S", SOURCES[3], "-o", assembly_path])
    commands.run([*clang, *FLAGS, "-S", SOURCES[0], "-o", OUTPUT / "generated.s"])
    nm = shutil.which("nm")
    require(nm is not None, "nm is required to inspect retained external target calls")
    undefined = commands.run([nm, "-u", OUTPUT / "driver.o"])
    linked = commands.run([nm, "-g", executable])
    (OUTPUT / "driver.undefined.txt").write_text(undefined, encoding="utf-8")
    (OUTPUT / "run.symbols.txt").write_text(linked, encoding="utf-8")
    symbols = set(TARGETS) | {"benchmark_identity"}
    require(symbols <= nm_symbols(undefined), "driver lost an external target reference")
    require(symbols <= nm_symbols(linked, definitions=True), "linked binary lost a target")
    assembly = assembly_path.read_text(encoding="utf-8")
    start = re.search(r"^_?benchmark_batch:.*$", assembly, re.MULTILINE)
    require(start is not None, "cannot locate benchmark_batch in emitted assembly")
    body = assembly[start.start():]
    end = re.search(r"^\s*\.cfi_endproc|^\s*\.size\s+_?benchmark_batch\b|^\.?Lfunc_end\d+:",
                    body, re.MULTILINE)
    require(end is not None, "cannot locate end of benchmark_batch assembly")
    body = body[:end.end()]
    # Clang's native arm64 and x86 assembly, including AT&T and Intel call syntax.
    indirect = re.findall(
        r"^\s*(?:blr\s+x\d+\b|call[qwl]?\s+(?:\*[^\n]+|"
        r"(?:r\d+|[re](?:ax|bx|cx|dx|si|di|bp|sp))\b[^\n]*|"
        r"(?:(?:qword|dword)\s+ptr\s+)?\[[^\n]+))", body, re.MULTILINE)
    require(len(indirect) == 1, "expected one retained indirect call in the common batch loop")
    require(re.search(r"\b(?:bl|call[qwl]?)\s+_?benchmark_batch\b", assembly) is not None,
            "common benchmark batch is not called")
    return {"assembly": relative(assembly_path), "target_assembly": relative(OUTPUT / "generated.s"),
            "undefined_symbols": undefined,
            "linked_target_symbols": sorted(symbols), "batch_assembly": body,
            "indirect_calls_in_batch": [line.strip() for line in indirect],
            "note": "Three separate translation units; -O2 -fno-lto at compile/link; "
                    "no sanitizer instrumentation; only the common batch boundary is noinline."}


def reference(n):
    """Independent linear, exact-integer Fibonacci; no generated/doubling code."""
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def read_checked(path, calibration=False):
    fields = ["target", "input", "round", "iterations", "elapsed_ns", "checksum"]
    with path.open(newline="", encoding="utf-8") as source:
        reader = csv.DictReader(source)
        require(reader.fieldnames == fields + (["phase"] if calibration else []),
                f"unexpected CSV header in {path}")
        rows = list(reader)
    for row in rows:
        for key in fields[1:]:
            row[key] = int(row[key])
        key = (row["target"], row["input"])
        require(key in CONFIGURATIONS, f"unexpected configuration in {path}: {key}")
        # Tiny probes can fall within one clock tick; retain them, then double.
        # Final calibration and all actual repeated samples must be positive.
        require(0 < row["iterations"] <= MASK
                and row["elapsed_ns"] >= (0 if calibration else 1),
                f"nonpositive/invalid batch in {path}: {row}")
        expected = row["input"] if key[0] == "identity" else reference(key[1])
        require(row["checksum"] == (row["iterations"] * expected) & MASK,
                f"independent Fibonacci checksum mismatch in {path}: {row}")
    return rows


def shuffled_rounds(configurations, seed):
    state = seed
    for _ in range(REPEATS):
        order = list(configurations)
        for i in range(len(order) - 1, 0, -1):
            state ^= state >> 12
            state ^= (state << 25) & MASK
            state ^= state >> 27
            j = ((state * 2685821657736338717) & MASK) % (i + 1)
            order[i], order[j] = order[j], order[i]
        yield order


def spread(values):
    values = sorted(values)
    require(len(values) == REPEATS, "incomplete repeated samples")
    # Eleven samples: the second/tenth order statistics are p10/p90.
    return {"median_ns": statistics.median(values), "p10_ns": values[1],
            "p90_ns": values[-2], "min_ns": values[0], "max_ns": values[-1]}


def affine_fit(xs, ys):
    xmean, ymean = statistics.mean(xs), statistics.mean(ys)
    slope = math.fsum((x - xmean) * (y - ymean) for x, y in zip(xs, ys))
    slope /= math.fsum((x - xmean) ** 2 for x in xs)
    intercept = ymean - slope * xmean
    residual = math.fsum((y - intercept - slope * x) ** 2 for x, y in zip(xs, ys))
    total = math.fsum((y - ymean) ** 2 for y in ys)
    return {"intercept": intercept, "slope": slope,
            "r_squared": 1 - residual / total if total else 1.0,
            "rmse": math.sqrt(residual / len(xs)), "n_observations": len(xs)}


def bands(values):
    result = []
    for n, label in values:
        if result and result[-1]["label"] == label and result[-1]["input_max"] == n - 1:
            result[-1]["input_max"] = n
        else:
            result.append({"input_min": n, "input_max": n, "label": label})
    return result


def analyze(report):
    samples = read_checked(OUTPUT / "raw.csv")
    calibration = read_checked(OUTPUT / "calibration.csv", calibration=True)
    metadata = report["run_metadata"]
    seed = int(metadata["seed"], 0)
    require(seed == report["design"]["seed"], "driver seed differs from requested seed")
    require(int(metadata["repeats"]) == REPEATS, "driver repeats differ from analysis")
    require(metadata["clock"] in ("CLOCK_MONOTONIC_RAW", "CLOCK_MONOTONIC")
            and int(metadata["clock_resolution_ns"]) > 0, "invalid benchmark clock metadata")
    cap = metadata["l1_first_skipped_input"]
    cap = None if cap == "none" else int(cap)
    require(cap is None or cap in L1_INPUTS, "invalid L1 cap input")
    skipped = [n for n in L1_INPUTS if cap is not None and n >= cap]
    active = [key for key in CONFIGURATIONS if key[0] != "fib_l1" or key[1] not in skipped]
    require(int(metadata["configuration_count"]) == len(active), "configuration count mismatch")
    require(len(samples) == len(active) * REPEATS, "missing/extra repeated batches")

    calibration_by_key = {}
    for row in calibration:
        require(row["round"] == -1, "invalid calibration round")
        calibration_by_key.setdefault((row["target"], row["input"]), []).append(row)
    expected_calibration = set(active) | ({("fib_l1", cap)} if cap is not None else set())
    require(set(calibration_by_key) == expected_calibration, "missing/extra calibration configurations")
    final = {}
    for key, rows in calibration_by_key.items():
        l1 = key[0] == "fib_l1"
        require(rows[0]["phase"] == "warmup" and rows[0]["iterations"] == (1 if l1 else 10000),
                f"wrong warmup for {key}")
        iterations = 1 if l1 else 1024
        for row in rows[1:]:
            require(row["phase"] == "calibration" and row["iterations"] == iterations,
                    f"wrong calibration doubling sequence for {key}")
            iterations *= 2
        if key == ("fib_l1", cap):
            require(rows[-1]["iterations"] == 1 and rows[-1]["elapsed_ns"] > L1_CAP_NS
                    and rows[-1]["phase"] == metadata["l1_cap_phase"]
                    and rows[-1]["elapsed_ns"] == int(metadata["l1_cap_elapsed_ns"]),
                    "L1 cap lacks the recorded >1s single-call probe")
        else:
            require(len(rows) >= 2 and rows[-1]["elapsed_ns"] >= MIN_BATCH_NS,
                    f"unfinished calibration for {key}")
            require(all(row["elapsed_ns"] < MIN_BATCH_NS for row in rows[1:-1]),
                    f"calibration continued past its threshold for {key}")
            final[key] = rows[-1]

    for round_number, expected_order in enumerate(shuffled_rounds(active, seed)):
        rows = samples[round_number * len(active):(round_number + 1) * len(active)]
        require(all(row["round"] == round_number for row in rows)
                and [(row["target"], row["input"]) for row in rows] == expected_order,
                f"incomplete or incorrectly shuffled round {round_number}")
    sink = 0
    for row in calibration + samples:
        sink ^= row["checksum"]
    require(sink == int(metadata["checksum_sink"]), "consumed checksum sink does not match batches")
    per_configuration = {}
    for key in active:
        rows = [row for row in samples if (row["target"], row["input"]) == key]
        iterations = final[key]["iterations"]
        require(all(row["iterations"] == iterations for row in rows),
                f"sample iterations differ from calibration for {key}")
        per_configuration[key] = {"target": key[0], "input": key[1], "iterations": iterations,
                                  **spread([row["elapsed_ns"] / iterations for row in rows])}

    models = {}
    l1_fit_inputs = [n for n in L1_INPUTS if n >= 15 and ("fib_l1", n) in per_configuration]
    l1_fit = None
    if len(l1_fit_inputs) >= 2:
        l1_fit = affine_fit(l1_fit_inputs, [math.log2(per_configuration["fib_l1", n]["median_ns"])
                                          for n in l1_fit_inputs])
        l1_fit.update(inputs=l1_fit_inputs, exponential_base=2 ** l1_fit["slope"],
                      phi=(1 + math.sqrt(5)) / 2)
    models["fib_l1_log2_ns_a_plus_b_n"] = l1_fit
    for target in TARGETS[1:]:
        models[target] = {}
        for minimum in ((1, 16) if target == "fib_l2" else (1,)):
            inputs = list(range(minimum, 92))
            ys = [per_configuration[target, n]["median_ns"] for n in inputs]
            models[target][f"n_{minimum}_to_91"] = {
                "a_plus_b_n": affine_fit(inputs, ys),
                "a_plus_b_bit_length": affine_fit([n.bit_length() for n in inputs], ys)}

    crossovers = {}
    for target in TARGETS[2:]:
        winners, separated = [], []
        for n in range(92):
            l2, other = per_configuration["fib_l2", n], per_configuration[target, n]
            winner = ("fib_l2" if l2["median_ns"] < other["median_ns"] else target
                      if other["median_ns"] < l2["median_ns"] else "equal")
            winners.append((n, winner))
            separated.append((n, "fib_l2" if l2["p90_ns"] < other["p10_ns"] else target
                              if other["p90_ns"] < l2["p10_ns"] else "overlap"))
        crossovers[target] = {"median_winner_bands": bands(winners),
                              "nonoverlapping_p10_p90_bands": bands(separated)}
    ratios = [per_configuration["fib_l4", n]["median_ns"]
              / per_configuration["fib_l3", n]["median_ns"] for n in range(1, 92)]
    noise = {}
    for target in (*TARGETS, "identity"):
        rows = [row for row in per_configuration.values() if row["target"] == target]
        if not rows:
            continue
        widths = [(row["max_ns"] - row["min_ns"]) / row["median_ns"] for row in rows]
        noise[target] = {
            "median_relative_min_max_width": statistics.median(widths),
            "largest_relative_min_max_width": max(widths),
            "median_relative_p10_p90_width": statistics.median(
                (row["p90_ns"] - row["p10_ns"]) / row["median_ns"] for row in rows)}
    report.update(
        verification={"method": "Independent Python linear exact-integer F(n); "
                      "checksum = iterations * result modulo 2^64, including warmup/calibration",
                      "all_checksums_and_sink_match": True, "all_seeded_round_orders_match": True,
                      "raw_batches_checked": len(samples), "calibration_batches_checked": len(calibration),
                      "zero_elapsed_probe_batches": sum(row["elapsed_ns"] == 0 for row in calibration),
                      "minimum_measured_batch_ns": min(row["elapsed_ns"] for row in samples),
                      "maximum_measured_batch_ns": max(row["elapsed_ns"] for row in samples),
                      "measured_batches_below_calibration_threshold": sum(
                          row["elapsed_ns"] < MIN_BATCH_NS for row in samples)},
        l1_skipped_inputs=skipped, samples=samples, calibration=calibration,
        per_configuration=list(per_configuration.values()), models=models,
        l2_crossovers=crossovers, within_input_noise=noise,
        l4_over_l3={"input_min": 1, "input_max": 91, "median": statistics.median(ratios),
                    "min": min(ratios), "max": max(ratios),
                    "l4_faster_inputs": sum(ratio < 1 for ratio in ratios)})
    return per_configuration


def format_bands(items):
    return "; ".join(f"{row['input_min']}–{row['input_max']}: {row['label']}" for row in items)


def markdown(report, configurations):
    baseline = configurations["identity", 17]
    design, metadata = report["design"], report["run_metadata"]
    lines = ["# Four-level generated C benchmark", "",
             f"CPU: {report['environment']['cpu']}. Platform: {report['environment']['platform']}.",
             f"Compiler: {report['environment']['compiler'].splitlines()[0]}.",
             "Build: C11, strict warnings, `-O2 -fno-lto -fno-sanitize=all`; three separate translation units.",
             f"Clock: {metadata['clock']}, resolution {metadata['clock_resolution_ns']} ns. "
             f"Seed: `0x{design['seed']:016x}`. Eleven shuffled rounds, one process/thread.",
             f"Calibrated batches ≥12 ms; L1 warmup/initial calibration: 1/1 call; others: 10000/1024 calls.",
             "All checksums, the consumed sink, and seeded round orders verified. No outlier removal.", "",
             "## Runtime", "", "Raw median ns/call; identity overhead is not subtracted.",
             "All configurations have p10/p90 and min/max in `report.json`; individual batches are in `raw.csv`.",
             f"Identity(17): {baseline['median_ns']:.3f} ns; p10–p90 "
             f"[{baseline['p10_ns']:.3f}, {baseline['p90_ns']:.3f}]; min–max "
             f"[{baseline['min_ns']:.3f}, {baseline['max_ns']:.3f}].", "",
             "| n | L1 | L2 | L3 | L4 | L4/L3 |", "|---:|---:|---:|---:|---:|---:|"]
    for n in (1, 5, 10, 15, 20, 25, 30, 35, 40, 64, 91):
        cells = [f"{configurations[target, n]['median_ns']:,.3f}"
                 if (target, n) in configurations else "unmeasured" for target in TARGETS]
        ratio = configurations["fib_l4", n]["median_ns"] / configurations["fib_l3", n]["median_ns"]
        lines.append(f"| {n} | " + " | ".join(cells) + f" | {ratio:.3f} |")
    lines += ["", f"L1 requested samples: `{', '.join(map(str, L1_INPUTS))}`."]
    if report["l1_skipped_inputs"]:
        lines.append(f"L1 single-call probe at n={metadata['l1_first_skipped_input']} took "
                     f"{int(metadata['l1_cap_elapsed_ns']) / 1e9:.3f} s during {metadata['l1_cap_phase']}. "
                     f"Repeated timing was capped; skipped inputs: {report['l1_skipped_inputs']}.")
    else:
        lines.append("All requested L1 samples completed; no L1 input above 40 was timed.")
    lines += ["", "## Descriptive fits", "",
              "Unweighted per-input medians; affine model is y = a + b·x. These are finite-range fits."]
    l1 = report["models"]["fib_l1_log2_ns_a_plus_b_n"]
    if l1 is not None:
        lines += [f"L1, sampled n≥15 ({l1['n_observations']} points): "
                  f"log2(time_ns) = {l1['intercept']:.6f} + {l1['slope']:.6f}·n; "
                  f"R²={l1['r_squared']:.6f}, RMSE={l1['rmse']:.6f} log2(ns).",
                  f"Fitted exponential base: **{l1['exponential_base']:.6f}**, versus φ={l1['phi']:.6f}."]
    else:
        lines.append("L1 fit unavailable: fewer than two measured samples at n≥15.")
    lines += ["", "| Target | n range | x | a (ns) | b (ns/unit) | R² | RMSE (ns) |",
              "|---|---|---|---:|---:|---:|---:|"]
    for target in TARGETS[1:]:
        for scope, fits in report["models"][target].items():
            for name, fit in fits.items():
                lines.append(f"| {target} | {scope[2:].replace('_to_', '–')} | {name[9:]} | "
                             f"{fit['intercept']:.6f} | {fit['slope']:.6f} | "
                             f"{fit['r_squared']:.6f} | {fit['rmse']:.6f} |")
    lines += ["", "The additional n≥16 L2 fits help inspect small-input compiler unrolling effects;",
              "`generated.s` retains the target assembly for that interpretation.",
              "Positive inputs 1..91 span only seven bit lengths.", "", "## Measured comparisons", "",
              "Bands name the smaller measured median on **0..91**, not an exact or universal crossover.",
              "The second line uses nonoverlapping p10/p90 ranges; overlap is not a significance test."]
    for target, values in report["l2_crossovers"].items():
        lines += [f"- L2 vs {target}: {format_bands(values['median_winner_bands'])}.",
                  f"  p10/p90 separation: {format_bands(values['nonoverlapping_p10_p90_bands'])}."]
    ratio = report["l4_over_l3"]
    lines += [f"- L4/L3 on 1..91: median of per-input median ratios **{ratio['median']:.3f}**, "
              f"range [{ratio['min']:.3f}, {ratio['max']:.3f}]; "
              f"L4 faster at {ratio['l4_faster_inputs']}/91 inputs.", "", "## Observed batch noise", "",
              "Widths below are divided by the per-input median; all eleven samples are retained.", "",
              "| Target | Median p10–p90 width | Median min–max width | Largest min–max width |",
              "|---|---:|---:|---:|"]
    for target, noise in report["within_input_noise"].items():
        lines.append(f"| {target} | {noise['median_relative_p10_p90_width']:.1%} | "
                     f"{noise['median_relative_min_max_width']:.1%} | "
                     f"{noise['largest_relative_min_max_width']:.1%} |")
    verified = report["verification"]
    lines += ["", f"Checked {verified['raw_batches_checked']} timed batches and "
              f"{verified['calibration_batches_checked']} warmup/calibration batches. "
              f"Timed batch range: {verified['minimum_measured_batch_ns'] / 1e6:.3f}–"
              f"{verified['maximum_measured_batch_ns'] / 1e6:.3f} ms; "
              f"{verified['measured_batches_below_calibration_threshold']} fell below 12 ms after calibration.",
              f"Retained {verified['zero_elapsed_probe_batches']} zero-duration probes below clock resolution; "
              "all repeated timed samples have positive elapsed time.",
              "", "## Reproduction and limits", "", "```sh", report["invocation"],
              "python3 scripts/benchmark_c.py --analyze-only", "```", "",
              f"Generated C SHA-256: `{report['source_sha256_after']['build/c/generated.c']}`.",
              "Source/header/tool hashes stayed identical before and after the run. Exact commands,",
              "compiler/CPU/platform metadata, assembly evidence, hashes, and samples are in `report.json`.",
              "Calibration/probes are in `calibration.csv`; object code and the binary are retained here.", "",
              "The approved numeric domain is uint64 natural values at inputs 0..91. L1 has only the",
              "listed finite samples; larger L1 times are neither measured nor extrapolated. All four",
              "actual generated targets share one optimized binary and the same indirect-call loop.",
              "Calls, checksum additions, loop control, and clock overhead are included. Constant input",
              "within each warmed batch favors branch prediction. Core placement, frequency, thermal",
              "state, and background OS activity are uncontrolled; this run cannot prove asymptotics",
              "or equate Rocq's abstract resource costs with native running time.", ""]
    (OUTPUT / "report.md").write_text("\n".join(lines), encoding="utf-8")


def seed_argument(text):
    try:
        value = int(text, 0)
    except ValueError as error:
        raise argparse.ArgumentTypeError("seed must be a nonzero uint64 integer") from error
    if not 0 < value <= MASK:
        raise argparse.ArgumentTypeError("seed must be a nonzero uint64 integer")
    return value


def timeout_argument(text):
    try:
        value = float(text)
    except ValueError as error:
        raise argparse.ArgumentTypeError("timeout must be positive and finite") from error
    if not math.isfinite(value) or value <= 0:
        raise argparse.ArgumentTypeError("timeout must be positive and finite")
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clang", default=os.environ.get("CLANG", "clang"),
                        help="Clang command, split with shlex (default: CLANG or clang)")
    parser.add_argument("--seed", type=seed_argument, default=SEED)
    parser.add_argument("--timeout", type=timeout_argument, default=240,
                        help="per-command timeout in seconds (default: 240)")
    parser.add_argument("--analyze-only", action="store_true", help="verify/rebuild reports without timing")
    args = parser.parse_args()
    report = None
    try:
        if args.analyze_only:
            report = json.loads((OUTPUT / "report.json").read_text(encoding="utf-8"))
            require(report.get("status") == "complete", "previous run did not complete")
            require(hashes(SOURCES) == report["source_sha256_after"], "benchmark inputs changed since run")
            require(hashes(report["artifact_sha256"]) == report["artifact_sha256"],
                    "benchmark artifacts changed since run")
        else:
            check_interface()
            clang = shlex.split(args.clang)
            require(clang and shutil.which(clang[0]), "--clang command is empty or unavailable")
            OUTPUT.mkdir(parents=True, exist_ok=True)
            report = {"status": "running", "started_utc": datetime.datetime.now(
                datetime.timezone.utc).isoformat(), "working_directory": str(ROOT),
                "invocation": shlex.join(["python3", "scripts/benchmark_c.py", "--clang", args.clang,
                                          "--seed", hex(args.seed), "--timeout", str(args.timeout)]),
                "source_sha256_before": hashes(SOURCES), "commands": [],
                "design": {"seed": args.seed, "repeats": REPEATS, "rng": "xorshift64*",
                           "shuffle": "Fisher-Yates, modulo remaining count",
                           "requested_configurations": [list(key) for key in CONFIGURATIONS],
                           "l1_inputs": list(L1_INPUTS), "fast_inputs": [0, 91],
                           "minimum_calibration_batch_ns": MIN_BATCH_NS,
                           "l1_single_call_cap_ns": L1_CAP_NS,
                           "warmup_calls": {"fib_l1": 1, "others": 10000},
                           "initial_calibration_iterations": {"fib_l1": 1, "others": 1024},
                           "calibration_growth": 2, "threads": 1, "benchmark_processes": 1,
                           "constant_input_within_batch": True, "baseline_subtracted": False,
                           "outliers_removed": False, "p10_p90_method": "second/tenth of eleven sorted samples",
                           "compile_flags": list(FLAGS), "link_flags": list(LINK_FLAGS)}}
            write_json(OUTPUT / "report.json", report)
            commands = Commands(report["commands"], args.timeout)
            report["environment"] = environment(commands, clang)
            report["assembly_evidence"] = build(commands, clang)
            print("Timing 297 requested configurations in one process (usually about 60–75 seconds).",
                  flush=True)
            stdout = commands.run([OUTPUT / "run", OUTPUT / "raw.csv", OUTPUT / "calibration.csv",
                                   hex(args.seed)])
            (OUTPUT / "run.stdout.txt").write_text(stdout, encoding="utf-8")
            report["run_metadata"] = dict(line.split("=", 1) for line in stdout.splitlines())
            report["source_sha256_after"] = hashes(SOURCES)
            require(report["source_sha256_before"] == report["source_sha256_after"],
                    "benchmark/generated inputs changed while compiling or timing; discard this run")
            report["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        configurations = analyze(report)
        markdown(report, configurations)
        artifacts = [relative(OUTPUT / name) for name in (
            "raw.csv", "calibration.csv", "driver.s", "generated.s", "driver.undefined.txt", "run.symbols.txt",
            "run.stdout.txt", "generated.o", "driver.o", "identity.o", "run", "report.md", "commands.json")]
        report["artifact_sha256"] = hashes(artifacts)
        report["status"] = "complete"
        write_json(OUTPUT / "report.json", report)
        print(f"Report: {relative(OUTPUT / 'report.md')}; raw samples: {relative(OUTPUT / 'raw.csv')}")
    except (BenchmarkError, OSError, ValueError, KeyError, TypeError) as error:
        if report is not None and not args.analyze_only:
            report.update(status="failed", error=str(error))
            write_json(OUTPUT / "report.json", report)
        print(f"benchmark-c: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
