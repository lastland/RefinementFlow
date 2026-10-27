# Native runtime evaluation: L1–L4

On **2026-10-29**, the researcher asked to extract L1 and L2 as well as L3/L4,
then evaluate their runtime against the later levels. The C backend now exports
all four actual derived implementations. It lowers L1 to native self-recursion
and L2 to its countdown loop, using the same arithmetic and sequencing rules as
L3/L4. See the [extraction guide](c-extraction.md) for the supported source
fragment and numeric policy.

## Reproduce

```sh
opam exec --switch=cs2-rocq92 -- make check-c
opam exec --switch=cs2-rocq92 -- make benchmark-c
python3 scripts/benchmark_c.py --analyze-only
```

The benchmark is an optional experiment. `make check` runs correctness and
sanitizer checks, with no runtime threshold. Benchmark sources are tracked in
[`scripts/benchmark_c.py`](../scripts/benchmark_c.py),
[`tests/c/benchmark_driver.c`](../tests/c/benchmark_driver.c), and
[`tests/c/benchmark_identity.c`](../tests/c/benchmark_identity.c).

The benchmark writes `raw.csv`, `calibration.csv`, `report.json`, `report.md`,
optimized assembly, object files, and the executable under ignored
`build/c/benchmark-all/`. The JSON records commands, versions, source/artifact
hashes, the random seed, per-input distributions, fits, and measured comparison
bands. `--analyze-only` verifies those artifacts and regenerates the reports
without timing again.

## Measurement method

The recorded run used an **Apple M1 Max**, macOS **14.5**, and Clang **22.1.8**.
All four functions shared one C11 binary compiled with strict warnings,
`-O2 -fno-lto -fno-sanitize=all`. The generated targets, benchmark driver, and
identity baseline were separate translation units. Assembly and symbol checks
confirmed that the common timing loop retained the external target calls.

Each batch repeatedly called one function with a constant input. Returned
values fed an unsigned checksum consumed after timing. A separate linear Python
exact-integer reference checked every checksum, including warmup/calibration
batches. The experiment used:

- A monotonic raw clock with reported resolution **42 ns**.
- Calibration by doubling the call count until a batch took at least **12 ms**.
- **11 rounds** with independently shuffled configuration order in each round,
  using seed `0x20261029ba5e1a11`.
- One process/thread, with no competing benchmark process.
- One-call L1 warmups and initial calibration, avoiding repeated expensive
  recursion during setup. A single-call duration above one second caps larger
  L1 configurations; no cap was triggered in this run.
- An identity-function baseline measured through the same call loop.

L2/L3/L4 ran at every input `0..91`. L1 ran at:

```text
0, 1, 2, 3, 4, 5, 8, 10, 12, 15, 18, 20, 22, 25, 28, 30, 32, 35, 38, 40
```

The run checked **3,267 timed batches** and **3,846 warmup/calibration batches**.
All checksums, the consumed checksum sink, and the seeded round orders matched.
Actual timed batches ranged from **11.712 to 354.325 ms**; nine fell below the
calibration target during repetition. All samples were retained. Median
within-input p10–p90 widths were about **2%** for each target. The identity
baseline measured **0.973 ns/call** and was not subtracted.

Generated C SHA-256 for this run:

```text
5b493919324bcfa95d57bb27b587c636ab2ec7ccc3a1468706fbda7883b2fd63
```

## Observed runtime

These are raw medians per call. Times include call-loop and checksum overhead.
The report retains all eleven samples and their spread for every input.

| Input | L1 | L2 | L3 | L4 |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1.30 ns | 0.97 ns | 1.63 ns | 1.63 ns |
| 5 | 15.9 ns | 3.57 ns | 4.88 ns | 5.54 ns |
| 10 | 172 ns | 5.18 ns | 5.54 ns | 6.52 ns |
| 15 | 2.04 µs | 6.87 ns | 5.52 ns | 6.52 ns |
| 20 | 22.8 µs | 8.45 ns | 6.19 ns | 7.51 ns |
| 25 | 252 µs | 10.09 ns | 6.18 ns | 7.51 ns |
| 30 | 2.80 ms | 11.79 ns | 6.16 ns | 7.43 ns |
| 35 | 31.1 ms | 13.22 ns | 7.44 ns | 8.71 ns |
| 40 | 344 ms | 15.02 ns | 7.41 ns | 8.70 ns |
| 64 | Unmeasured | 22.75 ns | 9.08 ns | 10.46 ns |
| 91 | Unmeasured | 31.44 ns | 9.02 ns | 10.38 ns |

### Growth rates

L1's measured growth closely follows an exponential. On its eleven sampled
inputs from `15` through `40`, fitting `log2(time_ns) = a + b * input` gave
`b = 0.694451`, corresponding to a base of **1.618269** per increment of input.
This is close to `φ = 1.618034`; the descriptive fit had `R² = 0.999999`.

For the remaining levels, the following table compares two affine fits to
per-input median times over `1..91`:

| Target | `a + b * input`: R² | `a + b * bit_length(input)`: R² |
| --- | ---: | ---: |
| L2 | **0.9975** | 0.8200 |
| L3 | 0.8335 | **0.9651** |
| L4 | 0.8000 | **0.9796** |

L2 was approximately linear, with a fitted slope of **0.329 ns/input**.
L3/L4 followed input bit length, consistent with logarithmic growth over this
finite range. Here `bit_length(input) = floor(log2(input)) + 1` for positive
inputs.

### Relative performance

L2 won many small-input comparisons: its simple addition loop can cost less
than mask construction and fast doubling. In this run L3 had the smaller median
at every input `11..91`, although the timing spreads overlapped at `11`.
L4 had the smaller median than L2 at every input `18..91`. Smaller-input
comparisons were non-monotone, so these are observed bands, not universal
crossover thresholds. At `91`, L3 was about **3.49×** faster than L2; L4 was about
**3.03×** faster.

L4 was slower than L3 at **90 of 91** positive inputs. The median of per-input
L4/L3 median-time ratios was **1.174**, about **17% slower**. The near-tie at `1`
was within ordinary measurement variation. Clang's optimized assembly helps
explain the result: it computes both branch alternatives in L4 and selects their
results, leaving four multiply-family instructions per bit versus three in L3.
Fewer source ticks therefore did not imply faster native execution in this build.

## Correctness coverage and limits

The common unguarded numeric precondition remains **`0..91`** for all four
exports. This comparison did not execute L1 at `64` or `91`, and it does not
extrapolate their runtimes. The regular acceptance gate checks L1 on every input
`0..30` and L2/L3/L4 on every input `0..91`, in ordinary and sanitized builds.
It also checks actual Rocq executions on nine small L1 inputs through `10` and
twelve inputs through `20` for each later level. Benchmark checksum checks on
the listed L1 samples through `40` are additional unsanitized execution evidence.

These are warmed, constant-input measurements on one machine. Core placement,
frequency, thermal state, and background OS activity were uncontrolled. Input
bits, compiler decisions, and branch prediction can change timings. Positive
inputs span only seven bit lengths; finite samples do not prove asymptotic
complexity, translation correctness, or a portable speed ranking. Source
resource theorems count abstract ticks and array cells, rather than machine
running time or native stack bytes. L1's native recursion also uses call-stack
storage; its lack of an array is not a constant-space claim.
