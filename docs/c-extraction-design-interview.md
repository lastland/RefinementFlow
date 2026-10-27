# C Extraction Design Interview

Status: **Design approved on 2026-10-28.** The researcher confirmed the
consolidated design after clarifying the extraction mechanism. Implementation
is integrated: a clean whole-project gate passed on 2026-10-28, including the
C acceptance checks. Independent standards and specification reviews are
complete. See [Implementation verification](#implementation-verification).
The subsequent [L1/L2 extension](#l1l2-extension-and-runtime-evaluation) adds all
four targets and their native runtime comparison at the researcher's request.

## Subject

Extract L3 and the approved sequential L4 to C. Eliminate ITree and cost-event
machinery from execution, and compile memory events to actual memory
operations. Existing libraries and extraction tools may be used.

The [research notes](c-extraction-research.md) cover the current source model
and relevant work by Adam Chlipala and collaborators.

## Confirmed requirements: round 1

On 2026-10-28, the researcher answered questions 1–3 as follows.

1. **Reusable compilation rules: yes.** Support the shared constructs used by
   L3 and sequential L4: sequencing, conditionals, `cost_iter`, arithmetic, and
   array operations. Generate C from the actual derived implementations,
   with these two programs as the first clients.
2. **Exact unbounded arithmetic: no, for now.** Record the resulting mismatch
   with mathematical-natural semantics as a limitation. The concrete number
   representation, supported input domain, and overflow behavior remain open.
3. **Checked refinement: no requirement for the first backend.** The researcher
   asked whether such a proof would require C semantics. A theorem about
   generated C requires semantics for the relevant C subset; existing projects
   provide semantics that could be reused. A proof about an intermediate
   imperative language alone would leave the C-printing connection to justify.

Round 1 settled these requirements; round 3 subsequently selected the extraction
route. The final confirmation below approves the consolidated design.

## Confirmed requirements: round 2

The researcher answered yes to questions 4–6.

4. **Unsigned 64-bit numbers.** Use `uint64_t`, with mathematical correctness
   expected only within a documented overflow-free input range. Current source
   arithmetic inspection gives the shared range `0..91`; these bounds still
   require checks on generated output. No mathematical-correctness claim
   applies beyond the supported range. The precise overflow and subtraction
   mappings remain open.
5. **Standalone C runtime.** Generated programs compile as ordinary C with
   runtime dependencies limited to the C standard library. Generation tools
   may have richer dependencies.
6. **Execution and artifact acceptance gate.** Compile generated C with strict
   warnings, run memory/undefined-behavior sanitizers, compare small inputs
   against Rocq execution and the supported numeric range against an independent
   exact-integer reference, and inspect output for elimination of ITree nodes,
   event dispatch, cost counters, and interpreter machinery. These checks are
   evidence for tested executions and artifacts, not a correctness proof.

## Confirmed requirements: round 3

The researcher accepted questions 7, 9, and 10 and declined the saturating
subtraction proposed in question 8.

7. **Built-in JSON extraction plus C generation.** Preserve the relevant named
   combinators in Rocq's extracted JSON and translate them using reusable
   C-generation rules. The researcher requested an explanation of JSON
   extraction: it is an existing output mode for the extractor's simplified
   functional syntax tree, used here as a build-time interface. JSON is not
   part of the generated program's runtime or input format.
8. **Ordinary unsigned arithmetic.** Saturating subtraction is unnecessary for
   this milestone. Use native unsigned C subtraction and document the
   difference from `Nat.sub`, alongside addition/multiplication overflow.
9. **Restricted static memory fragment.** Support one constant-size local
   allocation outside loops or branches, with statically known indices and
   initialization. Reject unsupported memory patterns during generation.
   Generated accesses need no runtime bounds checks or initialization flags.
10. **Value-only C interface.** Export `uint64_t fib_l3(uint64_t input)` and
    `uint64_t fib_l4(uint64_t input)`. Keep working arrays private. The common
    supported input range `0..91` is a documented caller precondition, with no
    runtime range guard.

## Confirmed requirements: round 4

The researcher answered yes to questions 11–13.

11. **Reject unsupported source.** Stop generation with a diagnostic for
    constructs outside the documented fragment, including unknown operations,
    arbitrary recursive helpers, unsupported effects, and unexpected extraction
    shapes. Use explicit supported-operation rules tied to the pinned Rocq
    version.
12. **Integrated verification.** `make check` regenerates the C and runs the
    agreed C checks alongside the proof checks. Also expose `make extract-c`
    and `make check-c`. The existing staged-snapshot hook thereby includes the
    C gate. The checking environment needs Clang and sanitizer support.
13. **Generated build artifacts.** Keep JSON, generated `.c`/`.h`, and binaries
    in an ignored build directory. Track the exporter, generator, and tests;
    regenerate output from the checked sources.

## Consolidated design

### Source and extraction boundary

Generate C from the actual `Fib_L3` and sequential `Fib_L4` definitions produced
inside their `Derive` proofs. Their shared executable signature is
`nat -> itree (ArrayE nat +' TimeE) nat`. Retain the existing source
construction discipline and algorithm-independent specifications.

Use Rocq 9.2's built-in JSON extraction with the relevant combinators kept
named. A shared Python C generator consumes the extracted functional syntax
tree. JSON is a build-time interchange format. The generator uses reusable
construct rules rather than Fibonacci-specific algorithms or output templates.

Registered operations and expected extraction shapes define the supported
fragment. Reject unknown constructs and unexpected representations with a
diagnostic. The JSON uses extraction-renamed symbols and erases some type
information, so registration and shape checks must account for that boundary.

### Translation rules

| Source structure | Generated representation |
| --- | --- |
| Return and `bind` | Values and statement sequencing |
| Local continuations | Expanded during generation |
| Conditionals and natural/boolean cases | Native C control flow |
| Scalar/product state | Scalars and flattened state coordinates |
| `cost_iter`, with `inl` continuation and `inr` exit | Direct loop with simultaneous state updates and an exit result |
| Function-entry and arithmetic cost wrappers | Computational body or primitive operation, with cost machinery removed |
| Supported allocation | Function-local fixed-size array |
| Array reads and writes | Direct indexed loads and stores |

The first fragment supports the named helpers used by the two targets, their
natural/boolean/unit/product values, and their loop-control sums. General raw
ITrees, arbitrary effects, recursive helpers, and dynamic memory patterns lie
outside this fragment. Generated execution contains no ITree nodes, event
dispatch, cost counters, interpreter machinery, or runtime continuation objects.

### Numbers, memory, and C interface

Use C11 and `uint64_t` for natural-number data and scalar controls. Addition,
multiplication, and subtraction use native unsigned operators; halving uses
integer division by two and comparisons use native comparisons. Document the
overflow and natural-subtraction limitations below.

The common supported Fibonacci input range is `0..91`, inclusive, as an
unguarded caller precondition. Export:

```c
uint64_t fib_l3(uint64_t input);
uint64_t fib_l4(uint64_t input);
```

Each function owns its working memory and returns only its result. The first
memory fragment permits one constant-size local allocation outside loops or
branches, literal indices, and statically checked initialization. For the
current targets this becomes a two-cell local array. Reject unsupported or
invalid memory patterns during generation; emit no runtime bounds checks or
initialization flags. Ordinary generated programs require only the C standard
library/system runtime.

### Build and acceptance

Track the extraction client, Python generator, and meaningful verification
fixtures. Generate JSON, C, headers, and binaries into an ignored build
directory. `make extract-c` performs generation after building the required
Rocq definitions; `make check-c` runs the C gate. `make check` includes that
gate together with the existing proof checks.

The C gate regenerates output, compiles with strict warnings, executes ordinary
and sanitized builds, compares small cases against Rocq execution and the
supported range against an independent exact-integer reference, and checks
the generated artifacts for removal of tree/event/cost/interpreter machinery.
The feasibility probe additionally exercised simultaneous loop-state updates,
rejection of invalid memory operations, and the deliberate unsigned-subtraction
mismatch. Use such independent fixtures to check reusable translation rules.

### Existing feasibility evidence

The [research notes](c-extraction-research.md#validated-built-in-json-extraction-route)
record an end-to-end probe of both actual compiled targets using this route.
After switching to the selected native subtraction mapping, both generated
targets matched the independent reference on every input `0..91` in ordinary
and sanitized builds. Address, undefined-behavior, and unsigned-overflow
instrumentation reported no errors in those Fibonacci executions. Deliberate
underflow demonstrations ran separately in ordinary C.

## Limitations to preserve

- The source programs use unbounded natural numbers. A fixed-width C
  representation can overflow in intermediate computations even when the
  returned Fibonacci number fits. For example, L3 computes both `F(93)` and
  `F(94)`; only the former fits in an unsigned 64-bit integer.
- `Nat.sub` truncates at zero, whereas unsigned C subtraction wraps modulo
  `2^64` on underflow. For example, natural `0 - 1` is zero, but unsigned
  64-bit `0 - 1` is `UINT64_MAX`. Source-level natural-arithmetic semantics do
  not carry over generally. The supported Fibonacci range must avoid both
  overflow and underflow in every executed arithmetic operation.
- Existing source-level correctness, termination, and resource theorems do not
  establish the correctness of a new C generator or of its numeric mappings.
- Execution checks provide evidence for tested cases, not an end-to-end
  correctness proof.
- Source cost bounds count abstract operations and array cells; they are not
  machine-running-time or byte-space guarantees for the extracted program.

## Final confirmation

The researcher gave final approval on **2026-10-28**, replying **“OK approved.”**

Before approving, the researcher asked which extraction mechanism and additional
framework were used. The clarification confirmed Rocq's standard extraction
plugin with JSON output, followed by a custom Python C backend. Rupicola and
Fiat informed the investigation but are not dependencies of the prototype. The
backend is custom and unverified, with the agreed execution-based acceptance
gate. This clarification is part of the approved shared understanding.

## Implementation verification

The integrated backend implements the approved route through
[`extraction/ExtractC.v`](../extraction/ExtractC.v),
[`scripts/extract_c.py`](../scripts/extract_c.py), and the
[`registered extraction identities`](../scripts/c_extraction_registry.json).
[`scripts/check_c.py`](../scripts/check_c.py) runs the acceptance checks;
[`tests/c/`](../tests/c/) and
[`tests/test_c_extraction.py`](../tests/test_c_extraction.py) exercise the reusable
translation rules. The [C extraction guide](c-extraction.md) documents commands,
supported constructs, memory restrictions, registry maintenance, and limitations.

On **2026-10-28**, the prepared `cs2-rocq92` switch and Clang **22.1.8** passed:

```sh
opam exec --switch=cs2-rocq92 -- make clean
opam exec --switch=cs2-rocq92 -- make -j2 check
opam exec --switch=cs2-rocq92 -- make check
```

| Check | Result |
| --- | --- |
| Clean proof build and executable replay | All nine theory modules compiled; examples and constructed terms replayed |
| Strict assumption audit | All 101 registered names closed under the global context |
| Python guardrail suite | All 71 tests passed, including 25 generator-boundary tests |
| Actual L3/L4 C execution | Both functions matched the independent exact-integer reference at every input `0..91`, ordinary and sanitized |
| Small Rocq comparisons | Both actual derived definitions matched the 12 known small cases |
| Sanitizers | Address, undefined-behavior, and unsigned-integer-overflow checks passed with empty execution stderr |
| Reusable translation fixtures | Five native fixtures passed across `0..91`; 14 unsupported source fixtures were rejected |
| Unsigned-subtraction mismatch | Charged and pure subtraction demonstrated native wrapping in separate ordinary-only executions |
| Artifact inspection | Value-only prototypes, private two-cell arrays, direct operations, and absence of runtime tree/event/cost/interpreter machinery passed |

The gate writes reproducible evidence to ignored `build/c/report.json`,
`build/c/commands.json`, and `build/c/logs/`. `make extract-c` and `make check-c`
are integrated; `make check` includes the C gate, so the staged-snapshot hook
includes it as well. These results provide execution and artifact evidence under
the stated numeric precondition, not an end-to-end correctness proof.

Independent standards and specification source reviews completed with **zero
remaining actionable findings** on both axes. Review refinements declared Clang
as an opam test dependency, refreshed current assurance metadata, added explicit
drift checks between Rocq and Python small-case lists, and checked loop metadata
against emitted loops rather than requiring a fixed loop count. The focused C
gate and final integrated `make check` passed after those refinements.

The review baseline was `432433ca8b4ce478b058eb6a1c565dd27a6bcf94`.
The main session separately checked the Git diff scope: no existing theory
implementation changed, and the registry's `Cost.v` and `Array.v` source-blob
identities match that baseline. The registered hashes pin shared library
declarations; the derived target bodies remain subject to the reusable rules.

## L1/L2 extension and runtime evaluation

On **2026-10-29**, after requesting runtime evidence for L3/L4, the researcher
asked: **“Also extract L1 and L2. Evaluate them compared with L3 and L4.”**
This follow-up extends the extraction scope. The original interview decisions
above remain the record of the first L3/L4 milestone.

The exporter now selects the actual `Fib_L1`, `Fib_L2`, `Fib_L3`, and `Fib_L4`
constants, preserving the existing extraction-name registrations. The backend
adds `nat -> itree TimeE nat` clients and a conservative rule for singleton,
unary TimeE entrypoint self-recursion on matched predecessors of the original
input. The rule emits direct C self-calls and checks their argument ancestry;
mutual recursion, recursive arrays, and arbitrary recursive helpers remain
unsupported. L2 uses the existing array/iteration rules. No target-specific
algorithm template or new registry pin is needed.

All four exports retain the common unguarded **`0..91`** numeric precondition.
L1 uses native recursion; L2/L3/L4 own two-cell arrays. L1's exponential work
limits practical execution checks and does not imply a smaller numeric policy.

The integrated command passed on 2026-10-29:

```sh
opam exec --switch=cs2-rocq92 -- make -j2 check
python3 scripts/benchmark_c.py --analyze-only
```

| Check | Result |
| --- | --- |
| Theory build and executable replay | Passed |
| Strict assumption audit | All 101 registered declarations closed |
| Python guardrail suite | All 85 tests passed, including 39 generator-boundary tests |
| Native exact-reference comparison | L1 at every input `0..30`; L2/L3/L4 at every input `0..91`; 307 comparisons per build |
| Sanitizers | The same native cases passed address, undefined-behavior, and unsigned-overflow instrumentation |
| Actual Rocq execution | Nine small L1 cases through `10`; twelve cases through `20` for each later level; 45 total observations |
| Reusable translation fixtures | Six native fixtures passed, including non-Fibonacci TimeE recursion; all 14 negative fixtures rejected |
| Optional native benchmark | 297 configurations, 11 shuffled rounds, 3,267 timed batches; all checksums and round orders verified |

[`scripts/benchmark_c.py`](../scripts/benchmark_c.py) and its tracked C driver
make the comparison reproducible through `make benchmark-c`. Timing is optional
and supplies no threshold to `make check`. The
[runtime evaluation](c-runtime-evaluation.md) records the method, measured values,
model fits, coverage, and limitations. It times selected L1 inputs through `40`
and every input `0..91` for L2/L3/L4. In that Clang 22.1.8/M1 Max run, L1 grew
approximately as `1.618^input`, L2 approximately linearly, and L3/L4 with input
bit length. L4 was about 17% slower than L3 by the median per-input time ratio,
despite its smaller abstract cost.

Independent standards and specification/correctness reviews of this extension
completed with **zero actionable findings on both axes**. Both covered the
staged change against `e0b07058acd4e3cc713dc567bca151476b4cf8ff` and accepted the
integrated gate. The correctness review also checked ancestry/closure rejection
cases, compared fresh lowering with the generated artifacts, and reanalyzed
the benchmark hashes, checksums, round orders, and model fits in memory.
