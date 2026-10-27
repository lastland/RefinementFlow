# C extraction

The C backend translates the actual `Fib_L1`, `Fib_L2`, `Fib_L3`, and sequential
`Fib_L4` definitions constructed inside their `Derive` proofs. Rocq 9.2's built-in JSON extractor
preserves named operations; a shared Python generator lowers the extracted
functional syntax tree to C11. JSON is a build-time interface.

The [approved design](c-extraction-design-interview.md) defines the original L3/L4
milestone. The researcher's follow-up request extends extraction to L1/L2 and
compares native runtime across all four levels; see the
[runtime evaluation](c-runtime-evaluation.md).
The [research notes](c-extraction-research.md) preserve the feasibility evidence
and background. The backend is custom and unverified.

## Generate and use the C interface

From the repository root, with the pinned opam switch:

```sh
opam exec --switch=cs2-rocq92 -- make extract-c
clang -std=c11 -Wall -Wextra -Wpedantic -Werror -c build/c/generated.c \
  -o build/c/generated.o
```

Include `generated.h` and link `generated.c` with the calling program. The
exported interface is:

```c
uint64_t fib_l1(uint64_t input);
uint64_t fib_l2(uint64_t input);
uint64_t fib_l3(uint64_t input);
uint64_t fib_l4(uint64_t input);
```

The caller must supply **`input` in `0..91`, inclusive**. Neither function checks
this precondition. Each function returns only its Fibonacci result. L1 uses
native self-recursion without an array; L2, L3, and L4 own private two-cell arrays.
The generated program uses standard integer types, local arrays, arithmetic,
control flow, and direct calls. It needs the C standard library/system runtime,
with no additional runtime library. L1's exponential work makes large inputs
impractical despite the shared numeric precondition.

All generated files stay under ignored `build/c/`:

| Artifact | Purpose |
| --- | --- |
| `targets.json` | Rocq extraction of all four actual implementations and their dependencies |
| `generated.c`, `generated.h` | Standalone C and value-only interface |
| `lowering-metadata.json` | Generated entrypoint names, local-array capacities, loop/self-call counts, and lowered operations |
| `fixtures.json`, `fixtures/`, `wrap/` | Independent source fixtures and their generated/native artifacts |
| `report.json`, `commands.json`, `logs/` | Acceptance status, input/output hashes, exact commands, and captured output |
| `benchmark-all/` | Optional native timing samples, optimized assembly, binary, and reports |

`make clean` removes these artifacts. `ROCQ`, `PYTHON`, and `CLANG` can select the
build commands; Clang is required for the sanitizer acceptance gate.

## Supported source fragment

The interface accepts `nat -> itree (ArrayE nat +' TimeE) nat` and
`nat -> itree TimeE nat`. Clients use the same named helpers as the targets:

| Extracted construct | C lowering |
| --- | --- |
| Direct `Ret`, `ITree.bind` | Values and ordered statements |
| Fully applied local lambdas and continuations | Expanded during generation |
| Natural, boolean, unit, and nested product values | `uint64_t` scalars and flattened product coordinates; unit has no runtime payload |
| Exhaustive natural/boolean cases and product destructuring | Native branches and scalar bindings |
| `cost_iter`, returning `inl` to continue and `inr` to exit | Direct loop with simultaneous state updates and an exit value |
| `function_entry`, `cost_add`, `cost_mul`, `cost_sub` | Computational body or native arithmetic, with charges removed |
| `Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.div2`, `Nat.leb`, natural successor | Unsigned operators, division by two, and comparison |
| `array_alloc`, `array_read`, `array_set` | Function-local fixed array, direct loads, and direct stores |
| Restricted TimeE entrypoint self-recursion | Direct C self-calls on matched predecessors of the original input |

Bound expressions and reads are materialized before later effects. Loop updates
snapshot all coordinates before assigning any of them. Products, lambdas, and
loop-control sums are generation-time objects; the C contains no corresponding
runtime objects.

### Recursion restrictions

A recursive entrypoint must be a singleton, unary `TimeE` extraction fixgroup.
Each self-call must receive a strictly smaller predecessor obtained through one
or more successful natural-successor matches descended from the original input.
Immutable aliases and expanded local lambdas preserve that ancestry. Arithmetic,
recursive results, branch-result joins, and loop state/results forget it, so
computed or nondecreasing recursive arguments are rejected. Local closures that
contain or capture self-calls must be expanded and checked, including closures
whose results would otherwise be unused.

This rule covers L1 and independent countdown examples without a Fibonacci
template. Mutual recursion, recursive array clients, and calls to arbitrary
recursive helpers or other client entrypoints remain unsupported. The descent
analysis is conservative and is not a translation-correctness proof.

### Memory restrictions

A client may allocate at most one positive, literal-size array, outside every
branch and loop. Accesses require literal indices within its capacity. The
allocation's returned base is statically zero and may be used directly as an
index. Arithmetic expressions for indices and sizes are outside the fragment,
even if their operands are literals.

The generator checks definite initialization before every read. Branch joins
retain only cells initialized along both paths. Initialization gained inside a
loop is conservatively forgotten at its exit. These checks can reject safe
programs that require a stronger analysis. Generated accesses have no bounds
checks or initialization flags.

Raw trees other than direct returns, arbitrary effects, arbitrary recursive helpers,
unknown globals, dynamic memory patterns, partial applications, unsupported
values across control-flow joins, and unexpected extraction shapes stop
generation with a diagnostic. Unused local closures are also inspected for
unsupported source. The backend has no Fibonacci-specific algorithm or output
template.

## Extraction identities and maintenance

[`extraction/ExtractC.v`](../extraction/ExtractC.v) selects JSON output and keeps
the supported helpers named with `Extraction NoInline`.
[`scripts/extract_c.py`](../scripts/extract_c.py) checks exact JSON node schemas,
entrypoint types, symbol collisions, supported operations and arities, and the
direct array/time effect-injection dictionaries before lowering them.

JSON extraction renames symbols and erases some type information. The adjacent
[`c_extraction_registry.json`](../scripts/c_extraction_registry.json) records
reviewed Rocq identities, pinned package versions, and canonical declaration
hashes. Hashes cover entire owning declarations, including recursive groups or
inductive constructors, and the generator checks their dependency closure.
Client implementation bodies are not pinned: they must pass the reusable rules.

A changed helper, extraction flag, library version, or naming collision may
invalidate a pin. Inspect the original Rocq identity, type, body, dependencies,
renaming, and extractor output before updating the registry. Do not refresh hashes
automatically to make a rejected extraction pass. Pins detect shape changes; they
are not kernel provenance certificates or a proof of translation correctness.

The public Python boundary is:

```python
source, header, metadata = generate(document, targets, entrypoint_names=None)
```

`generate` raises `Unsupported` for source outside the fragment. It writes no
files. The command-line wrapper writes artifacts only after successful lowering:

```sh
python3 scripts/extract_c.py build/c/targets.json \
  fib_L3=fib_l3 fib_L4=fib_l4 fib_L1=fib_l1 fib_L2=fib_l2 --output-dir build/c
```

## Acceptance gate

```sh
opam exec --switch=cs2-rocq92 -- make check-c
opam exec --switch=cs2-rocq92 -- make check
```

`make check-c` regenerates production JSON and C, then:

1. Checks actual Rocq execution on `0, 1, 2, 3, 4, 5, 7, 8, 10` for L1, and
   `0, 1, 2, 3, 4, 5, 7, 8, 10, 15, 16, 20` for L2/L3/L4.
2. Compiles generated C11 with strict warnings treated as errors.
3. Compares L1 on every input `0..30` and L2/L3/L4 on every input `0..91`
   against a linear Python exact-integer Fibonacci reference, independent of the
   generated algorithms and generator rules. These are 307 comparisons per build;
   the smaller L1 execution range reflects its exponential work, not a different
   numeric policy.
4. Repeats execution with address, undefined-behavior, and unsigned-integer-overflow
   sanitizers. Any sanitizer diagnostic fails the gate.
5. Inspects the generated source and header for the required interface, private
   arrays, direct self-calls, and absence of tree, event, cost, interpreter,
   continuation, and dynamic-allocation machinery.
6. Runs independent source fixtures for simultaneous nested-product loop updates,
   arithmetic, sequencing around array effects, conditional results, branch
   initialization, and non-Fibonacci TimeE recursion. It rejects invalid initialization, bounds, dynamic accesses,
   unsupported allocation placement, raw trees/effects, and recursive helpers.
7. Runs deliberate unsigned-subtraction underflow separately in ordinary C.

`make check` also builds and replays the proofs, audits assumptions, and runs the
Python guardrail tests. The staged-snapshot commit hook invokes that same gate.
`scripts/check_c.py` regenerates extraction by default when run directly after
the theories have been built. Its `--reuse-extraction` mode checks freshness and
output identity for the immediately preceding `make extract-c`.

`make benchmark-c` runs an optional optimized wall-clock experiment after
regeneration. It times selected L1 inputs through `40` and all inputs `0..91`
for L2/L3/L4. The benchmark uses separately compiled targets, repeated shuffled
batches, consumed/checkable results, and a call-overhead baseline. It writes
measurements to `build/c/benchmark-all/`; no timing threshold affects `make check`.
See [Native runtime evaluation](c-runtime-evaluation.md) for the method and results.

## Numeric and assurance limits

Source naturals are unbounded. Generated data and scalar controls use
`uint64_t`; addition, multiplication, and subtraction wrap modulo `2^64`.
`Nat.sub` instead truncates at zero: natural `0 - 1` is `0`, whereas generated
unsigned `0 - 1` is `UINT64_MAX`. There is no general preservation of
natural-arithmetic semantics.

The shared `0..91` precondition accounts for intermediate computations, not
only the returned value. At input `92`, L3 computes an unused
`F(94) = 19740274219868223167`, which exceeds `UINT64_MAX`. The acceptance gate
checks all executed arithmetic in the supported Fibonacci range with unsigned
overflow instrumentation. It makes no mathematical-correctness claim outside
that range.

Execution checks support the tested executions and artifacts. Existing Rocq
correctness, termination, and resource theorems do not prove the generator or
its numeric mappings correct. Source costs count abstract operations and array
cells; they do not establish machine running time or byte-space guarantees for C.
