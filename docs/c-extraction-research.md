# C Extraction Research

Research for the L3/L4 extraction design interview, begun on 2026-10-28.
These findings support the design interview. Round 3 selects the built-in JSON
route below. The isolated feasibility probe is preserved here as historical
evidence; the [implementation verification](c-extraction-design-interview.md#implementation-verification)
records the integrated backend and its passing acceptance gate.

## Project starting point

- L3 is constructed as an `itree (ArrayE nat +' TimeE) nat` inside
  `Derive`. Its executable body uses array allocation, reads and writes,
  charged arithmetic, and `cost_iter` loops. See
  [`FibonacciL3.v`](../theories/FibonacciL3.v).
- The [approved sequential L4 revision](level-4-design-interview.md#approved-sequential-l4-revision)
  replaces the historical parallel construction. Its implementation is in
  progress at the start of this interview. By the second round, the working-tree
  `Spec_L4` and target declaration use the same sequential array/time signature
  as L3. Extraction planning follows that approved sequential target.
- `ignore_time` and `run_ignore` preserve computational outcomes while ignoring
  ticks. The current assurance does not establish elimination of event or
  interpreter overhead. See [`Cost.v`](../theories/Cost.v),
  [`Array.v`](../theories/Array.v), and the
  [cost conventions](agents/cost-conventions.md#unit-ticks-and-interpretation).
- Array events describe indexed cells in a canonical `list (option A)` state.
  They are not currently C pointers. Allocation appends uninitialized cells;
  invalid or uninitialized accesses abort the interpretation. See
  [automatic array charges and semantics](agents/cost-conventions.md#automatic-array-charges).
- Arithmetic currently has mathematical-natural semantics, including
  truncating subtraction. Choosing a C number representation therefore needs
  a separate semantic decision. The existing resource model counts operations
  and array cells independently of the numbers' bit lengths.

## Adam Chlipala's extraction and compilation work

### Rupicola: relational compilation

The [PLDI 2022 paper's author page](https://adam.chlipala.net/papers/RupicolaPLDI22/)
describes extraction as proof search: extensible compilation rules derive
imperative code and correctness proofs from annotated functional models.
The compiler is intentionally incomplete, so domain-specific rules can control
the generated code.

The [project README](https://github.com/mit-plv/rupicola/blob/master/README.rst)
shows compilation to Bedrock2 and C output, including loops and memory loads.
It lists examples involving arrays, memory cells, nondeterminism, and IO. Its
C-generation example uses `ToCString.c_module` on the derived Bedrock2
functions. The README reports GNU/Linux development and testing and some
student use on macOS.

**Relevance:** reusable rules for the project's effect and iteration vocabulary
are worth investigating. The cited sources do not establish that this project's
existing ITree definitions are accepted directly, that all ITree and Tick
representation overhead disappears, or that the project builds with the current
Rocq 9.2 environment. Those are validation questions, not established features.

### Fiat's extensible imperative extraction

The [IJCAR 2020 paper's author page](https://adam.chlipala.net/papers/FiatIJCAR20/)
describes syntax-driven proof search that derives imperative programs from
nondeterministic functional programs. Extensible rules support manual memory
management and foreign functions. Its demonstrated pipeline runs within Coq
and produces linked assembly with functional-correctness proofs in separation
logic. The [Fiat repository](https://github.com/mit-plv/fiat) contains the
associated implementation.

**Relevance:** this work directly addresses effectful extraction and memory
representation. Its demonstrated source language and pipeline are not evidence
of a ready-made extractor for this project's ITrees.

### Bedrock2: imperative target and downstream compiler

The [Bedrock2 README](https://github.com/mit-plv/bedrock2/blob/master/README.md)
describes a C-like imperative language with 32- or 64-bit words and byte memory,
a program logic, and a verified compiler to RISC-V. It distinguishes that
compiler from the other components of the end-to-end system. It also excludes
function pointers and currently excludes recursive functions.

**Relevance:** the project's terminating loops and explicit array effects are
potentially compatible with this style of imperative target. Exact unbounded
natural arithmetic would require an additional representation and refinement
story. Availability of a verified RISC-V compiler does not by itself establish
correctness of a separate C-printing route.

## Interview decisions

The [design interview](c-extraction-design-interview.md) records the confirmed
scope and limitations. The first three rounds approve reusable compilation
rules over built-in JSON extraction, native unsigned 64-bit arithmetic, a
restricted static memory fragment, and value-only C functions with a `0..91`
caller precondition. Exact unbounded arithmetic and checked refinement are
deferred. Round 4 adds rejection of unsupported source, integrates C checks into
`make check`, and makes generated output untracked build artifacts. The
researcher approved the consolidated design on 2026-10-28 after confirming that
the route uses Rocq's standard extractor and a custom Python backend, without
an additional extraction framework.

## Fixed-width arithmetic inspection

An exact-integer Python calculation on 2026-10-28 checked the largest
arithmetic intermediates suggested by the current doubling bodies. For a
processed prefix `p`, L3 computes `F(2*p)`, `F(2*p+1)`, and `F(2*p+2)` even
when the last value is not selected. The sequential L4 computes only the
pair selected by the next bit.

For unsigned 64-bit arithmetic, this inspection places the overflow-free
input ranges at `0..91` for current L3 and `0..92` for current sequential L4.
In particular, L3 at input `92` computes the unused intermediate
`F(94) = 19740274219868223167`, exceeding `2^64 - 1`, although both retained
values fit. These are source-inspection and arithmetic-check findings, not
machine-checked bounds or validation of a C translation. A selected numeric
policy still needs execution checks on the generated programs.

## Validated built-in JSON extraction route

An isolated throwaway probe on 2026-10-28 successfully generated direct C from
both actual compiled targets, including the sequential `Fib_L4`. The probe used
Rocq 9.2's built-in extraction rather than parsing printed Gallina:

```coq
Extraction Language JSON.
Extraction NoInline ITree.bind function_entry cost_iter
  cost_add cost_mul cost_sub array_alloc array_read array_set
  Nat.add Nat.mul Nat.sub Nat.div2 Nat.leb.
Extraction "targets.json" Fib_L3 Fib_L4.
```

### What JSON extraction means

Rocq extraction first produces a simplified functional program representation,
called MiniML in the extractor's implementation. Its JSON backend serializes
that representation as nodes for applications, lambdas, cases, constructors,
and declarations. JSON is the build-time interface between Rocq extraction and
the C generator; it is not a generated-program runtime dependency.

This architecture is visible in the installed Rocq 9.2 extraction sources:
`miniml.ml:11` identifies the core language; `json.ml:93–127` serializes
applications and globals; and `extract_env.ml:514–518` selects the JSON printer.
The sources are installed under
`/Users/liyao/.opam/cs2-rocq92/lib/rocq-runtime/plugins/extraction/`.

The JSON preserves named combinator applications, local continuations,
conditionals, products, and loop-control sums. A shared Python lowering expands
the continuations during generation, lowers `cost_iter` to direct loops, and
replaces array operations with loads and stores. It contains no Fibonacci
algorithm or target-specific output templates. Each generated target has two
loops and one local `uint64_t cells[2]` array, with no runtime ITree, events,
interpreter, cost counters, closures, or dynamic allocation.

### Evidence

- Both actual targets passed strict C11 compilation with warnings treated as
  errors.
- Rocq evaluation checked 12 small inputs per target. Both generated targets
  matched an independent Python exact-integer Fibonacci reference on every
  input `0..91`, in ordinary and sanitized builds.
- Address, undefined-behavior, and unsigned-overflow instrumentation passed
  those executions with empty sanitizer stderr.
- Independent fixtures checked simultaneous loop-state updates. Invalid reads
  and an unsupported raw-tree fixture were rejected during generation.
- The initial probe used saturating subtraction. After the researcher declined
  that mapping, the probe switched to native unsigned subtraction and reran
  the Fibonacci gate successfully, retaining unsigned-overflow instrumentation.
  Deliberate-underflow fixtures ran separately in ordinary C and demonstrated
  the documented mismatch with natural subtraction.
- The ordinary executable linked only the platform system runtime. Repository
  source and compiled-input hashes were unchanged during the probe.

The sources, generated C, complete commands, hashes, and results are retained at:

```text
/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/json-c-feasibility-20261028.FLtFsM/
```

Run its complete gate with `python3 <probe-directory>/verify.py`; `EVIDENCE.md`
explains the commands and validation boundary.

### Scope and remaining production questions

This probe supports the existing targets' named ITree/cost helpers, scalar and
product values, natural/boolean cases, and one positive constant-size allocation
outside branches or loops. Array indices are literal and reads require static
definite initialization. Addition, multiplication, and subtraction use native
unsigned arithmetic. Overflow and underflow can wrap outside the supported
domain, including the deliberate mismatch with `Nat.sub`'s truncation at zero.
The range is a caller precondition in the prototype. Current generated
entrypoints are `fib_l3` and `fib_l4`; the earlier saturating experiment is
preserved separately in the probe directory.

The JSON is extracted MiniML, not a canonical kernel AST: it uses
extraction-renamed identifiers and erases some type information. Production
registration must guard against name collisions or unexpected extraction
shapes. The probe checks the recognized effect-injection dictionaries before
erasing them. It does not establish general support for arbitrary effects,
raw trees, recursion, dynamic memory operations, or failure outcomes.

This is end-to-end feasibility evidence for the selected narrow route, not a
translation-correctness proof. The interview records the approved integration
and artifact-tracking requirements. Its later
[implementation verification](c-extraction-design-interview.md#implementation-verification)
records the completed integration; the [C extraction guide](c-extraction.md)
describes the current backend.
