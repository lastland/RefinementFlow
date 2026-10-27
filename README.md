# RefineToITree

A Rocq experiment in **specification-driven program construction**, with an
implemented chain of Fibonacci programs:

- **Level 0:** the pure reference `Fib_L0`.
- **Level 1:** `Fib_L1`, derived with naive recursion and an exponential cost bound.
- **Level 2:** `Fib_L2`, derived relative to L1 with a two-cell mutable array,
  iteration, and linear time and space upper bounds.
- **Level 3:** `Fib_L3`, derived relative to L2 with iterative fast doubling,
  logarithmic time and constant array-space upper bounds.
- **Level 4:** `Fib_L4`, derived relative to L3 with sequential, bit-specific fast
  doubling and the same array-storage discipline. Its affine logarithmic cost
  bound has a leading coefficient strictly below `13`; the implementation saves
  exactly one tick per input bit over L3 on every positive input.

Rocq checks the contracts under canonical interpretations. **Sequential L4 source
verification, before the C backend:** the replacement passed a **clean integrated
`make check`**: all **nine**
modules compiled, actual L3/L4 examples and cost comparisons replayed, all **101**
audited declarations were closed under the global context, and all **46** guardrail
tests passed. Independent sequential standards and specification/proof reviews
are **complete**: standards found **zero documented violations and zero actionable
heuristic findings**; specification/proof review found **zero findings**.
The earlier parallel L4 and its shared-proof extraction remain verified historical
baselines, with **97/45** and **104/45** closed audit reports/passing guardrail
tests respectively. Those results do not verify the replacement. See
[L4 verification status](#l4-verification-status).

The **C backend** implements the [approved extraction design](docs/c-extraction-design-interview.md)
and the researcher's follow-up request to extract L1/L2. The integrated gate passed
with all **101** audit entries closed and all **85** Python tests passing.
Ordinary and sanitized C matched exact Fibonacci values on **`0..30` for L1**
and **`0..91` for L2/L3/L4**, giving **307 comparisons per build**. See
[four-level extraction verification](docs/c-extraction-design-interview.md#l1l2-extension-and-runtime-evaluation)
and the [native runtime evaluation](docs/c-runtime-evaluation.md). Independent
standards and specification/correctness reviews found **zero actionable findings**.

## Build and replay checks

The tested environment is OCaml **5.4.1** in the prepared opam switch
`cs2-rocq92`. [refine-to-itree.opam](refine-to-itree.opam) fixes these versions:

| Package | Version |
| --- | --- |
| `rocq-core` | `9.2.0` |
| `rocq-stdlib` | `9.2.0` |
| `coq-itree` | `5.2.1` |
| `coq-paco` | `4.2.3` |
| `coq-ext-lib` | `0.13.2` |

Verification also requires Python **3.9+**, Git, and **Clang with address,
undefined-behavior, and unsigned-integer-overflow sanitizer support**. Ordinary
generated programs require only a C11 compiler and the C standard library/system
runtime. From the repository root, use the prepared switch:

```sh
opam exec --switch=cs2-rocq92 -- make check
make install-hooks
```

For a fresh named switch, install opam 2.1+ and Make first; run `opam init --bare`
if opam is not initialized. Then, from the repository root:

```sh
opam switch create refine-to-itree ocaml-base-compiler.5.4.1 \
  --repositories=rocq-released=https://rocq-prover.org/opam/released,default
opam install --switch=refine-to-itree --deps-only --with-test .
opam exec --switch=refine-to-itree -- make check
make install-hooks
```

The prepared switch resolves `coq-itree`, `coq-paco`, `coq-ext-lib`, and
`rocq-stdlib` through the [Rocq released repository](https://rocq-prover.org/docs/using-opam),
and `rocq-core` through `default`. The fresh-switch recipe fixes the compiler and
proof-library versions, but is not a full transitive lock. **The fresh-switch recipe
has not been executed**; the tested environment is the prepared switch.

| Command | Check |
| --- | --- |
| `make check` | Build, executable examples, strict assumption audit, guardrail regression tests, and C acceptance gate |
| `make examples` | Build and replay `theories/Examples.v`, even when compilation is up to date |
| `make assumptions` | Build and require every registered theorem's assumptions report to be closed |
| `make guard-tests` | Run the Python guardrail tests, including real Rocq and Git fixtures |
| `make extract-c` | Regenerate L1–L4 JSON and standalone C from the actual derived definitions |
| `make check-c` | Regenerate C, compile strictly, compare results, run sanitizers, and check supported/rejected source fixtures |
| `make benchmark-c` | Run the optional optimized native runtime comparison of all four levels |
| `make install-hooks` | Install the local pre-commit launcher |

`make clean` removes generated Rocq artifacts and `build/c`. `opam test` uses the
same `make check` gate; its test dependencies include `conf-python-3` and
`conf-clang`. `ROCQ`, `PYTHON`, and `CLANG` select the corresponding commands.

### Continuous integration

The `CI` workflow in [.github/workflows/ci.yml](.github/workflows/ci.yml) runs
the full `make check` gate on pushes to `main`, all pull requests, and manual
runs. It uses Ubuntu 24.04, OCaml 5.4.1, the pinned proof dependencies from
[refine-to-itree.opam](refine-to-itree.opam), Python 3, and Clang 18. The
workflow uses `setup-ocaml`'s built-in compiler cache and rebuilds the project
proofs and generated C outputs on each run. The check command uses
`opam exec --set-switch` so nested hook checks retain the selected switch in
temporary repositories. On failure, it uploads available C-gate reports,
command records, and logs in the `c-check-evidence` artifact for seven days.
The first Ubuntu run installed the pinned dependencies and passed the proof
build, examples, and assumption audit; the full hosted gate still awaits
verification.

### Standalone C extraction

`make extract-c` runs Rocq 9.2's built-in JSON extractor, then the shared Python
backend. It produces ignored `build/c/generated.c` and `build/c/generated.h`:

```c
uint64_t fib_l1(uint64_t input);
uint64_t fib_l2(uint64_t input);
uint64_t fib_l3(uint64_t input);
uint64_t fib_l4(uint64_t input);
```

All four functions have the unguarded caller precondition **`0 <= input <= 91`**.
They return only the value. L1 uses native self-recursion; L2–L4 keep their
two-cell arrays local and execute direct loops, arithmetic, loads, and stores.
JSON, ITree nodes, event dispatch, continuations, and cost counters are absent
from execution. The C acceptance gate executes L1 through `30` and L2–L4
through `91`; large L1 inputs are computationally impractical.

Native unsigned addition, multiplication, and subtraction wrap modulo `2^64`.
In particular, subtraction differs from `Nat.sub` on underflow. The supported
Fibonacci range avoids these failures in tested intermediate operations; values
outside that range have no mathematical-correctness claim. The backend is custom
and unverified. The C gate supplies execution and artifact evidence, rather than
an end-to-end correctness proof or a machine-time/resource guarantee.

See [C extraction](docs/c-extraction.md) for the supported fragment, registry
maintenance, build commands, and verification evidence. The
[approved design](docs/c-extraction-design-interview.md) records the decisions.
The [native runtime evaluation](docs/c-runtime-evaluation.md) compares all four
generated levels: L1's timings grow exponentially, L2's grow approximately
linearly, and L3/L4 follow input bit length over the tested range. L4's lower
abstract cost does not make it faster than L3 in the measured Clang build.

### Strict assumption audit

[checks/assumptions.txt](checks/assumptions.txt) is the single list of audited
theorems. Add one Rocq name per line when extending that audit. Blank lines and
`#` comments are supported; empty lists, malformed names, and duplicates fail.

`make assumptions` uses [scripts/check_assumptions.py](scripts/check_assumptions.py)
to generate a marker-delimited Rocq report for each name. Every report must say
exactly **“Closed under the global context.”** Axiom dependencies, missing or
truncated reports, unexpected output, Rocq errors, and timeouts all fail the
command. The expected reports come from the manifest, rather than a fixed count.

The script imports `RefineToITree.FibonacciL4` and `RefineToITree.Parallel`
independently by default: current L4 no longer imports the parallel library.
Explicit `--module` arguments replace both defaults and may be repeated. The
sequential revision replaces only obsolete parallel-L4-specific audit entries;
every shared-library entry remains in the manifest.

### Local commit guard

`make install-hooks` installs an executable launcher in Git's default local hook
directory. The launcher calls the versioned [.githooks/pre-commit](.githooks/pre-commit),
so later hook changes travel with the repository. Installation is idempotent and
preserves existing custom hooks and configured hook frameworks.

Before a commit, the hook exports the **staged index** into a temporary directory
and runs `opam exec -- make check` there. An unstaged fix cannot mask a broken
staged change. The checks leave the working tree and index intact and remove
their temporary build artifacts. Success produces a short summary; failure
returns a nonzero status and the captured check output.

The hook resolves the active/local opam switch in the real repository before
checking the snapshot. Use the intended switch when committing. Each clone needs
`make install-hooks` once.

## Shared effects and charging

The [project-wide cost conventions](docs/agents/cost-conventions.md) apply to all
four derived levels and future examples. `Cost.v` replaces the former writer-style
`CostM` interface with a singleton effect:

```coq
Variant TimeE : Type -> Type := Tick : TimeE unit.
Definition tick : itree TimeE unit := trigger Tick.
```

Raw programs return values only. `count program` owns a private counter, starts
at zero, and adds exactly one per tick. It returns a closed
`itree void1 (nat * Result)` with **cost first**. Time events carry no numeric payload.

- `function_entry`: one tick per target-function invocation, including base cases.
- `cost_iter`: one tick per `ITree.iter` body invocation, including terminal exit.
- `cost_add`: one tick per addition of `nat` data values.
- `cost_mul`: one tick per multiplication of `nat` data values.
- `cost_sub`: one tick per truncated subtraction of `nat` data values.

The policy charges each primitive data-arithmetic operation once. The iteration
tick covers loop-control comparisons, index maintenance (including index-only
halving and mask updates), and branching. Preprocessing scans, such as binary-mask
construction, must remain explicit charged computation. The body callback receives
no second entry tick merely for being a Gallina function; helpers implementing
primitives or interpreters also incur no duplicate charges.

`Array.v` defines polymorphic `ArrayE A` with `ArrayAlloc`, `ArrayRead`, and
`ArraySet`. Its canonical state is `array_state A = list (option A)`:

| Operation | Result and state behavior | Automatic ticks |
| --- | --- | --- |
| `array_alloc size` | Append `size` `None` cells; return the old length as the base index | `size + 1` |
| `array_read index` | Return a stored value of type `A`; invalid or uninitialized reads fail | `1` per attempt |
| `array_set index value` | Store `Some value`, return `tt : unit`; invalid indices fail | `1` per attempt |

Failure aborts with canonical `None` and skips the continuation; failed attempts
still cost one tick. Allocation emits one operation tick plus one per new cell,
including one tick for `array_alloc 0`. These are actual unit events, not weighted
charges. There is no deallocation; reads and sets preserve array length.

`run_count program` starts with an empty array and zero cost. Its result type is
`itree void1 (nat * option (array_state A * Result))`: cost first, then either
failure or the final array and value. Space counts cells, including uninitialized
cells, rather than bits. Costs are abstract operations, not machine running time.

`ignore_time` supplies `tt` for ticks; `run_ignore` applies it after array
interpretation. `count_ignore_result` and `arrays_count_ignore_result` prove
preservation of computational outcomes, including failures, after discarding
cost. **Ignoring ticks does not establish full runtime overhead erasure.**

`Cost.v` also owns four generic laws moved from `Parallel.v`:
`interp_leaf_source` recovers a source leaf from an interpreted leaf, and
`interp_state_leaf_source` does the same after discarding the interpreter's state.
`count_offset` relates executions from different initial counters;
`count_shift_leaf` shifts a zero-based counted leaf to an arbitrary starting
counter without changing its value. The move adds no imports or dependencies to
`Cost.v`.

### Countdown-loop invariant rule

`Array.v` provides `run_count_cost_iter_nat_invariant` for `cost_iter` loops that
count down in `nat`, with arbitrary cell type `A` and result type `R`. The caller
supplies an invariant indexed by the remaining iterations and array state,
constant `step_cost` and `exit_cost`, and a fixed `final_array` and `result`.
The rule requires two body proofs, for every applicable array and starting cost:

- **Continue:** From `invariant (S remaining) array`, the body reaches a successful
  leaf at `cost + step_cost`, returns `inl remaining`, and leaves some `array'`
  satisfying `invariant remaining array'`.
- **Exit:** From `invariant 0 array`, the body reaches a successful leaf at
  `cost + exit_cost`, returns `inr result`, and leaves `final_array`.

Both body obligations use `run_count_from` starting at `S cost`:
**`step_cost` and `exit_cost` each include the iteration-entry tick.** From
`invariant remaining array`, the theorem gives a successful `Leaf` for
`run_count_from (cost_iter body remaining) array cost`, with outcome
`Some (final_array, result)` and exact total cost
`cost + step_cost * remaining + exit_cost`.

Initialization and program sequencing use the existing `function_entry`,
`array_alloc`, `array_set`, and bind laws.

### Loops with a proof-only remaining rank

`run_count_cost_iter_rank_invariant` separates the number of continuing iterations
left, a proof-only `nat` rank, from an arbitrary runtime `State`. Its invariant has
type `nat -> State -> array_state A -> Prop`:

- **Continue:** At rank `S remaining`, the body returns `inl state'` and leaves an
  array satisfying the invariant at rank `remaining` and runtime state `state'`.
- **Exit:** At rank zero, the body returns `inr result` and leaves `final_array`.

The obligations establish the same fixed `step_cost` and `exit_cost` as above,
including the iteration-entry tick. The rule gives exact total cost
`cost + step_cost * remaining + exit_cost` and the successful final array and
result, without adding a countdown to the runtime state. L3's
`fib_l3_doubling_count` and L4's `fib_l4_doubling_count` use this rule while their
loops carry only the remaining input and mask; persistent Fibonacci pairs stay
in their arrays.

For sequential, array-free `TimeE` loops, `Cost.v` provides
`count_cost_iter_step` and `count_cost_iter_rank_invariant`. The latter takes an
invariant of type `nat -> State -> Prop` and proves the exact cost
`cost + step_cost * remaining + exit_cost`. Its body obligations also start at
`S cost`, so both cost constants include the iteration-entry tick. This remains a
shared library rule, independent of current L4; the rank is proof data, not runtime
state.

### Initialization and space-bound rules

`run_count_init_pair_bind` proves the common two-cell initialization prefix:
allocate two cells, store `first` at index `0`, and store `second` at index `1`.
Starting from an empty array, this prefix costs five ticks and gives the
continuation `[Some first; Some second]`. The rule supports arbitrary cell and
result types and preserves successful or failed continuation outcomes.
`function_entry` supplies its separate entry tick.

`final_bound_subtree_leaf` derives bounds on canonical residual arrays from a
successful counted leaf and a bound on its final array length.
`final_bound_handler_subtree_leaf` also covers pending handler prefixes. A
successful leaf of the closed counted tree supplies termination and determines
the final outcome, so callers need no separate termination premise. Both rules
reuse the shared monotonicity theorems.

### Binary-control proof rules

`Binary.v` owns the level-neutral control arithmetic. Alongside `div2_bounds`,
`log2_div2`, and `binary_prefix_step`, `binary_prefix_rank_step` packages mask
positivity, mask halving, and preservation of the processed-prefix invariant,
including the last-bit transition to rank zero. L3's and L4's array-loop proofs
both use this rule; Fibonacci-specific data invariants and arithmetic remain in
their respective modules.

The same module defines two **proof-only witnesses** for the charged mask scan:

| Input | `binary_mask input` | `mask_scan_cost input` |
| --- | --- | --- |
| `0` | `0` | `1` |
| Positive | `2 ^ Nat.log2 input` | `Nat.log2 input + 1` |

`mask_body_rule` describes a loop body that halves a quotient and doubles a scalar
mask until the quotient is `0` or `1`. Given that body rule, `mask_count_all` covers
every input, arbitrary scale and starting counter, and an arbitrary array of any
cell type. It proves that `cost_iter` returns `scale * binary_mask input`, leaves
the array unchanged, and adds exactly `mask_scan_cost input` ticks.

The existing `mask_count` and `mask_zero` rules remain available for positive and
zero inputs respectively; `mask_zero` needs only the body's zero-case equation.
L3 and L4 use the all-input rule but still construct their executable mask scans
inside `Derive`. Neither target calls the proof-only witnesses to compute a mask
or cost.

### Parallel effects and interpretations

`Parallel.v` is an **independent shared library**, originally developed for the
superseded parallel L4. Its generic fixtures and audited proofs remain current;
the sequential `FibonacciL4.v` neither imports it nor has parallel obligations.

`Parallel.v` adds shallow fork/join: each child is a sequential `TimeE`
computation, so it can neither access the parent's array nor fork another child.
The result types of the two children may differ.

```coq
Record Prices := { fork_cost : nat; join_cost : nat }.
Variant ForkEvent : Type -> Type :=
| Fork {A B} : itree TimeE A -> itree TimeE B -> ForkEvent (A * B).
Definition ParallelE (A : Type) := ArrayE A +' (ForkEvent +' TimeE).
```

| Interface | Purpose |
| --- | --- |
| `fork left right` | Emit a fork event and return the pair of child results at join |
| `lift_serial program` | Embed an existing `ArrayE A +' TimeE` computation in `ParallelE A` |
| `run_parent_from program array` | Apply canonical array handling and automatic array ticks, leaving fork and time events |
| `run_parallel_from prices program array (work, span)` | Interpret from a supplied array and pair of resource counters |
| `run_parallel prices program` | Start from an empty array and zero counters; return `((work, span), outcome)` |
| `serialization program` | Produce an `ArrayE A +' TimeE` program that executes the same children sequentially, without coordination charges |

Here `span` is parallel time, and `outcome` is `None` on array failure or
`Some (array, result)` on success. Ordinary parent ticks and automatic array ticks
add one to both counters. For child costs `wl` and `wr`, the fork handler adds:

```text
work: fork_cost + wl + wr + join_cost
span: fork_cost + max(wl, wr) + join_cost
```

The handler emits coordination charges through `unit_ticks`, as repeated ordinary
unit `Tick` events. Prices belong to the interpretation, not the target program.
This separation lets serialization remove only coordination machinery and its
charges, preserving all computational ticks and duplicated child work. Use
`run_count (serialization program)` to observe its accumulated cost; serialization
is not tick ignoring. Invalid array operations retain their one-attempt charge and
abort the continuation under both interpretations.

`run_parallel` is a resource interpretation, not an executable multicore backend.
The separate `scheduled` predicate relates the interpreted parent source to a
concrete `pool_execution` certificate. Two sequential children can attain the
maximum of their counted costs on two lanes. Worker zero executes the parent and
then the left child; worker one executes the right child. The waiting parent saves
its continuation rather than occupying a third worker. These traces are proof
data, not storage allocated by the target; `Tau` and dispatch transitions carry no
ticks in this abstract model.

The shared library proves:

- **Accounting:** `parallel_branch_accounting`, `serial_branch_accounting`, and
  `branch_outcome_agreement` connect the same counted children to both
  interpretations. `run_parallel_lift_serial_leaf` reuses serial execution proofs,
  including automatic array charges and failure outcomes.
- **Composition:** `serial_fork_serial_execution_exact` combines successful serial
  prefix, child, and serial suffix witnesses into exact parallel and serialized
  leaves plus a schedule on the named `serial_fork_serial_trace`. The existing
  `serial_fork_serial_execution` is a compatibility wrapper that existentially
  hides the trace. `serial_fork_serial_outcome` proves equal array/value outcomes
  for that composition after disregarding resource counters.
- **Scheduling and bookkeeping:** `scheduled_attains` and `scheduled_matches_leaf`
  connect trace work and length to the resource counters. `scheduled_pool_budget`
  and `scheduled_worker_bookkeeping` bound workers, queues, saved continuations,
  open frames, and per-lane task records.
- **Arrays throughout execution:** `parallel_final_bound_subtree_leaf` bounds
  canonical residual arrays from a successful final leaf;
  `parallel_final_bound_handler_subtree_leaf` covers pending parent-handler ticks,
  and `parallel_waiting_array_bound` covers the unchanged array while children and
  coordination handlers run. These laws use canonical array monotonicity and
  successful termination, not a final-state bound alone.

## Derived programs and contracts

All four targets are chosen **inside their `Derive` proofs**. L1 uses a local
Fibonacci-specific induction lemma; L2 instantiates the shared countdown-loop rule;
L3 and L4 use the shared array rank-invariant rule. No target is a complete program
defined beforehand and wrapped in a theorem. `Derive` does not automatically
synthesize an algorithm.

### Level 1: naive recursion

`Fib_L1 : nat -> itree TimeE nat` uses guarded naive recursion, `function_entry`
for every invocation, and `cost_add` for each non-base addition.

`Spec_L1` requires `has_post` on `count (program input)`: the returned value equals
`Fib_L0 input`, and cost is at most `time_constant * 2^input`, with a positive
constant chosen before the input. It also requires `all_finite` of that counted
program for every input, ruling out divergence. `Fib_L1_spec` witnesses
`time_constant = 1`. The specification-only recurrence `fib_cost` is:

```text
T(0) = T(1) = 1
T(input + 2) = 2 + T(input + 1) + T(input)
```

`Fib_L1_leaf` and `Fib_L1_count` establish the exact counted result
`(fib_cost input, Fib_L0 input)`; `fib_cost_bound` proves `fib_cost input <= 2^input`.
`Fib_L1_terminates` proves counted termination; `Fib_L1_erases` proves the ignored
result. The raw target calls neither `Fib_L0` nor `fib_cost`.

### Level 2: a two-cell rolling array

`Spec_L2` refers directly to **`Fib_L1` only**, not to `Fib_L0`:

```coq
Definition Spec_L2
    (program_l2 : nat -> itree (ArrayE nat +' TimeE) nat) : Prop :=
  exists time_constant space_constant : nat,
    0 < time_constant /\ 0 < space_constant /\ forall input,
      eutt
        (fun '(cost_l2, outcome_l2) '(cost_l1, result_l1) =>
          match outcome_l2 with
          | None => False
          | Some (array_l2, result_l2) =>
              result_l2 = result_l1 /\
              cost_l2 <= time_constant * (input + 1) /\
              length array_l2 <= space_constant * (input + 1)
          end)
        (run_count (program_l2 input)) (count (Fib_L1 input)) /\
      all_finite (run_count (program_l2 input)).
```

Here `eutt` relates computations up to finite internal `Tau` steps. The relation
requires success and equal returned values, with independent L2 resource bounds;
it does **not** require equal costs. Correctness relative to L0 follows through L1.

`Fib_L2` allocates two cells initialized to `0` and `1`. Each continuing iteration
reads both, adds them through `cost_add`, and writes the next pair. Only the
remaining iteration count is loop-carried; Fibonacci data lives in the array.
The terminal invocation reads and returns the first cell.

The loop proof instantiates the shared rule with `step_cost = 6` and
`exit_cost = 2`. The Fibonacci-specific invariant and body proofs remain in
`FibonacciL2.v`.

`Fib_L2_leaf` and `Fib_L2_count` prove the exact counted outcome:

```text
(6 * input + 8,
 Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input))
```

`Fib_L2_spec` uses `time_constant = 8` and `space_constant = 2`.
`Fib_L2_terminates` proves termination; `Fib_L2_erases` gives the same optional
array/value outcome without counted cost. A constant number of cells satisfies
the approved linear space upper bound; the contract prescribes neither an
algorithm nor a table of all preceding Fibonacci values.

Shared `final_bound_subtree` and `final_bound_handler_subtree` proofs combine
monotone length, a successful final bound, and termination to bound canonical
residuals (remaining interpreted computations) and states during handler ticks.
`Spec_L2_intermediate_bound` applies the residual bridge to any satisfying program;
`Fib_L2_intermediate_bound` proves `length array <= 2` for this implementation's
canonical residuals. A final-state bound alone would not constrain divergence.

### Level 3: logarithmic time with two cells

`Spec_L3` relates `run_count (program_l3 input)` to `run_count (Fib_L2 input)`
by equality of successful returned values. It requires positive `time_constant`
and `space_constant`, independent of the input, such that L3's cost is at most
`time_constant * (Nat.log2 input + 1)` and its final array length is at most
`space_constant`. The relation rejects either failed outcome and leaves L2's
cost and array contents unconstrained. An explicit `all_finite` conjunct requires
all-input termination. See the [approved contract](docs/level-3-design-interview.md#approved-relational-contract).

`Fib_L3` initializes two cells to `0` and `1`, then runs two `cost_iter` loops
written inline in its `Derive` proof. The first constructs the most-significant-bit
mask by halving a scalar quotient and doubling the mask. The second processes the
bits from most to least significant, fast-doubling the Fibonacci pair stored in
the cells. Loop-carried values are scalar controls; persistent Fibonacci data
stays in the array. Data arithmetic uses `cost_add`, `cost_mul`, and `cost_sub`.
Natural-number subtraction truncates at zero; the fast-doubling proofs establish
that the intended difference is nonnegative. The executable target contains no
calls to earlier Fibonacci levels, specification-only cost functions, `Nat.log2`,
or `Nat.pow`.

`Fib_L3_leaf` and `Fib_L3_count` establish the exact counted outcome:

```text
(fib_l3_cost input,
 Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input))

fib_l3_cost 0 = 9
fib_l3_cost input = 8 + 13 * (Nat.log2 input + 1), when input > 0
```

`Fib_L3_spec` witnesses `time_constant = 21` and `space_constant = 2`.
`Fib_L3_terminates` proves termination; `Fib_L3_erases` preserves the same
optional array/value outcome when ticks are ignored.

`Spec_L3_intermediate_bound` derives a uniform constant bound on canonical residual
arrays for **any** program satisfying `Spec_L3`, using termination and shared
monotonicity. `Fib_L3_intermediate_bound` gives the implementation's two-cell bound;
`Fib_L3_handler_intermediate_bound` also covers pending handler prefixes. This is
an array-cell bound, not a bit-space or concrete runtime-storage guarantee. Source
review checks the fixed number of scalar controls and arithmetic temporaries and
the absence of input-sized auxiliary storage.

### Level 4: sequential improvement with the same array storage

The researcher approved a sequential replacement with a leading cost coefficient
**strictly below `13`** and L3's storage discipline. L3's actual positive-input
cost is `8 + 13 * (Nat.log2 input + 1)`; merely improving its uniform bound witness
`21` would not necessarily improve its actual cost. See the
[approved sequential design](docs/level-4-design-interview.md#approved-sequential-l4-revision).

`Spec_L4 (program_l4 : nat -> itree (ArrayE nat +' TimeE) nat)` existentially
quantifies `time_constant`, `additive_constant`, and `space_constant` before the
input, with `0 < time_constant < 13` and `0 < space_constant`. For every input it
requires:

- an `eutt` relation between `run_count (program_l4 input)` and
  `run_count (Fib_L3 input)`, rejecting either failure and requiring equal returned
  values;
- accumulated cost at most
  `additive_constant + time_constant * (Nat.log2 input + 1)` and final array length
  at most `space_constant`;
- `all_finite (run_count (program_l4 input))`.

The relation does not require equal costs or arrays. The specification leaves the
algorithm and concrete witnesses to `Derive`; the approved construction constraint
keeps persistent Fibonacci data in the array, with scalar controls and fixed
arithmetic temporaries. Current L4 has no fork/join prices, serialization,
work/span, or scheduling obligations, and its module does not import `Parallel`.

#### Construction and exact cost

`Fib_L4` initializes two cells to `0` and `1` and constructs both loops inside its
`Derive` proof using `cost_iter`. The first loop builds the binary mask with scalar
quotient/mask controls. The second carries only `(remaining, mask)` between
iterations, reading and updating the persistent Fibonacci pair in the array.
For `a = F(k)` and `b = F(k + 1)`, it computes only the next pair needed for the bit:

```text
bit 0: (a * ((b + b) - a), a * a + b * b)
bit 1: (a * a + b * b, b * ((a + a) + b))
```

Each branch uses six charged arithmetic operations, rather than L3's seven.
A continuing doubling step costs **11** ticks: one iteration entry, two reads,
six arithmetic operations, and two writes. Its terminal invocation costs **2**
ticks: entry and the result read. For positive input, the charged mask scan adds
`L = Nat.log2 input + 1` ticks. Function entry and two-cell initialization add six
ticks, yielding the exact costs below.

`Fib_L4_leaf` and `Fib_L4_count` establish the counted outcome
`(fib_l4_cost input, Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input))`.
`Fib_L4_count_from` also allows an arbitrary initial counter with an empty array.

| Input | L4 accumulated cost | L3 accumulated cost | Saving |
| --- | --- | --- | --- |
| `0` | `9` | `9` | `0` |
| Positive, with `L = Nat.log2 input + 1` | `8 + 12 * L` | `8 + 13 * L` | `L` |

`Fib_L4_spec` chooses `time_constant = 12`, `additive_constant = 8`, and
`space_constant = 2`. `fib_l4_cost_saving` proves the exact saving, and
`Fib_L4_improves_L3` proves strictly smaller accumulated cost for **every positive
input**, not just beyond a threshold. Zero ties. These are comparisons with the
actual L3 implementation, **not proofs of sequential optimality or runtime
speedup**. The target calls no earlier Fibonacci level, specification-only cost
function, `Nat.log2`, or `Nat.pow`.

#### Termination, tick ignoring, and space

The proof reuses `mask_count_all`, `binary_prefix_rank_step`, the shared array
rank-invariant rule, and `run_count_init_pair_bind`; Fibonacci-specific invariants
and arithmetic remain local. `Fib_L4_terminates` proves all-input termination, and
`Fib_L4_erases` preserves the successful array/value outcome under `run_ignore`.
Tick ignoring does not establish full runtime overhead erasure.

`Spec_L4_intermediate_bound` extends the final array bound to canonical residuals
for any satisfying program, using success, termination, and nondecreasing array
length. `Fib_L4_intermediate_bound` gives the implementation's **two-cell** bound;
`Fib_L4_handler_intermediate_bound` covers pending handler prefixes as well.
These are array-cell bounds, not bounds on bytes or natural-number bit sizes.
Independent reviews confirmed the scalar-storage discipline and cost fidelity;
this source-review assurance is separate from the checked array-cell bounds.

#### Superseded parallel L4

The parallel target is preserved at commit
`df9797b6a38c645c313b199ee1567627ecdc1773`, not in the current `FibonacciL4.v`.
Its children duplicated the full pair computation, and they carried persistent
Fibonacci pairs as scalars rather than using L3's array-storage discipline.
Its proved comparisons therefore combined overlap with different storage
allowances; they did not isolate a parallel benefit under L3's allowances or prove
an advantage over the best sequential algorithm. The
[historical implementation record](docs/level-4-design-interview.md#implementation)
preserves its exact contract, costs, proofs, and reviews. The generic `Parallel.v`
library remains independent and current.

## Verification and cost-fidelity boundary

`Cost.v`, `Array.v`, `Binary.v`, and `Parallel.v` contain shared state/option, cost,
iteration, space, binary-control, serialization, and fixed-pool laws; the Fibonacci
modules contain the reference identities, example-specific invariants, and bounds.
Checked laws establish helper and interpreter behavior. Source review checks
consistent use, complete and nonduplicated charges, and no repeated target
computation or reference shortcuts hidden in pure helpers. Raw ITree and Gallina
can bypass the helpers: **there is no universal cost-fidelity proof for arbitrary
candidates** or new restricted DSL.

**Historical L1/L2 baseline:** a clean whole-project build and `make examples`
passed in the prepared switch. Every audited theorem reported **“Closed under
the global context.”** Independent standards and specification reviews found no
issues, including their source-level cost-fidelity inspection. The
[L2 implementation record](docs/level-2-design-interview.md#implementation-verification)
preserves that evidence; it does not cover the L3 extension.

**Historical L3 integration:** all six source files compiled after `make clean`,
and the full integrated `make check` passed. All 58 registered theorems reported
“Closed under the global context,” and all 45 guardrail tests passed. Independent
standards and specification reviews of the extension found no actionable issues,
including the source-level checks for cost fidelity, fixed storage, and
construction inside `Derive`.

**Historical shared-proof extraction (L1–L3):** all seven source files compiled
after `make clean`, and the integrated `make check` passed with 61 closed
assumption reports and all 45 guardrail tests. L2 and L3 reuse the initialization
and exact-leaf space rules; L3 also uses the shared binary-control rules. The L0
monotonicity and doubling identities live alongside their reference in `Fibonacci.v`.

### L4 verification status

**Current sequential replacement: clean integrated gate passed; independent reviews
complete.** On **2026-10-28**, `opam exec --switch=cs2-rocq92 -- make clean`
completed, followed by a passing `opam exec --switch=cs2-rocq92 -- make check`
with `TIMED=1` and `TMPDIR` set to the approved temporary directory.

| Check | Current result |
| --- | --- |
| Clean build | **All nine modules compiled** |
| Executable and constructed-term replay | **Passed**, including actual L3/L4 examples and cost comparisons |
| Strict assumption audit | **All 101 names closed under the global context**, with the target and independent `Parallel.v` imported by default |
| Full guardrail suite | **All 46 passed**, including the new real-CLI default-import test |
| Independent standards review | **Complete: zero documented violations and zero actionable heuristic findings** |
| Independent specification/proof review | **Complete: zero findings** |

Both reviews covered exactly the **nine-file working-tree diff** against
`df9797b6a38c645c313b199ee1567627ecdc1773`, with `HEAD` still at that commit and no
intervening commits. Both accepted the clean gate, including all 101 closed audit
reports, all 46 guardrail tests, and example/constructed-term replay. No source
changes followed review; only documentation status metadata changed.
The [sequential verification record](docs/level-4-design-interview.md#sequential-implementation-verification)
records the gate results, compilation timings, exact review scope, and separate
standards and specification/proof results.

**Historical shared-proof extraction (`df9797b`): clean gate passed; reviews complete.**
The researcher approved four follow-up extractions on **2026-10-28**, relative to
`3a29285aac7767560a712494d73c38367d51b642`. On the same date, after
`opam exec --switch=cs2-rocq92 -- make clean`, the integrated
`opam exec --switch=cs2-rocq92 -- make check` passed with `TIMED=1` and `TMPDIR`
set to the approved temporary directory. All **nine** modules compiled, executable
examples and constructed terms replayed, all **104** audited declarations reported
**“Closed under the global context,”** and all **45** guardrail tests passed.
The audit includes seven shared helpers added to the historical 97-entry manifest.
Independent standards review found **zero documented violations and zero
actionable smells**; independent specification/proof review found **zero findings**.
Both covered the complete nine-file working-tree diff against the baseline above
and accepted the clean gate. The
[Shared-proof extraction record](docs/level-4-design-interview.md#shared-proof-extraction)
records the approved scope, preservation requirements, file timings, and completed
review results.

**Historical original parallel L4 (`3a29285`):** on 2026-10-28, all nine
modules passed a clean build before review cleanup. After the review fixes, the
incremental build compiled `Parallel.v` in 2.07 seconds, `FibonacciL4.v` in 0.75
seconds, and `Examples.v` in 0.69 seconds. The final
`opam exec --switch=cs2-rocq92 -- make check` then passed: executable examples and
constructed terms replayed, all **97** audited declarations—including
`Fib_L4_execution`—reported **“Closed under the global context,”** and all **45**
guardrail tests passed.

Independent standards review initially found two hard violations (event-sum
syntax and stale assurance status) and one heuristic issue (repeated proof
composition). All were fixed; follow-up found **zero remaining actionable
issues**. Independent specification review found **zero issues** both initially
and on follow-up. Both reviews confirmed source-level cost fidelity and the fixed
scalar/closure structure. The
[L4 implementation verification record](docs/level-4-design-interview.md#implementation-verification)
records that baseline's pinned review base, scope, and resolutions. Those checks
and the later extraction checks above do not certify the sequential replacement.

### Historical L1–L3 executable observations

The L1–L3 `Examples.v` baseline prints counted observations at the
following inputs:

| Input | Returned value (L1–L3) | L1 cost | L2 cost | L3 cost |
| --- | --- | --- | --- | --- |
| `0` | `0` | `1` | `8` | `9` |
| `1` | `1` | `1` | `14` | `21` |
| `2` | `1` | `4` | `20` | `34` |
| `5` | `5` | `22` | `38` | `47` |
| `10` | `55` | `265` | `68` | `60` |

The L3 counted examples cover `0, 1, 2, 3, 4, 5, 7, 8, 10, 15, 16`, including
inputs around powers of two; tick-ignoring execution is checked at `10`.
`Examples.v` also retains checks for generic `bool` arrays, failed accesses and
short-circuited continuations, empty allocation, terminal iteration, and finite
`Tau` prefixes. The theorem manifest and strict audit enforce assumption closure
separately. Guardrail tests exercise rejection of real axiom-dependent and admitted
fixtures, missing reports, and failed staged checks; the deliberately invalid
fixtures are generated only in temporary directories.
`observe_closed` uses fuel to traverse a closed tree; that allowance is not
accumulated cost. General proofs, not finite samples, establish all-input results.

### Sequential L4 executable checks

Current `Examples.v` contains L4 checks at
`0, 1, 2, 3, 4, 5, 7, 8, 10, 15, 16, 20`, tick ignoring at `10`, and counted
L3/L4 savings at `0, 1, 2, 5, 10, 20`. At `10`, both levels return `55` with array
`[Some 55; Some 89]`; L4 costs `56`, versus L3's `60`. These checks replayed in the
passing clean integrated gate; finite samples supplement the all-input proofs.

## Source map and design records

| File | Role |
| --- | --- |
| [theories/Cost.v](theories/Cost.v) | Unit ticks, charging helpers, count/ignore interpretations, array-free charged-loop rules, generic source-leaf, counter-shift, and closed-tree laws |
| [theories/Array.v](theories/Array.v) | Generic array/state/option interpretation, automatic charges, initialization and charged-loop rules, monotonicity and space bridges |
| [theories/Binary.v](theories/Binary.v) | Shared halving and ranked binary-prefix arithmetic, proof-only mask/cost witnesses, mask-body contract, and all-input polymorphic exact-cost scan rules |
| [theories/Parallel.v](theories/Parallel.v) | Independent shared fork/join library: coordination charges, work/parallel-time interpretation, serialization, exact trace composition, two-worker certificates, bookkeeping/array bounds, and generic fixtures; not imported by current L4 |
| [theories/Fibonacci.v](theories/Fibonacci.v) | L0 reference and arithmetic identities, revised recurrence, L1 contract, derivation, and proofs |
| [theories/FibonacciL2.v](theories/FibonacciL2.v) | L1-based contract, rolling-array derivation, loop and resource proofs |
| [theories/FibonacciL3.v](theories/FibonacciL3.v) | L2-based contract, fast-doubling derivation, logarithmic cost and constant array-space proofs |
| [theories/FibonacciL4.v](theories/FibonacciL4.v) | Sequential L3-based affine contract with coefficient below 13, array-based derivation, exact cost saving, termination/tick-ignoring proofs, and residual/handler array bounds |
| [theories/Examples.v](theories/Examples.v) | Executable examples and constructed-term inspection |
| [extraction/ExtractC.v](extraction/ExtractC.v), [scripts/extract_c.py](scripts/extract_c.py), [scripts/c_extraction_registry.json](scripts/c_extraction_registry.json) | Actual L1–L4 JSON export, reusable C lowering, and pinned supported-operation identities |
| [scripts/check_c.py](scripts/check_c.py), [tests/c/](tests/c/), [tests/test_c_extraction.py](tests/test_c_extraction.py) | C acceptance gate and independent positive/negative translation fixtures |
| [scripts/benchmark_c.py](scripts/benchmark_c.py), [docs/c-runtime-evaluation.md](docs/c-runtime-evaluation.md) | Optional reproducible native runtime comparison and recorded results |
| [checks/assumptions.txt](checks/assumptions.txt), [scripts/check_assumptions.py](scripts/check_assumptions.py) | Audited theorem list and fail-closed assumption gate |
| [.githooks/pre-commit](.githooks/pre-commit), [scripts/git_hooks.py](scripts/git_hooks.py) | Versioned commit guard and local installation |
| [tests/](tests/) | Positive and negative guardrail regression tests |
| [Makefile](Makefile), [_CoqProject](_CoqProject) | Build targets and logical prefix `RefineToITree` |

See [CONTEXT.md](CONTEXT.md), the [construction rules](AGENTS.md#program-construction),
the [cost conventions](docs/agents/cost-conventions.md), and the
[L2 interview](docs/level-2-design-interview.md) for terminology, rules, and design
decisions. The [L3 interview](docs/level-3-design-interview.md) records the approved
2026-10-28 decisions, throwaway feasibility probes, implementation, and passing
integrated check and independent reviews. The
[L4 interview](docs/level-4-design-interview.md) leads with the approved sequential
contract, implementation, passing clean integrated gate, and completed independent
reviews. It also preserves the superseded parallel approvals, implementation, and
passing checks.
Its historical
[Shared-proof extraction record](docs/level-4-design-interview.md#shared-proof-extraction)
records the approved parallel-era refactor, whose clean integrated gate passed and
independent reviews completed with no actionable issues.
The [initial L1 interview](docs/design-interview.md) is historical.
The approach is motivated by Section 2 of
[Don't Sweat Interaction Trees](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.16);
this project supplies its own cost semantics and approved construction discipline.
