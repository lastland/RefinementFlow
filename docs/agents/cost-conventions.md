# Cost conventions

These are the approved, canonical charging rules for **Levels 1–4 and future examples**, including the retroactive Level 1 revision. The shared time, array, and parallel modules and all four derived Fibonacci levels implement this discipline.

**Current integrated gate includes L1–L4 C extraction.** `make -j2 check` passed the theory build and example replay, audited all **101** declarations as **“Closed under the global context,”** passed all **85** Python guardrail tests, and passed the C gate in ordinary and sanitized builds. The native execution ranges are **`0..30` for L1** and **`0..91` for L2/L3/L4**, giving **307 exact comparisons per build**. Six independent native fixtures passed and 14 unsupported source fixtures were rejected. The backend's execution/artifact evidence is separate from source-level proof assurance: it does not prove C translation correctness, general natural-arithmetic preservation, or machine resource bounds. The optional runtime experiment records exponential/linear/bit-length scaling and a slower native L4 in the measured build; it does not equate abstract ticks with runtime. See [four-level extraction verification](../c-extraction-design-interview.md#l1l2-extension-and-runtime-evaluation), the [C extraction guide](../c-extraction.md), and [native runtime evaluation](../c-runtime-evaluation.md).

**Sequential L4 source verification, before C extraction: clean integrated gate passed; independent standards and specification/proof reviews complete.** After `make clean`, the integrated `make check` compiled all **nine** modules, replayed actual L3/L4 examples and cost comparisons, audited all **101** declarations as **“Closed under the global context,”** and passed all **46** guardrail tests, including the new real-CLI default-import test. The audit imported the target and independent `Parallel.v` by default and retained every shared-library entry. Standards review found **zero documented violations and zero actionable heuristic findings**; specification/proof review found **zero findings**. Both accepted the clean gate. The replacement follows the approved coefficient bound and L3 storage discipline without changing the charging rules. See [Sequential implementation verification](../level-4-design-interview.md#sequential-implementation-verification) for the commands, timings, and completed review record.

**Historical shared-proof extraction (`df9797b`):** its clean integrated `make check` compiled all **nine** modules, replayed executable examples and constructed terms, audited all **104** declarations as **“Closed under the global context,”** and passed all **45** guardrail tests. Independent standards review found **zero documented violations and zero actionable smells**; specification/proof review found **zero findings**. The [Shared-proof extraction record](../level-4-design-interview.md#shared-proof-extraction) preserves the commands, timings, review scope, and preservation results for that parallel-L4 baseline.

**Historical original parallel L4:** all nine modules passed a clean build. After review fixes, its final `make check` passed executable replay, all **97** audited declarations were closed, and all **45** guardrail tests passed. Independent follow-up reviews found **zero remaining actionable issues**; see the [historical L4 review record](../level-4-design-interview.md#independent-implementation-review). Neither historical gate verifies the sequential replacement. See the [README](../../README.md) for interfaces and current status, and the [Level 2](../level-2-design-interview.md), [Level 3](../level-3-design-interview.md), and [Level 4](../level-4-design-interview.md) interviews for decisions.

## Unit ticks and interpretation

- Use a dedicated singleton time effect and a unit `tick` operation:

  ```coq
  Variant TimeE : Type -> Type := Tick : TimeE unit.

  Definition tick : itree TimeE unit := trigger Tick.
  ```

- Do not represent time with `writerE`, numeric payloads, or weighted charge events. Each `Tick` represents exactly one abstract cost unit.
- The canonical counting interpreter `count` owns a private counter, starts at zero, and adds exactly one per tick. Its interpreted pair is `(cost, value)`. Raw programs return only their computational value, not a chosen cost total.
- The tick-ignoring interpretation `ignore_time` supplies `tt` and preserves the computational outcome, including success or failure, after discarding counted cost. This supports non-counting execution; **full runtime overhead erasure is not established**.

## Target-program charges

| Work | Unit ticks |
| --- | --- |
| Every constructed program function invocation, including outermost calls, recursive calls, and base cases | One on entry |
| Every `ITree.iter` body invocation, including the terminal exit-check invocation | One on entry |
| Each primitive arithmetic operation on data values | One per operation |

- The iteration-entry tick covers loop-control comparisons, index maintenance, and branching, including index-only halving and mask updates. Arithmetic on computational data receives separate primitive-operation ticks.
- The iteration-body callback receives its entry charge through the iteration rule; representing it as a Gallina function does not add a second function-entry charge. A target-program function called from the body receives its normal function-entry charge.
- Pure or control helpers must not hide repeated target computation. Expose preprocessing scans, including binary-mask construction, as charged calls or iterations.
- Helpers that implement primitives or library interpreters are not themselves target-program function calls. Do not add duplicate abstract charges for implementing a primitive.

These are abstract operation costs, not machine-time or bit-complexity guarantees.

## Current sequential L4 bounds and storage

The [approved sequential revision](../level-4-design-interview.md#approved-sequential-l4-revision) uses `ArrayE nat +' TimeE`, like L3. Its algorithm-independent contract existentially quantifies `time_constant`, `additive_constant`, and `space_constant` before the input, with `0 < time_constant < 13` and `0 < space_constant`. The cost bound is `additive_constant + time_constant * (Nat.log2 input + 1)`. The ceiling `13` comes from L3's actual positive-input coefficient, not its looser uniform bound witness `21`; the derivation still chooses the algorithm and concrete resource witnesses.

Persistent Fibonacci data must remain in the mutable array. Loop-carried scalar controls and a fixed number of arithmetic temporaries follow L3's construction discipline; moving the persistent pair into scalar loop state would change the storage allowances of the comparison. `Spec_L4` states successful returned-value agreement with actual L3, a final array-length bound, and all-input finiteness. Shared monotonicity extends the array bound to canonical residuals; the implementation also proves the bound during pending handlers. Scalar payload size remains outside these array-cell theorems. Current L4 has no prices, fork, serialization, work/span, or worker-budget obligations.

## Shared parallel composition

These rules originated in the **superseded parallel L4 design**, approved on **2026-10-28**, whose round 5 replaced the original one-tick coordination prices. They remain valid rules for the independent shared library, not requirements of current `Spec_L4`. `Parallel.v` retains its effects, interpreters, concrete fixed-pool certificates, generic fixtures, and audited laws. Current `FibonacciL4.v` does not import it. `Cost.v` supplies generic interpreter/counter laws and array-free charged-loop rules for library clients.

- Retain accumulated cost as total charged work. Parallel time measures the longest dependency chain of charged operations: sequential costs add, and independent parallel child costs combine by maximum.
- Fork and join have positive, input-independent parameters `fork_cost` and `join_cost`, held in `Prices` and supplied to the interpreter rather than the target. The fork handler emits the respective charges as repeated ordinary unit ticks before the children execute and after both complete. These coordination ticks contribute to accumulated cost and parallel time. They are abstract costs; backend calibration has not been established.
- A parallel speedup claim must state its supported conditions on coordination prices and exhibit a positive configuration satisfying them. Resource constants may depend on that fixed configuration, but not on the computational input. The library's `positive_prices` predicate records positivity; it is not part of current `Spec_L4`.
- Serialization executes both children sequentially and omits fork/join coordination and its charges. It retains the same computational work, including duplicated arithmetic, and all function-entry, iteration, arithmetic, and automatic array charges. A comparison with serialization measures the benefit of overlap in that program, not improvement over a separately optimized sequential algorithm or in runtime wall-clock measurements.
- An inline child computation receives no extra function-entry tick merely for being a parallel branch. A target-program function called by a child receives its normal function-entry tick. Required iteration and arithmetic charges also continue to apply within children.
- Longest-path parallel time does not by itself specify a finite-processor schedule. A worker-budget claim needs a proof that a schedule within that budget attains the reported time, counting the worker executing the parent. The shared `scheduled` predicate uses source-linked `pool_execution` certificates: two sequential children occupy two lanes, so their counted costs combine by maximum. These traces are proof data, not target-program allocations or an executable multicore backend.
- Parallel storage accounting covers queued tasks, saved continuations, and retained results wherever stored. The checked storage propositions bound array cells and payload-free task records. Source review checks bounded scalar state, arithmetic temporaries, and closure/result payloads; those payload bounds are not universal machine-checked theorems. Total modeled bookkeeping/array storage is bounded by the worker budget times the per-worker constant, plus the shared constant.
- The shared fork/join primitive accepts two sequential, array-free children operating on local scalar data. Mutable-array operations remain in the parent; children cannot fork further children.

### What shared parallel storage bounds count

`worker_bookkeeping` counts payload-free task records, in state `RunningTask` or `RetainedResult`. An idle lane can still retain a completed child's result record until join. **One record does not mean one scalar or a bound on the record's payload size.**

The shared bound covers:

```text
length array + queued_children round + saved_continuations round
  + 2 * open_fork_frames round <= shared_constant
```

The last term reserves two bookkeeping slots per open fork frame, not two simultaneously open frames. The shared two-lane schedule has at most one open frame and one saved parent continuation; eager dispatch uses no queue, satisfying the library's at-most-one queued-child bound. Array bounds depend on the parent program; children and coordination handlers cannot modify its array.

The historical parallel target at `df9797b6a38c645c313b199ee1567627ecdc1773` chose `pool_size = 2`, `per_worker_constant = 1`, and `shared_constant = 32`, giving **34 bookkeeping/array units**. Its L4-specific storage theorems and reviews are preserved in the [historical implementation record](../level-4-design-interview.md#what-the-storage-proof-establishes), not asserted for the sequential target. The shared library proofs remain current and audited.

## Automatic array charges

- Use polymorphic `ArrayE A` with allocation, read, and set operations. Canonical state is `list (option A)`.
- `alloc size` retains existing cells, appends `size` uninitialized `None` cells, and returns the old array length as the starting index.
- `read index` has result type `A`, not `option A`. An out-of-bounds or uninitialized read aborts the canonical interpretation with `None`.
- A valid `set index value` stores `Some value` and returns `tt : unit`; an out-of-bounds set aborts the canonical interpretation with `None`.
- Reads and sets preserve array length. There is no deallocation, so canonical array length is nondecreasing. Space counts all allocated cells, including uninitialized cells.

The common array interpreter emits the following **actual unit `Tick` events**, not a weighted charge event. Examples must not duplicate these automatic charges.

| Array operation | Automatically emitted unit ticks |
| --- | --- |
| `alloc size` | `size + 1`: one operation tick plus one per new cell |
| `read index` | One per attempt, including failure |
| `set index value` | One per attempt, including failure |

In particular, `alloc 0` still emits one tick.

## Shared machinery and assurance boundary

- Common combinators insert function-entry, iteration-entry, and primitive-arithmetic ticks. The implemented helpers are `function_entry`, `cost_iter`, `cost_add`, `cost_mul`, and `cost_sub`. Their generic laws and the canonical interpreter laws are proved once in the common library and reused across examples, including exact accumulation and preservation of outcomes under tick ignoring. `count_cost_iter_rank_invariant` gives the corresponding exact-cost rule for array-free `TimeE` loops; its rank is proof data, not an executable countdown.
- `Cost.v` now owns `interp_leaf_source` and `interp_state_leaf_source`, which recover source leaves from interpreted leaves, and `count_offset` and `count_shift_leaf`, which shift initial counters while preserving returned values. These four generic facts moved from `Parallel.v` without changing their statements or adding imports or dependencies to `Cost.v`.
- `Binary.v` owns `binary_mask` and `mask_scan_cost` as **proof-only witnesses**, not executable preprocessing helpers. Its `mask_count_all` rule covers zero and positive inputs with arbitrary scale, array of any cell type, and starting counter; it preserves the array and adds exactly `mask_scan_cost input` ticks. Its `binary_prefix_rank_step` packages the pure control step, including the last-bit transition to rank zero. L3 and L4 reuse these rules while keeping their Fibonacci-specific data proofs local. Both targets still construct the mask through an explicit charged `cost_iter` loop inside `Derive`.
- `Parallel.v` independently proves branch accounting, serialization laws, concrete two-worker attainability, task-record bounds, and parent-array bounds. Its `serial_fork_serial_execution_exact` rule composes successful serial-prefix, child, and serial-suffix witnesses into exact parallel/serialized leaves and a schedule on `serial_fork_serial_trace`. The existing existential `serial_fork_serial_execution` remains a compatibility wrapper, and `serial_fork_serial_outcome` proves array/value agreement. The named trace remains proof data, not target storage. Pending parent-handler and fork-handler bounds retain the canonical parent array; children and coordination cannot modify it.
- `cost_mul` and `cost_sub` each charge one tick for every pair of operands. `cost_sub` uses natural-number subtraction, which truncates at zero.
- Individual examples must use this shared machinery consistently. Checked helper and interpreter laws establish what the machinery does; source review checks that a program uses it for all required work without omitted or duplicate charges.
- Unrestricted raw ITree and Gallina can bypass these helpers. A cost bound or numerical agreement with a recurrence does not establish universal machine-checked cost fidelity. This policy uses common helpers and review, not a new DSL or generic enforcement framework.

The approved assurance model retains L1's source discipline and agent review alongside checked generic laws. All audited theorems, including shared interpreter laws and all four levels' specification, termination, and resource results, must report **“Closed under the global context.”** `make check` enforces closure for `checks/assumptions.txt`, alongside the build, examples, guardrail regression tests, and C acceptance gate. The sequential revision replaces obsolete parallel-L4-specific entries while retaining every shared-library entry. The audit script imports `RefineToITree.FibonacciL4` and `RefineToITree.Parallel` independently by default; explicit, repeatable `--module` arguments replace both defaults.

The completed independent sequential reviews covered exactly the **nine-file working-tree diff** against `df9797b6a38c645c313b199ee1567627ecdc1773`; `HEAD` remained at that commit with no intervening commits. Their source inspection confirmed six charged arithmetic operations per bit, the persistent Fibonacci pair in the array with scalar controls, and construction inside `Derive` with the `Spec_L4 Fib_L4` goal. This source-review assurance remains distinct from the checked resource theorems. No source changes followed review; only documentation status metadata changed. Historical parallel-L4 reviews remain separate evidence for their baselines. The local pre-commit hook runs the integrated gate on an isolated staged snapshot; see the [README verification commands](../../README.md#build-and-replay-checks).

## Implemented Level 1 revision

The uniform rules replace L1's invocation-only model with function-entry and addition costs. For naive Fibonacci, each non-base invocation contributes one entry tick and one addition tick, besides its two recursive costs:

```text
T(0) = 1
T(1) = 1
T(input + 2) = 2 + T(input + 1) + T(input)
```

The revised costs are `4` for input `2` and `22` for input `5`, rather than `3` and `15`. The repository's `Fib_L1_leaf` and `Fib_L1_count` now connect the counted program to this recurrence for every input. `fib_cost_bound` proves `T(input) <= 2^input`, and `Fib_L1_spec` uses `time_constant = 1`. The [original L1 interview](../design-interview.md) preserves the historical model and its verification evidence.

## Naming

Use level-neutral common arguments such as `program`, `array`, `size`, `index`, and `value` or `input`. Name uniform bound constants `time_constant` and `space_constant`; use `additive_constant` for the input-independent offset in L4's affine time bound. Shared parallel accounting uses `pool_size`, `per_worker_constant`, and `shared_constant` for worker and storage bounds. Reserve level suffixes such as `_l1`, `_l2`, `_l3`, and `_l4` for cross-level example specifications.
