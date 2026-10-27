# Level 4 Design Interview

**Current status: sequential L4 approved and implemented; clean integrated gate passed; independent standards and specification/proof reviews complete.** All nine modules compiled, actual L3/L4 examples and comparisons replayed, all **101** audited names were closed under the global context, and all **46** guardrail tests passed. Standards review found **zero documented violations and zero actionable heuristic findings**; specification/proof review found **zero findings**. The current design retains L3's array-storage discipline and requires a leading cost coefficient strictly below `13`. The implementation saves exactly `Nat.log2 input + 1` ticks over actual L3 for every positive input and ties at zero.

The [sequential verification record](#sequential-implementation-verification) records the completed gate and independent reviews. The [parallel history](#historical-parallel-l4-superseded-at-df9797b) preserves the earlier approvals, implementation, and **104/45** extraction and **97/45** original integration audit/test results. Those historical passes do not verify this replacement.

## Approved sequential L4 revision

After the shared-proof extraction, the researcher approved replacing parallel L4 with a sequential specification whose leading time-cost coefficient is **strictly below `13`** (“Let's try 13”). The researcher also confirmed retaining L3's storage discipline. The fixed replacement baseline is **`df9797b6a38c645c313b199ee1567627ecdc1773`**.

L3's exact positive-input cost is `8 + 13 * (Nat.log2 input + 1)`; its cost at zero is `9`. Its uniform bound witness is `21`. Requiring only a witness below `21` need not improve on L3's actual cost. The approved affine bound separates a uniform additive constant from a leading coefficient below L3's actual `13`.

The construction constraint also matters: persistent Fibonacci values live in the mutable array, with scalar controls and bounded arithmetic temporaries. This keeps the sequential comparison under L3's storage allowances. The old parallel children both duplicated the full pair computation and carried their persistent Fibonacci pairs as scalars. Their proved comparisons therefore did not isolate a parallel benefit under L3's array-storage discipline. Neither those results nor the sequential replacement prove optimality among sequential algorithms or a runtime speedup.

### Approved relational contract

The production [`theories/FibonacciL4.v`](../theories/FibonacciL4.v) now defines:

```coq
Definition Spec_L4
    (program_l4 : nat -> itree (ArrayE nat +' TimeE) nat) : Prop :=
  exists time_constant additive_constant space_constant : nat,
    0 < time_constant /\ time_constant < 13 /\ 0 < space_constant /\
    forall input,
      eutt
        (fun '(cost_l4, outcome_l4) '(cost_l3, outcome_l3) =>
          match outcome_l4, outcome_l3 with
          | Some (array_l4, result_l4), Some (array_l3, result_l3) =>
              result_l4 = result_l3 /\
              cost_l4 <= additive_constant + time_constant * (Nat.log2 input + 1) /\
              length array_l4 <= space_constant
          | _, _ => False
          end)
        (run_count (program_l4 input)) (run_count (Fib_L3 input)) /\
      all_finite (run_count (program_l4 input)).
```

All three witnesses are chosen before the input. The relation requires both outcomes to succeed and compares returned values with **actual `Fib_L3`**, without requiring equal arrays or costs. `all_finite` rules out divergence. The final array bound extends to canonical residuals through `Spec_L4_intermediate_bound`, using successful termination and shared array monotonicity. The scalar-storage discipline is a source-reviewed construction constraint, not a payload-size theorem encoded in `Spec_L4`.

The specification prescribes neither an algorithm nor the concrete witnesses `12`, `8`, and `2`. Its arbitrary additive constant also means the contract alone does not require a saving on every positive input; the implementation proves that stronger result separately. There are no current L4 fork/join prices, serialization, work/span, scheduling, or worker-budget obligations.

### Sequential construction and proofs

The target is constructed inside:

```coq
Derive (Fib_L4 : nat -> itree (ArrayE nat +' TimeE) nat) in
  (Spec_L4 Fib_L4) as Fib_L4_spec.
```

`Fib_L4` enters through `function_entry`, allocates two cells, and initializes them to `0` and `1`. Both subsequent loops use shared `cost_iter` and are written inside `Derive`. The mask scan carries a scalar quotient and mask. The doubling loop carries only `(remaining, mask)`; it reads the Fibonacci pair from the array, computes the next pair for the current bit, and writes both cells back. The fixed arithmetic temporaries do not persist as loop state.

For `a = F(k)` and `b = F(k + 1)`, the bit-specific pairs are:

```text
bit 0: (a * ((b + b) - a), a * a + b * b)
bit 1: (a * a + b * b, b * ((a + a) + b))
```

Each branch computes only the two needed coordinates, using **six charged arithmetic operations** rather than L3's seven. A continuing doubling step costs **11** ticks: entry, two reads, six arithmetic operations, and two writes. The terminal invocation costs **2** ticks for entry and the result read. For positive input, the mask scan adds `L = Nat.log2 input + 1` ticks; function entry and initialization add six more. At zero, the mask scan costs one tick and doubling exits immediately.

`Fib_L4_spec` chooses `time_constant = 12`, `additive_constant = 8`, and `space_constant = 2`. The exact outcome is:

```text
(fib_l4_cost input,
 Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input))
```

| Input | L4 cost | L3 cost | Exact saving |
| --- | --- | --- | --- |
| `0` | `9` | `9` | `0` |
| Positive, with `L = Nat.log2 input + 1` | `8 + 12 * L` | `8 + 13 * L` | `L` |

The proof reuses `run_count_init_pair_bind`, `mask_count_all`, `binary_prefix_rank_step`, and `run_count_cost_iter_rank_invariant`; Fibonacci identities and data invariants remain local. Prefix, exponent, and remaining rank are proof data, not additional loop state. The target calls no earlier Fibonacci implementation, specification-only cost function, `Nat.log2`, or `Nat.pow`.

The production results include:

- **Exact execution:** `Fib_L4_count_from` starts from an empty array and any counter; `Fib_L4_leaf` and `Fib_L4_count` expose the zero-counter result.
- **Improvement:** `fib_l4_cost_saving` proves `fib_l4_cost input + (Nat.log2 input + 1) = fib_l3_cost input` for positive input. `Fib_L4_improves_L3` proves strict improvement for every such input. Both compare exact costs, not merely bound witnesses.
- **Termination and tick ignoring:** `Fib_L4_terminates` proves all-input finiteness. `Fib_L4_erases` preserves the successful array/value outcome under `run_ignore`; it does not prove full runtime overhead erasure.
- **Array bounds:** `Spec_L4_intermediate_bound` covers canonical residual arrays for every satisfying program. `Fib_L4_intermediate_bound` proves the target's two-cell bound, and `Fib_L4_handler_intermediate_bound` also covers pending handler prefixes. These are cell counts, not bit-space or byte bounds.

Current `FibonacciL4.v` does not import `Parallel`. [`Parallel.v`](../theories/Parallel.v) remains an independent shared library with its generic fixtures and valid audited proofs; replacing the Fibonacci target does not remove or turn those library results into historical-only claims.

### Sequential implementation verification

**Status as of 2026-10-28: clean integrated gate passed; independent sequential standards and specification/proof reviews complete.**

On **2026-10-28**, `opam exec --switch=cs2-rocq92 -- make clean` completed, followed by a passing `opam exec --switch=cs2-rocq92 -- make check` with `TIMED=1` and `TMPDIR` set to the approved temporary directory. The gate compiled all nine modules, replayed the actual L3/L4 examples and cost comparisons, closed all 101 assumption reports, and passed all 46 guardrail tests.

| Check | Result |
| --- | --- |
| Clean build | **Passed**, all nine modules compiled |
| Individual L4 assumption reports | **Closed**, including the contract, exact-cost/improvement, termination, tick-ignoring, and residual/handler array-bound results |
| Earlier focused assumption-guard tests | **35 passed**, before the clean integrated gate |
| Current manifest | **101 declarations**; obsolete parallel-L4-specific entries replaced, every shared-library entry retained |
| Full integrated gate | **Passed on 2026-10-28**, with the commands above |
| Executable/constructed-term replay | **Passed**, including actual L3/L4 examples and comparisons |
| Integrated strict assumption audit | **All 101 names closed under the global context**, with target and independent parallel-library default imports |
| Full guardrail suite | **All 46 passed**, including the new real-CLI default-import test |
| Independent review baseline | `df9797b6a38c645c313b199ee1567627ecdc1773` |
| Independent review scope and accepted gate evidence | **Exactly nine working-tree files** against the baseline above; both reviews accepted the clean gate |
| Independent standards review | **Complete: zero documented violations and zero actionable heuristic findings** |
| Independent specification/proof review | **Complete: zero findings** |

| File | Compilation time (seconds) |
| --- | --- |
| `Cost.v` | `0.71` |
| `Array.v` | `2.10` |
| `Parallel.v` | `2.05` |
| `Binary.v` | `0.42` |
| `Fibonacci.v` | `0.41` |
| `FibonacciL2.v` | `0.45` |
| `FibonacciL3.v` | `0.57` |
| `FibonacciL4.v` | `0.59` |
| `Examples.v` | `0.88` |

The audit script imports `RefineToITree.FibonacciL4` and `RefineToITree.Parallel` independently by default; the passing 101-name audit used those defaults. Explicit `--module` arguments replace them and may be repeated. The new real-CLI regression fixture for both default imports passed within the 46-test suite; existing explicit-module fixtures also passed their override checks.

`Examples.v` contains sequential L4 checks at `0, 1, 2, 3, 4, 5, 7, 8, 10, 15, 16, 20`, counted savings at `0, 1, 2, 5, 10, 20`, and tick ignoring at `10`. At input `10`, L4 returns `55` with array `[Some 55; Some 89]` and cost `56`, compared with L3's `60`. These checks replayed in the passing clean integrated gate; finite samples supplement rather than replace the all-input proofs.

#### Independent sequential reviews

Both independent reviews covered exactly the **nine-file working-tree diff** against **`df9797b6a38c645c313b199ee1567627ecdc1773`**. `HEAD` remained at that commit; there were no intervening commits. The scope comprised `theories/FibonacciL4.v` and `theories/Examples.v`; `checks/assumptions.txt`, `scripts/check_assumptions.py`, and `tests/test_assumptions.py`; and `README.md`, `CONTEXT.md`, `docs/agents/cost-conventions.md`, and this interview record.

- **Standards review: complete.** **Zero documented violations and zero actionable heuristic findings.**
- **Specification/proof review: complete.** **Zero findings.**

Both accepted the clean nine-module build, all **101** closed assumption reports, all **46** passing guardrail tests, and executable example and `Print` replay, with the compilation timings above. Their inspection confirmed:

- six charged arithmetic operations per bit, the persistent Fibonacci pair in the array with scalar loop controls, and construction inside `Derive` with the unchanged `Spec_L4 Fib_L4` goal and witnesses `time_constant = 12`, `additive_constant = 8`, and `space_constant = 2`;
- exact cost `9` at zero and `8 + 12 * L` for positive input, where `L = Nat.log2 input + 1`, strict improvement for every positive input, comparisons of actual `run_count` executions, all-input finiteness, and residual and pending-handler array bounds;
- the 101-entry manifest retaining every shared-library entry, independent target and `Parallel` default imports, and real-CLI tests of both defaults and explicit `--module` overrides.

No source changes followed review; only documentation status metadata changed. These completed reviews retain the distinction between checked array-cell bounds and source-reviewed scalar-storage discipline. They establish neither sequential optimality nor a runtime-backend speedup.

### Sequential feasibility evidence

A temporary `L4SequentialFeasibility20261028.v` compiled in the `cs2-rocq92` switch on 2026-10-28. It typechecked the proposed algorithm-independent relation and constructed an array-based candidate inside `Derive`, using charged mask and doubling loops. The bit-specific arithmetic used six operations per bit, so the continuing doubling step cost `11` and its terminal invocation cost `2`.

The temporary proof established all-input correctness, termination, exact accumulated cost, and a two-cell bound throughout execution, including pending handlers:

```text
cost at zero:            9
cost for positive input: 8 + 12 * (Nat.log2 input + 1)
proposed witnesses:      a = 12, b = 8, s = 2
```

For every positive input, this candidate saved exactly `Nat.log2 input + 1` ticks relative to actual L3. Executable checks covered `0, 1, 2, 3, 4, 5, 7, 8, 10, 15, 16, 20`; input `10` returned `55` with cost `56`, compared with L3's `60`. All 15 audited proof declarations were closed under the global context. This remains historical feasibility evidence, not an integrated gate result or an imposed algorithm.

## Historical parallel L4: superseded at df9797b

**Scope of the remaining sections:** the parallel interview rounds, implementation, shared-proof extraction, and probes are historical. The superseded target is preserved in `theories/FibonacciL4.v` at commit **`df9797b6a38c645c313b199ee1567627ecdc1773`**. Its L4-specific types, names, and obligations below do not describe the current sequential file. Shared `Parallel.v` interfaces and proofs remain available independently.

**Historical parallel approval:** the researcher gave final approval on **2026-10-28**, after the response “OK approved.” See the [approved consolidated design](#approved-consolidated-design). The later [Shared-proof extraction](#shared-proof-extraction), also approved on that date, passed a clean integrated `make check`: all nine modules compiled, executable examples and constructed terms replayed, all **104** audited declarations were closed under the global context, and all **45** guardrail tests passed. Independent standards and specification/proof reviews completed with no actionable issues.

**Historical original implementation baseline:** all nine modules passed a clean build. After review fixes, its final integrated `make check` passed executable replay, all **97** audited declarations were closed, and all **45** guardrail tests passed. Independent follow-up reviews found **zero remaining actionable issues**. See [Implementation](#implementation) for the historical contract and derivation, and [Implementation verification](#implementation-verification) for that baseline's checks, review scope, and resolutions.

The rounds below retain their original decision sequence: question 10 superseded the fixed one-tick fork/join prices, and the later sequential approval superseded the parallel L4 design as a whole. Probe limitations describe their earlier stages, not missing all-input proofs in the completed historical parallel implementation.

### Subject

Use parallelism to improve the time cost of the next Fibonacci level beyond Level 3.

### Existing context

The [cost conventions](agents/cost-conventions.md) count abstract operations under the unit-cost, array-cell model. The canonical counting interpreter measures accumulated cost, not overlapping execution or machine running time.

For positive input, the implemented L3 has exact accumulated cost `8 + 13 * (Nat.log2 input + 1)`; its cost at zero is `9`. It uses two array cells. See the [L3 interview](level-3-design-interview.md).

### Confirmed requirements: round 1

The researcher answered yes to both questions and clarified that parallel time should count the longest chain.

1. Retain accumulated cost as the total charged work. Add parallel time as the cost of the longest dependency chain: sequential costs add, and independent parallel branches combine by maximum.
2. Compute one exact Fibonacci number for every natural-number input, with `Fib_L3` as the direct behavioral reference.

The researcher also reaffirmed the existing construction discipline: write an algorithm-independent specification, then construct the implementation through its proof inside `Derive`. The derivation chooses the algorithm and concrete resource-bound witnesses within the approved constraints. Shared primitives and proof rules belong in the common library; target-program loops use `cost_iter`.

The [domain context](../CONTEXT.md) now defines sequential Level 4; it retains parallel time, serialization, and worker budget as terms for the shared library.

### Confirmed requirements: round 2

The researcher accepted questions three through five and clarified the space requirement in question six.

3. Require a uniform constant-factor parallel-time improvement over L3's exact accumulated cost for all sufficiently large inputs. The derivation chooses the factor and threshold. Correctness and termination remain all-input requirements. Round 5 adds a second required comparison, with the same program serialized.
4. Round 2 originally assigned one ordinary unit tick to each fork and join. **Round 5 supersedes these fixed prices.** The rest of this decision stands: inline child computations receive no additional function-entry tick merely for being parallel branches; calls to target-program functions retain their normal entry charges.
5. Accumulated cost must remain logarithmic, with its own derivation-chosen uniform constant. Coordination may increase accumulated cost above L3's.
6. A constant space bound per concurrent thread or process is acceptable. The researcher raised a fixed-size thread pool as a way to obtain constant total storage. Round 3 subsequently settled the worker-budget requirement and the accounting of shared storage, queued tasks, and saved continuations.

See [Shared parallel composition](agents/cost-conventions.md#shared-parallel-composition) for the retained charging rules. Round 5 below replaces the historical one-tick prices in point 4.

### Confirmed requirements: round 3

The researcher answered yes to questions seven and eight.

7. Require an input-independent worker budget, chosen by the derivation, and prove that a schedule within that budget attains the reported longest-chain parallel time. Count the worker executing the parent computation within the budget. A waiting parent's saved continuation consumes storage without necessarily reserving an execution worker.
8. Require constant per-worker space and a separate constant shared-storage bound. Count queued tasks and saved continuations wherever they are stored. Total modeled storage is bounded by `pool_size * per_worker_constant + shared_constant`. Array-cell bounds are proved; bounded scalar state and task bookkeeping follow the shared-construction discipline and source review, as at L3.

### Confirmed requirements: round 4

The researcher answered yes to question nine.

9. The first L4 may use a reusable fork/join primitive with two sequential, array-free children operating on local scalar data. Mutable-array operations remain in the parent. The children use the existing charged arithmetic and iteration machinery, return their results at join, and complete before the parent continues. The specification remains algorithm-independent; the derivation chooses the computations to overlap.

### Reopened question: coordination price and practical runtime

Before consolidated approval, the researcher asked whether fork should be more expensive to reflect practical runtime. This reopened the one-tick fork and join prices from round 2. **Round 5 resolves this question by approving positive fixed parameters, and adds a comparison with the same program serialized.** The discussion below records the motivation, not an unresolved pricing decision.

Primary runtime sources establish that task coordination needs sufficient useful work, but do not determine a universal conversion to this project's arithmetic ticks:

- The [OCaml parallelism manual](https://ocaml.org/manual/latest/parallelism.html#s%3Apar_domains) describes domains as heavyweight entities mapped to operating-system threads. The [Domainslib example](https://ocaml.org/manual/latest/parallelism.html#s%3Apar_parfib_domainslib) explicitly switches to sequential computation for small problems because parallelization can outweigh the work available.
- [Domainslib's implementation](https://github.com/ocaml-multicore/domainslib/blob/master/lib/task.ml) creates domains during pool setup. Its `async` operation submits a closure and promise to an existing pool; `await` coordinates the result. A pool-based fork therefore has a different cost from creating a fresh domain. Pool startup is a separate measurement-boundary question.
- The [oneTBB chunking guide](https://uxlfoundation.github.io/oneTBB/main/tbb_userguide/Controlling_Chunking_os.html) also warns that excessively small chunks can spend more on overhead than they gain. Its workload-granularity heuristic is not a per-fork cost or a Tick calibration.
- [Zarith](https://github.com/ocaml/Zarith/blob/master/README.md) uses different representations and arithmetic paths for small and large integers. [GMP's multiplication algorithms](https://gmplib.org/manual/Multiplication-Algorithms) and [Fibonacci implementation](https://gmplib.org/manual/Fibonacci-Numbers-Algorithm) further illustrate operand-size-dependent costs and specialized squaring. The project's one-tick arbitrary-natural arithmetic does not capture those differences.

A runtime-based coordination price would require a selected backend, integer representation, hardware, operand sizes, and task-submission/join measurements. No such calibration has been established for this project.

These limitations motivated questions 10 and 11: state the supported overhead conditions explicitly, and require a benefit from parallel execution itself rather than only an improvement over L3. Both are now confirmed.

### Confirmed requirements: round 5

The researcher answered yes to questions ten and eleven. All earlier approvals remain in force except the fixed numerical prices in point 4.

10. Replace one tick each for fork and join with positive, input-independent `fork_cost` and `join_cost`. Emit each charge as repeated ordinary unit ticks, before the children execute and after both complete, respectively. Both charges contribute to accumulated cost and parallel time. The proof must state the overhead conditions under which its speedup claims hold. The model remains abstract; later backend measurements may instantiate these fixed parameters, but no runtime calibration or machine-time speedup is established now.
11. In addition to the comparison with L3, require an eventual uniform constant-factor parallel-time improvement over the **same derived program serialized**. Serialization executes both children sequentially and removes fork/join coordination machinery and its charges. It retains the program's computational work and charges, including function-entry, iteration, arithmetic, and automatic array charges. It is not a separately optimized sequential algorithm.

### Approved consolidated design

**Historical parallel design, superseded by the [approved sequential revision](#approved-sequential-l4-revision).**

The researcher approved this consolidated design on **2026-10-28**. The specification leaves the algorithm and concrete resource witnesses to the derivation within the approved construction constraints. It does not prescribe an algorithm, block width, worker count, or numerical bound constants from a feasibility candidate. The [implementation](#implementation) below records the chosen witnesses and distinguishes checked bookkeeping/array bounds from source-reviewed scalar and closure payload bounds.

#### Behavior, costs, and serialization

For every natural-number input `n`, L4 and its serialization must terminate successfully and return the same exact Fibonacci number `F(n)` as `Fib_L3`. Failed outcomes do not satisfy the contract. Serialization must preserve the computational outcome after disregarding cost; agreement with L3 concerns successful returned values, not identical internal arrays or costs. This is a single-result computation, not a batch of Fibonacci queries.

For a fixed overhead configuration, write:

- `W4(n)` for L4's accumulated cost, including coordination charges;
- `S4(n)` for its longest-chain parallel time, including coordination charges;
- `T3(n)` for L3's exact accumulated cost: `T3(0) = 9` and `T3(n) = 8 + 13 * (Nat.log2 n + 1)` for `n > 0`;
- `Tserial(n)` for the accumulated cost of the same L4 program serialized as in point 11.

Sequential composition adds both resource measures. Independent children contribute the sum of their work and the maximum of their parallel times. Fork and join contribute `fork_cost` and `join_cost` to both measures through ordinary unit ticks. Inline branches incur no additional function-entry charge; all existing computational charging rules still apply.

Serialization retains both children's computations, even when a different sequential algorithm could avoid duplicated work. It removes only the fork/join coordination machinery and charges, not computational charges. Thus the comparison with `Tserial` tests the benefit of overlap in the derived program, while the comparison with `T3` tests improvement over the existing level.

#### Supported overheads and uniform resource obligations

The derivation must state an **explicit, nonempty supported range** of fixed configurations `(fork_cost, join_cost)`, with both parameters positive natural numbers. It must give the actual conditions defining that range and exhibit a positive configuration satisfying them. An unspecified cost predicate, or one with no satisfying configurations, cannot make the speedup obligations vacuously true. This approved requirement did not demand support for every positive configuration; the implemented contract below uses that stronger domain.

For each fixed configuration in that range, the derivation must choose `C > 0`, positive integer ratio witnesses `p3, q3, ps, qs`, and natural-number thresholds `N3, Ns`, with:

```text
0 < p3 < q3                    0 < ps < qs

for every n:      W4(n) <= C * (Nat.log2 n + 1)
for n >= N3:      q3 * S4(n) <= p3 * T3(n)
for n >= Ns:      qs * S4(n) <= ps * Tserial(n)
```

The ratios and thresholds may differ between the two comparisons. A common ratio strictly between zero and one and a common threshold are also sufficient, but not required. Every witness, including the worker budget and storage constants below, must be independent of `n`; witnesses may depend on the fixed overhead configuration. The thresholds limit only the speedup claims: successful termination, behavioral agreement, and the work and storage bounds apply to every input.

#### Scheduling, storage, and construction

- **Scheduling:** choose an input-independent `pool_size` and prove that a schedule within that budget attains `S4(n)` for every input. The budget includes the worker executing the parent. A waiting parent's saved continuation consumes storage without necessarily reserving an execution worker. Longest-chain accounting alone is not this scheduling proof.
- **Storage:** require constant per-worker space and a separate constant shared-storage bound throughout execution. Count queued tasks, saved continuations, and retained results wherever stored. Total modeled storage is at most `pool_size * per_worker_constant + shared_constant`. Prove the array-cell bounds; use the shared-construction discipline and source review for bounded scalar state and task bookkeeping, as at L3. This is not a bit-space or concrete runtime-storage guarantee.
- **First primitive:** use reusable fork/join with two sequential, array-free children operating on local scalar data. Mutable-array operations remain in the parent. Both children return their results at join before the parent continues; the derivation chooses which computations to overlap.
- **Construction:** keep the behavioral and resource specification algorithm-independent. Construct the Fibonacci target inside its `Derive ... in ... as ...` proof, with shared `cost_iter` for target-program loops. Reusable primitives and proof rules belong in the shared library. Any block width or other concrete construction witness is a derivation choice, not a fixed specification requirement.

#### Implementation and verification outline

The approved implementation and verification plan was:

1. Add reusable parallel machinery and proof rules to the shared library, covering charged work, longest-chain time, outcome-preserving serialization, and the required scheduling and array-storage arguments. Retain ordinary unit ticks and reuse the existing charging, array, and iteration machinery; no concrete parallel API is fixed here.
2. Construct `Fib_L4` inside `Derive`, keeping Fibonacci-specific mathematics and invariants with the example. Prove successful all-input termination and agreement with L3 and serialization, the logarithmic work bound, both eventual speedups under the explicit supported overhead conditions, and the scheduling and storage obligations above.
3. Register the sources in the build, extend the executable examples and constructed-term inspection in `theories/Examples.v`, and add the headline L4 theorems and reusable laws to `checks/assumptions.txt`.
4. Run `opam exec --switch=cs2-rocq92 -- make check`: build, executable examples, strict assumption audit, and guardrail regressions. Every audited theorem, including the headline L4 results, must report **“Closed under the global context.”** Source review must also check cost fidelity, bounded scalar state and task bookkeeping, and construction inside `Derive`.

The historical parallel implementation supplied the shared machinery and all-input derivation. Its original integration passed the final gate after review fixes, and both independent follow-up reviews found no remaining actionable issues. Finite examples supplemented the all-input proofs. The verification record below covers that integration; the later extraction also passed its clean integrated gate and completed independent reviews with no actionable issues.

### Implementation

**Historical target source:** `df9797b6a38c645c313b199ee1567627ecdc1773:theories/FibonacciL4.v`. The [current file](../theories/FibonacciL4.v) is sequential and does not contain the parallel contract below. [`theories/Parallel.v`](../theories/Parallel.v) still implements the independent shared effects, interpretations, concrete fixed-pool certificates, and generic resource laws. At the historical snapshot, the target was constructed inside:

```coq
Derive (Fib_L4 : nat -> itree (ParallelE nat) nat) in
  (Spec_L4 Fib_L4) as Fib_L4_spec.
```

#### Actual contract and supported prices

At the historical snapshot, `Spec_L4 program_l4` first quantifies over `prices : Prices` satisfying `supported_l4_prices prices`. That predicate is exactly `0 < fork_cost prices /\ 0 < join_cost prices`: **every positive fixed configuration is supported**, not just a restricted low-overhead range. `supported_l4_prices_nonempty` exhibits `(1, 1)`. The same target program serves every configuration; prices are interpreter arguments, not program inputs.

For each supported configuration, the specification existentially quantifies `time_constant`, `pool_size`, `per_worker_constant`, `shared_constant`, `gain_numerator`, `gain_denominator`, and `threshold`, before quantifying over the computational input. The four resource constants must be positive, and the ratio witnesses must satisfy `0 < gain_numerator < gain_denominator`. The derivation chooses all these witnesses. The implemented contract uses a common ratio and threshold for the two comparisons, which the approved design permits.

For every input, the contract requires:

1. An `eutt` relation between `run_parallel prices (program_l4 input)` and `run_count (Fib_L3 input)`. Both must succeed with equal returned values. Work is at most `time_constant * (Nat.log2 input + 1)`; final array length is at most `shared_constant`. At or above the threshold, parallel time satisfies the chosen constant-factor bound against L3's exact cost.
2. A source-linked `scheduled` certificate whose `schedule_work` equals reported work and whose length equals reported parallel time. Each round respects the worker budget, the per-lane task-record bound, and the shared bookkeeping/array bound described below.
3. A second `eutt` relation with `run_count (serialization (program_l4 input))`. Both must succeed with equal arrays and returned values; the serialized array also satisfies the shared bound. At or above the threshold, parallel time satisfies the same ratio bound against serialized cost.
4. Explicit `all_finite` for both parallel interpretation and counted serialization, for every input.

The relations reject failed outcomes. Agreement with L3 compares returned values without requiring equal arrays or costs; L3's exact cost is the reference for one speedup inequality. Agreement with serialization preserves both the array and returned value, while the resource counters may differ. Thresholds limit only the speedup claims. Correctness, termination, work, and storage obligations apply to all inputs. Neither the algorithm nor the concrete numerical witnesses below appears as a requirement in `Spec_L4`.

The storage relation uses the successful final array length in every round's shared bound. Because canonical array length never decreases, `Spec_L4_intermediate_bound` transfers this bound to canonical residual arrays for any satisfying program. This argument does not claim a bound on an arbitrary runtime heap.

#### Shared interfaces and proof rules

These shared interfaces remain current. The descriptions of their use by L4 in this subsection refer to the historical parallel target.

`ParallelE A = ArrayE A +' (ForkEvent +' TimeE)` permits array operations and ordinary ticks in the parent. A `Fork left right` event carries two sequential `TimeE` computations and returns their pair of results. The child types exclude nested forks and mutable-array events. `fork` emits that event; `lift_serial` embeds an existing array/time computation in the parent effect type.

`run_parent_from` reuses the canonical array handler and its automatic charges, leaving fork and time events for the resource interpretation. `run_parallel_from prices program array (work, span)` then tracks accumulated work and parallel time; `run_parallel prices program` starts from an empty array and `(0, 0)`. Its result is `((work, span), outcome)`, with `outcome = None` on array failure or `Some (array, result)` on success. Failure keeps the attempted access charge and skips the continuation.

The parallel fork handler counts `unit_ticks (fork_cost prices)` before the children and `unit_ticks (join_cost prices)` after them. These are repeated ordinary ticks, not weighted events or target-chosen cost totals. For counted child costs `wl` and `wr`, work increases by `fork_cost + wl + wr + join_cost`, and parallel time by `fork_cost + max(wl, wr) + join_cost`. Every ordinary parent or array-handler tick adds one to both measures.

`serialization` interprets the same fork event as left-then-right child execution without coordination machinery or its ticks. It preserves computational ticks, array charges, and duplicated child arithmetic. Because the parallel handler owns the coordination charges, serialization removes them by interpreting the fork event differently, without removing any target tick. `run_count (serialization program)` observes the serialized cost. This is not tick ignoring or a separately optimized sequential algorithm.

The shared laws include:

- `unit_ticks_exact`, `parallel_branch_accounting`, `serial_branch_accounting`, and `branch_outcome_agreement` for exact charges and child-result agreement;
- `run_parallel_lift_serial_leaf` for reusing canonical serial execution witnesses, including failures;
- `serial_fork_serial_trace` and `serial_fork_serial_execution_exact` for composing successful serial prefixes, children, and suffixes into exact parallel/serialized leaves and a schedule on the canonical named trace; the existential `serial_fork_serial_execution` remains a compatibility wrapper, and `serial_fork_serial_outcome` proves array/value agreement;
- `pool_execution_accounting`, `scheduled_attains`, and `scheduled_matches_leaf` for connecting source-linked schedule certificates to the interpreted work and parallel time;
- `scheduled_pool_budget`, `scheduled_worker_bookkeeping`, and `two_lane_storage_bound` for worker and bookkeeping bounds;
- `parallel_final_bound_subtree_leaf`, `parallel_final_bound_handler_subtree_leaf`, and `parallel_waiting_array_bound` for canonical residual arrays, pending parent-handler prefixes, and the unchanged array during child and coordination execution.

`Cost.v` supplies `count_cost_iter_step` and `count_cost_iter_rank_invariant` for array-free `TimeE` loops. The invariant has type `nat -> State -> Prop`; the rank exists only in the proof. Both continuing and terminal body obligations start at `S cost`, so `step_cost` and `exit_cost` include the iteration-entry charge. The rule concludes exact cost `cost + step_cost * remaining + exit_cost`.

`Cost.v` also owns the generic `interp_leaf_source`, `interp_state_leaf_source`, `count_offset`, and `count_shift_leaf` facts moved from `Parallel.v`, without new imports or dependencies. These laws recover source leaves or shift initial counters while preserving results. The shared laws establish helper behavior, not universal cost fidelity or scalar payload bounds for arbitrary raw ITree/Gallina programs.

`Binary.v` owns the proof-only `binary_mask` and `mask_scan_cost` witnesses, the all-input `mask_count_all` scan rule, and `binary_prefix_rank_step` for the pure control step through the last bit. L3 and L4 reuse these rules; their Fibonacci-specific data invariants and arithmetic remain local. The targets still compute their masks in charged loops rather than call the witnesses.

L4 composes its execution evidence through one helper, `fib_l4_program_execution`. The helper applies `serial_fork_serial_execution_exact` to the parent prefix, the two children, and the parent suffix, then retains its `Hscheduled` witness directly instead of rebuilding the schedule locally. The construction declaration above remains unchanged: its goal is `Spec_L4 Fib_L4`, with exact execution evidence local to the proof rather than added to the specification. After `Derive`, `Fib_L4_execution` packages the exact parallel leaf, serialized leaf, and named canonical trace. `Fib_L4_leaf`, `Fib_L4_serial_leaf`, and `Fib_L4_scheduled` project that evidence; the counted equations follow from the leaves.

#### Chosen construction and duplicated work

The derivation chooses **one coarse fork for the whole bit scan**, rather than one fork per bit or block. This pays the fixed coordination overhead once, allowing the growing child computations to amortize every fixed positive price configuration in the abstract model.

The target performs these steps:

1. The parent enters through `function_entry`, allocates two array cells, and initializes them to `0` and `1`. Its charged `cost_iter` mask loop halves a quotient and doubles a mask; input zero produces mask zero. The parent then reads the initial pair.
2. Two inline, array-free `TimeE` children each run a `cost_iter` over the input bits. Each carries exactly four loop-state scalars: remaining input, mask, and the adjacent Fibonacci pair `(a, b)`. Both children update the full pair with the same arithmetic; only their terminal return differs. The left returns `F(n)`, and the right returns `F(n + 1)`.
3. After join, the parent stores the two returned coordinates in its array and reads the first cell as the result. All mutable-array operations remain in the parent.

For `a = F(k)` and `b = F(k + 1)`, each child's bit-specific arithmetic is:

```text
bit 0: c = a * ((b + b) - a); d = a * a + b * b; next pair = (c, d)
bit 1: d = a * a + b * b; e = b * ((a + a) + b); next pair = (d, e)
```

Each branch uses six charged data-arithmetic operations per bit. The iteration-entry tick covers comparisons, remaining-input updates, and mask halving. The terminal body costs one entry tick. Inline children receive no extra function-entry tick merely for being branches. The mask-building scan is explicit charged computation; the target calls no earlier Fibonacci implementation, specification-only cost function, `Nat.log2`, or `Nat.pow`.

**Both children duplicate the full pair calculation.** They do not split its arithmetic into disjoint halves. Their same-program serialization retains this duplication, as the approved comparison requires. The proved improvement over that serialization establishes a benefit from overlap in this particular program. It does not establish improvement over a sequential implementation that computes each pair once, over the best sequential Fibonacci algorithm, or in runtime wall-clock measurements.

The children also carry persistent Fibonacci pairs as scalars, unlike L3's array-based pair. Thus the comparison with L3 changes the storage allowances as well as execution order. The sequential replacement restores L3's array-storage discipline; it does not claim to be the optimal sequential control.

#### Exact resources and derivation witnesses

Let `h = fork_cost prices + join_cost prices`. For positive input `n`, let `L = Nat.log2 n + 1`. `Fib_L4_leaf` and `Fib_L4_count` prove the exact parallel outcome; `Fib_L4_serial_leaf` and `Fib_L4_serial_count` prove the exact serialized outcome:

```text
final array: [Some (Fib_L0 n); Some (Fib_L0 (S n))]
result:      Fib_L0 n
```

| Input | Parent prefix | Each child | Parent suffix | Work | Parallel time | Serialized cost |
| --- | --- | --- | --- | --- | --- | --- |
| `0` | `9` | `1` | `3` | `14 + h` | `13 + h` | `14` |
| `n > 0` | `8 + L` | `7 * L + 1` | `3` | `13 + 15 * L + h` | `12 + 8 * L + h` | `13 + 15 * L` |

The local proof witness `fib_l4_prefix_cost input` is now `8 + mask_scan_cost input`, definitionally equal to its former zero/positive formula. The shared `binary_mask` replaces `fib_l4_mask`. These proof changes leave every exact cost above unchanged.

`fib_l4_work_bound` proves the all-input bound `W4(n) <= (28 + h) * (Nat.log2 n + 1)`. The derivation chooses:

| Witness | Value |
| --- | --- |
| `time_constant` | `28 + h` |
| `pool_size` | `2` |
| `per_worker_constant` | `1` task record per lane |
| `shared_constant` | `32` bookkeeping/array units |
| `gain_numerator`, `gain_denominator` | `3`, `4` |
| `threshold` | `2 ^ (4 * (h + 5))` |

`Fib_L4_eventual_speedups` proves both `4 * S4(n) <= 3 * T3(n)` and `4 * S4(n) <= 3 * Tserial(n)` at or above this threshold for every supported price configuration. The common ratio is **`3/4`**. These are sufficient proof witnesses, not optimal constants or measured runtime crossover points. `Fib_L4_terminates` and `Fib_L4_serial_terminates` expose the all-input termination results separately.

For example, prices `(2, 3)` and input `10` give result `55` and array `[Some 55; Some 89]`, with work `78`, parallel time `49`, and serialization cost `73`; L3's cost is `60`. This small sample illustrates the exact formulas, not the eventual `3/4` bound.

#### Concrete fixed-pool certificate

The production `scheduled` predicate is defined through `pool_execution prices (run_parent_from program array) trace outcome`. Unlike the temporary probe's abstract scheduling predicate, each constructor refers to the executed source. In particular, `PoolFork` requires canonical counted executions of the actual two children; numerical work/span inequalities alone cannot construct a certificate.

The schedule uses two lanes. Worker zero executes the parent prefix, pays fork coordination, and executes the left child. Worker one executes the right child. The waiting parent saves its continuation instead of reserving a third worker. Both children are sequential, so simultaneous execution of their tick streams takes the maximum of their counted costs. After both finish, worker zero pays join coordination and resumes the parent suffix. `Tau` and dispatch transitions cost no ticks in this abstract schedule; there is no claim that a runtime performs them for free.

`Fib_L4_scheduled` supplies this source-linked trace. `Fib_L4_pool_attains` proves its `schedule_work` equals `fib_l4_work h input`, its length equals `fib_l4_span h input`, and every round fits the two-worker budget. Eager dispatch uses zero queued children, satisfying the library's at-most-one queued-child bound. At most one parent continuation and one fork frame remain open.

The trace lists are **proof-only certificates**, not target-memory allocations or an executable backend scheduler. Their input-dependent length does not mean the target stores an input-sized execution history. Conversely, proving trace attainability alone does not prove a bound on the payload of a task closure or result.

#### What the storage proof establishes

The checked per-worker bound concerns `worker_bookkeeping`, the length of a lane's list of payload-free task-record states. A lane reuses one record: `RunningTask` while executing, or `RetainedResult` after its child finishes and before join. `completed_child_retains_record` explicitly distinguishes occupied execution slots from stored result records. Thus **`per_worker_constant = 1` counts records, not scalars, closure payloads, or bytes**.

The shared bound counts:

```text
length array + queued_children round + saved_continuations round
  + 2 * open_fork_frames round <= 32
```

The last term reserves two bookkeeping slots per open frame; it does not mean two open forks. The canonical parent array has at most **two cells**, allocated once. The shared constant is a conservative upper bound, not a claim that the program allocates a 32-cell array.

`Fib_L4_intermediate_bound` bounds every canonical residual parent array by two cells. Applying the shared `parallel_final_bound_handler_subtree_leaf` to `Fib_L4_leaf` also bounds incoming arrays during pending allocation/read/set ticks. `parallel_waiting_array_bound` covers the retained parent array while fork/join handlers and children run; those computations cannot change it. `Fib_L4_serial_intermediate_bound` gives the serialized residual-array bound.

`Fib_L4_worker_bookkeeping` bounds each lane's record count. `Fib_L4_modeled_storage` combines any reachable canonical residual array with any round of the certified schedule, conservatively proving **`2 * 1 + 32 = 34` bookkeeping/array units**. These theorems do not bound total bytes or the sizes of values stored in the counted cells and records.

Each child carries four scalar loop-state values and uses a fixed number of arithmetic temporaries. The source also has two fixed child closures/results and one saved parent continuation; none accumulates across iterations. Both independent reviews of the original L4 integration confirmed this fixed scalar and closure structure and the charging discipline. This historical source-review assurance is not a universal machine-checked scalar-payload bound; growing natural-number bit sizes remain outside the unit-cost, array-cell model. The completed extraction reviews confirmed preservation of the target bodies and resource guarantees.

### Implementation verification

**Historical baseline: `3a29285aac7767560a712494d73c38367d51b642`.** On **2026-10-28**, the original L4 integration completed verification and independent review. Its all-input correctness, exact resources, serialization, termination, schedule attainability, and bookkeeping/array proofs were closed. The results below cover that implementation, not the follow-up extraction.

- **Clean build: passed.** All nine modules compiled after `opam exec --switch=cs2-rocq92 -- make clean`, before the review-driven cleanup.
- **Post-review build and integrated gate: passed.** After the fixes, the incremental build recorded 2.07 seconds for `Parallel.v`, 0.75 seconds for `FibonacciL4.v`, and 0.69 seconds for `Examples.v`. The final `opam exec --switch=cs2-rocq92 -- make check` replayed the executable observations and constructed terms, audited all **97** manifest declarations as **“Closed under the global context,”** and passed all **45** guardrail tests. The audited declarations include the new combined `Fib_L4_execution` theorem.

#### Independent implementation review

Both reviews covered the complete working-tree change relative to **`31d68361c006c2a656b6c434cbe68d7209146dfd`**, including all untracked L4 files. The review base remained fixed through the fixes and follow-up reviews.

The initial standards review reported two hard violations and one heuristic issue. All three were resolved:

| Finding | Resolution |
| --- | --- |
| Hard: explicit event-sum syntax did not follow the notation convention | Used `SumNotations` for explicit event-sum injections. |
| Hard: stale assurance status | Updated current verification and review records to the completed results, while retaining the source-review assurance boundary. |
| Heuristic: repeated proof composition | Consolidated composition in `fib_l4_program_execution` using the shared `serial_fork_serial_execution` rule; public results reuse `Fib_L4_execution`. The `Derive ... in (Spec_L4 Fib_L4) as Fib_L4_spec` construction goal remains unchanged. |

The standards follow-up found **zero remaining actionable issues**. Independent specification review found **zero issues** both initially and on follow-up. Both reviews confirmed construction inside `Derive`, correct charge placement without omitted or duplicate charges, no hidden calls to Fibonacci references or `Nat.log2`/`Nat.pow`, and the fixed scalar/closure structure. They retained the distinction between the checked task-record/array bounds and source-reviewed payload structure; neither review establishes a payload-size theorem or runtime speedup.

The [README verification status](../README.md#l4-verification-status) separates these historical results, the later extraction's completed checks, and the sequential replacement's passing clean gate and completed independent reviews. Historical L1–L3 integrated passes and reviews remain valid for those baselines; the probe limitations below remain historical.

### Shared-proof extraction

**Historical scope:** this extraction produced the parallel-L4 baseline at `df9797b6a38c645c313b199ee1567627ecdc1773`. Its preservation requirements and completed checks below apply to that refactor, not to the later approved sequential replacement. The extracted generic library laws remain current.

**Approval:** the researcher approved four follow-up extractions on **2026-10-28**, after commit **`3a29285aac7767560a712494d73c38367d51b642`**. That commit is the fixed baseline for independent review. This section is the refactor specification; it adds no algorithm requirement or runtime-model change.

**Status:** implementation, clean integrated gate, and independent reviews **complete**. The clean gate passed on **2026-10-28**, with all **104** manifest declarations, seven more than the historical 97, closed under the global context. Standards review found zero documented violations and zero actionable smells; specification/proof review found zero findings. Only documentation status metadata changed after review.

#### Approved scope and source ownership

1. **All-input mask rule in `Binary.v`.** Keep `binary_mask` and `mask_scan_cost` as proof-only witnesses: at zero they are `0` and `1`; at positive input they are `2 ^ Nat.log2 input` and `Nat.log2 input + 1`. `mask_count_all` must accept any body satisfying `mask_body_rule`, any input and scale, any array of any cell type, and any starting counter. It preserves the array, returns `scale * binary_mask input`, and adds exactly `mask_scan_cost input` ticks. L3's `fib_l3_program_count` applies this rule once before its Fibonacci-specific input split; L4's `fib_l4_prefix_count` uses it without an input case split. Remove `fib_l4_mask` in favor of `binary_mask`; retain `fib_l4_prefix_cost input` as `8 + mask_scan_cost input`, definitionally equal to the old formula. Keep `mask_count` and `mask_zero` available.
2. **Ranked control step in `Binary.v`.** `binary_prefix_rank_step` packages mask positivity, halving, and the processed-prefix invariant, including the last-bit transition to rank zero. Both `fib_l3_doubling_count` and `fib_l4_child_count` use this level-neutral rule. Fibonacci data invariants and arithmetic stay in their example modules; rank and prefix remain proof data rather than new loop state.
3. **Exact trace composition in `Parallel.v`.** `serial_fork_serial_trace prices prefix wl wr suffix` names the existing concatenation `repeat ParentRound prefix ++ (fork_rounds prices wl wr ++ repeat ParentRound suffix)`. `serial_fork_serial_execution_exact` exposes its schedule certificate and the same exact parallel/serialized leaves as the existing rule. Retain `serial_fork_serial_execution` as an existential compatibility wrapper. L4's `fib_l4_program_execution` retains `Hscheduled` directly and removes local schedule reassembly. All six explicit L4 trace occurrences use the shared name, including the local execution evidence and the public execution, schedule, and storage statements.
4. **Generic facts in `Cost.v`.** Move `interp_leaf_source`, `interp_state_leaf_source`, `count_offset`, and `count_shift_leaf` out of `Parallel.v`, preserving their statements. The first pair recovers source leaves from interpreted leaves; the second shifts counters without changing results. Add no imports or upstream dependencies to `Cost.v`.

The implementation touches `Cost.v`, `Binary.v`, `Parallel.v`, `FibonacciL3.v`, and `FibonacciL4.v`. The manifest adds `interp_leaf_source`, `interp_state_leaf_source`, `count_offset`, `count_shift_leaf`, `mask_count_all`, `binary_prefix_rank_step`, and `serial_fork_serial_execution_exact`. The accompanying documentation changes belong in this record, the README, and the cost conventions.

#### Clean integrated gate

On **2026-10-28**, `opam exec --switch=cs2-rocq92 -- make clean` completed, followed by a passing `opam exec --switch=cs2-rocq92 -- make check` with `TIMED=1` and `TMPDIR` set to the approved temporary directory. All **nine** modules compiled; executable examples and constructed terms replayed; all **104** registered declarations reported **“Closed under the global context”**; and all **45** guardrail tests passed.

| File | Compilation time (seconds) |
| --- | --- |
| `Cost.v` | `0.67` |
| `Array.v` | `2.12` |
| `Parallel.v` | `2.04` |
| `Binary.v` | `0.43` |
| `Fibonacci.v` | `0.41` |
| `FibonacciL2.v` | `0.46` |
| `FibonacciL3.v` | `0.58` |
| `FibonacciL4.v` | `0.76` |
| `Examples.v` | `0.72` |

#### Preservation requirements

The extraction must preserve every target computational body, every `Spec_L*` contract, construction inside `Derive`, charge placement, and exact cost. It must also preserve returned values and arrays, serialization behavior, supported prices, schedule meaning, and resource witnesses. Existing L3/L4 theorem statements must remain definitionally equivalent after unfolding the witnesses and named trace. These helpers remain proof data, not executable shortcuts or target allocations. The checked bookkeeping/array bounds and source-reviewed scalar/closure bounds retain their existing assurance boundary.

#### Independent extraction reviews

Both independent reviews covered the complete **nine-file working-tree diff** against **`3a29285aac7767560a712494d73c38367d51b642`**, using the refactor specification above. The scope comprised the five source modules, the assumption manifest, and these three documentation files. Both accepted the clean integrated gate, including executable example and constructed-term replay, **104** closed assumption reports, and **45** passing guardrail tests.

- **Standards review: complete.** **Zero documented violations and zero actionable smells.**
- **Specification/proof review: complete.** **Zero findings.**

Both reviews confirmed exactly seven manifest additions and preservation of target computational bodies, `Spec_L*` contracts, handlers, exact costs, and resource guarantees. They confirmed that the shared helpers are used in the actual L3/L4 proofs and that `fib_l4_program_execution` retains `Hscheduled` directly; all six explicit L4 trace occurrences use the shared named trace.

Within that refactor, no source or manifest changes followed review; only documentation status metadata was updated before the baseline commit. The completed gate and reviews retain the distinction between checked bookkeeping/array bounds and source-reviewed scalar/closure structure. They do not establish a runtime speedup. The original **97-entry** L4 audit and reviews above remain a separate historical record.

### Historical feasibility evidence

The temporary Rocq probes recorded below compiled in the `cs2-rocq92` switch on 2026-10-28, before the historical parallel implementation. Their source files lived outside the repository under the session's temporary directory. These results preserve feasibility evidence and its limitations at the time, not verification of either production target. Fixed one-tick fork/join prices below are historical test configurations, not the general shared-library policy.

#### Unit-tick accounting

`ForkJoinFeasibility20261028.v` checks a bounded, deterministic accounting layer over existing `TimeE` computations. Two independent one-tick arithmetic operations have accumulated cost `2` and parallel time `1` before coordination overhead. A dependent two-operation sequence has both measures equal to `2`. A branch using the existing `cost_iter` also evaluates successfully.

The checked accounting formula adds ordinary unit-tick fork and join charges to both measures, sums child accumulated costs, and takes the maximum of child parallel times. This probe does not provide a recursive parallel-effects interpreter, a finite-processor scheduler, or shared mutable branch state. Its four audited generic lemmas report “Closed under the global context.”

#### Fibonacci resource candidate

`L4ForkFeasibility20261028.v` typechecks a candidate constructed inside `Derive`, reusing the canonical array handler, charged arithmetic, and `cost_iter`. Its parallel children perform arithmetic only; all array access remains sequential. This is an available feasibility candidate, not an algorithm requirement.

The candidate exposes two independent three-operation arithmetic chains within each bit step. With inline child computations and no extra task-entry charges, a continuing step has accumulated cost `12 + h` and parallel time `9 + h`, where `h` is the combined fork/join overhead. For positive input, writing `L = Nat.log2 input + 1`, its candidate formulas are:

```text
accumulated cost = 8 + (13 + h) * L
parallel time   = 8 + (10 + h) * L
```

The candidate evaluates successfully against L3 on inputs `0, 1, 2, 3, 4, 5, 7, 8, 10, 15, 16`, including matching returned values and final arrays. Historical tests used both zero coordination overhead and one tick each for fork and join. For input `10`, L3's accumulated cost is `60`; the candidate gives accumulated cost/parallel time `60/48` with free coordination and `68/56` with the two coordination ticks. All three cases return `55`. At input zero, each has cost and parallel time `9`. The free-coordination case is diagnostic only: it is outside round 5's requirement that both overhead parameters be positive.

The probe proves child arithmetic charges for all operands and checks the proposed cost-formula comparisons. It did not prove the candidate's all-input correctness, termination, or execution-to-resource-formula theorems. Seven audited assumptions reports were closed under the global context. These are abstract accounting experiments, not multicore runtime measurements.

Adding an extra entry tick to each child, in addition to the historical one-tick fork and one-tick join, would remove this candidate's parallel-time advantage. Round 2 settled the policy that an inline branch has no extra function-entry tick. Round 5 changes the coordination prices, not this entry-charge rule.

The candidate's proposed work and parallel-time formulas are logarithmic. Parallelizing each bit step does not remove the dependency between successive steps or the charged mask-building scan. No sublogarithmic candidate has been established.

#### Fixed-pool and storage audit

The candidate's shallow fork admits a schedule using two total workers: one saves the parent continuation and executes one child, while the other executes the second child. After joining, the first worker resumes the parent. Each fork joins before the next iteration, so at most one child needs queuing and one parent continuation needs saving. Reusing or discarding completed task records keeps their storage bounded.

With the historical configuration `fork_cost = join_cost = 1`, a continuing step has accumulated cost `14` and parallel time `11`. Its proposed formulas for positive inputs become `8 + 15 * L` and `8 + 12 * L`. These formulas satisfy a uniform constant-factor comparison: `21 * (8 + 12 * L) <= 20 * (8 + 13 * L)` for `L >= 1`. The particular constants and the two-worker schedule remain feasibility witnesses, not specification requirements.

A temporary schedule calculation checked 196 child-length/pool cases and 128 bit-count cases. The original Rocq candidate also replayed successfully. At that stage, no concrete finite-pool semantics or all-input scheduling theorem had been integrated.

For this schedule, a waiting parent must release its worker or execute one child itself. If it occupies one of two workers while both children are queued, only one worker remains to execute the children, losing the overlap. More generally, longest-path accounting alone does not establish that a particular fixed pool can attain that time.

The candidate keeps the canonical two-cell array under parent control. Its children use only charged arithmetic and scalar results. A per-thread bound can count those cells against the parent, or a separate shared-array bound can count them once. Fixed worker count alone does not bound queued tasks, saved continuations, or retained results; the storage contract must say how these are covered. Canonical arrays are append-only, so allocating fresh task cells each iteration would also violate a constant array-length bound despite bounded live concurrency.

#### Coordination-price sensitivity

`L4ForkPriceProbe20261028.v` compiled temporary bit-specific and fixed-block candidates using configurable ordinary unit-tick coordination charges. It checked 594 observations against the proposed metrics and L3's returned values and arrays. Twenty audited assumptions reports were closed under the global context. Separate calculations checked 6,664 larger exact-value/resource cases and 448 two-worker schedules. The all-input execution-to-formula and finite-pool scheduling proofs remained outstanding for these probes.

Let `h` be total fork-plus-join overhead and `L = Nat.log2 input + 1` for positive input. A bit-specific candidate computes only the pair needed for the current input bit, using two independent three-operation children and no post-join arithmetic. Its proposed formulas are:

```text
accumulated cost = 8 + (12 + h) * L
parallel time   = 8 + (9 + h) * L
```

Thus its proposed parallel-time formula can still beat L3's `8 + 13 * L` when `h = 3`, extending the original candidate's tolerance. A sequential version of this bit-specific computation already costs `8 + 12 * L`; at `h = 3` its parallel version ties that sequential version. This demonstrates why round 5 adds the serialization comparison: improving on L3 alone does not establish a benefit from overlapping the derived program's branches.

A fixed-block candidate has proposed parallel time `8 + 8 * L + (h + 2) * B`, where `B = ceil(L / k)` and fixed block width `k` is independent of input. Its formulas permit eventual improvement over L3 for any fixed finite `h`, by choosing `k` large enough. However, its children duplicate intermediate arithmetic. A sequential blocked control that computes each intermediate pair once costs `8 + 8 * L + 5 * B`, so the parallel candidate is no faster than that control when `h >= 3`. Larger tolerated coordination prices therefore do not establish that expensive forks are worthwhile against the stronger sequential control.

That stronger blocked control is **not** the same-program serialization required by point 11: it avoids duplicated arithmetic that serialization must retain. The comparison remains useful evidence, but beating that separately optimized control is not an additional approved requirement.

These candidates establish abstract sensitivity and explain the two approved comparisons. They do not calibrate runtime prices, prescribe an algorithm or block width for the final derivation, or discharge the consolidated all-input contract.

#### Automatic coordination charges and relational contract

`L4AutomaticForkSpec20261028.v` compiled a temporary handler-level probe for the round-5 policy. Its fork event contains two sequential `TimeE` children. The parallel interpretation inserts the configured coordination charges as ordinary unit ticks; serialization interprets the same event as sequential child execution without those charges. Ordinary parent and child ticks and canonical array charges remain intact. Keeping coordination charges in the fork interpretation lets serialization distinguish them from computational ticks.

The probe proves generic branch work, longest-chain time, serialization cost, and branch-outcome agreement using canonical counted child witnesses. A complete arithmetic-and-array fixture with test prices `fork_cost = 2` and `join_cost = 3` returns `25` and array `[Some 25]` under both interpretations. Parallel work/time are `13/12`; serialization costs `8`, removing exactly the five coordination ticks. The fixture is a semantic check, not a speedup example. Failure fixtures also preserve the charged invalid-read outcome.

The draft relational `Spec_L4` typechecks against these handlers, using `eutt` comparisons with both `run_count (Fib_L3 input)` and the counted serialization, explicit finiteness, logarithmic work, and eventual speedup inequalities. Its supported-price declaration requires a nonempty positive domain. Twenty audited assumptions reports are closed under the global context.

The scheduling obligation in this probe remained a schema predicate; concrete fixed-pool semantics and their attainability theorem still required implementation at that stage. Whole-program outcome agreement and transfer of array bounds to parallel intermediate states also remained unproved. No Fibonacci target instantiated this temporary specification. The probe checked the accounting and specification interfaces needed for the consolidated design; the historical parallel implementation later supplied the concrete schedule predicate and all-input derivation.
