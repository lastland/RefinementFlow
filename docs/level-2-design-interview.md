# Level 2 Design Interview

The researcher approved the consolidated design on 2026-10-28. The implementation provides shared time and array libraries, the revised L1 derivation, and the L2 derivation. The clean build, executable examples, and assumption audit pass. Independent standards and specification reviews found no issues.

## Confirmed requirements

- Construct `Fib_L2` through `Derive`.
- Base `Spec_L2` on `Fib_L1` as its behavioral reference, rather than directly on `Fib_L0`.
- Use an ITree computation with mutable state representing a mutable array.
- Expose allocation, read, and set events, with no deallocation. Use a canonical interpretation whose array length is nondecreasing, so the space obligation can be checked on the final state of a terminating execution.
- Have `alloc size` extend the current flat array by `size` cells, retain all existing cells, and return the old array length as the starting index of the newly allocated cells.
- Make the array interface polymorphic in its element type `A`, with cells of type `option A`. Allocation appends `None` cells to represent allocated but uninitialized storage; these cells count toward array length.
- Give `read` result type `A`, not `option A`. Interpret the array events into state and option effects: an uninitialized read or an out-of-bounds access aborts the interpreted computation with `None`; a successful read supplies the stored value directly.
- Use `ITree.iter` to drive the computation.
- Use the abstract unit-cost, array-cell model: arithmetic and indexed array operations have constant abstract cost, and space counts array entries rather than their bit storage.
- Bound total accumulated cost by `time_constant * (input + 1)` for a constant independent of `input`.
- Bound mutable-array length by `space_constant * (input + 1)` at every reachable state, for a constant independent of `input`.
- Make this all-execution-points array-length bound a Rocq-checked obligation of `Spec_L2`, required by the derivation.
- Leave the array's contents and the iteration algorithm unspecified. In particular, retaining all Fibonacci values from index zero through the input is not required; the linear space requirement is an upper bound.
- Separate reusable array code, formalization, and generic theorems from the Fibonacci example.
- Have the canonical interpreter own the accumulated-time counter. Raw computations return their result rather than choosing a reported cost.
- Use a common abstract time effect for Level 1 and Level 2 with exactly one constructor, `Tick : TimeE unit`, and a unit `tick` operation. Each event contributes exactly one under canonical counting; the event carries no numeric amount.
- Have the canonical array interpreter automatically emit `size + 1` unit ticks for `alloc size`, and one unit tick for each read or set attempt, including failed attempts. Allocation charges one operation tick plus one tick per new cell.
- For L2, emit one explicit tick at function entry, one at each `iter` body entry including its terminating invocation, and one per arithmetic operation on data values. The iteration-entry tick covers comparisons, index maintenance, and branching.
- Make the charging discipline reusable as general project rules for future examples, with common-library support rather than repeating the mechanics in each example.
- Apply those uniform rules to L1 as well, replacing its original invocation-only measure with function-entry and data-arithmetic costs. Its revised naive-recursive cost remains bounded by `2^input`.
- Compare L1 and L2 by equality of returned values, with independent linear time and space bounds for L2. The relation rejects failure and does not compare the two accumulated costs.
- Use consistent argument names: level-neutral names in common code, descriptive `_l1` and `_l2` names in the cross-level relation, and `time_constant` and `space_constant` for the uniform bound constants.

The researcher approved the resource model and added the `iter` requirement. The use of `input + 1` accommodates initialization and input zero. These requirements concern abstract operations and array cells, rather than the concrete execution cost of Rocq arithmetic or a particular array representation.

The approved project-wide charging rules are maintained in [the cost conventions](agents/cost-conventions.md) and linked from the root `AGENTS.md`.

## Approved consolidated design

The researcher approved the public interfaces, Derive declarations, source layout, and assurance scope below before implementation began.

## Monotone-space formulation

The researcher proposed replacing the direct reachability clause with allocation, read, and set events and no deallocation. Under the canonical interpretation, allocation must retain existing cells, and reads and sets must preserve array length. Consequently, the final array length of a terminating execution bounds all intermediate lengths.

This approach requires a reusable checked monotonicity argument for the interpreter. Each derived program can then establish the final space bound and termination, without a separate `Reachable` clause in its specification. All-input termination is essential to this reduction: a final-state postcondition alone does not constrain a divergent computation.

The common-library theorems `final_bound_subtree` and `final_bound_handler_subtree` establish this implication using the existing ITree `Subtree.subtree` relation on canonically interpreted computations. They cover canonical residual executions and handler prefixes, including unchanged array state during handler ticks. `Spec_L2_intermediate_bound` derives the intermediate-length bound from `Spec_L2`. The specification therefore needs no additional reachability predicate or per-example space invariant.

The failure result belongs to the canonical interpretation; raw reads return values of type `A`. A closed executable projection can discard the final cells and ignore time after the specification has inspected them.

The researcher approved allocation extending one flat array by the requested number of cells and returning their starting index, the old array length. The researcher then replaced the zero-initialization proposal with polymorphic `option A` cells initialized to `None`. The illustrative state representation is therefore `list (option A)`, with allocation appending `repeat None size`. Allocation emits `size + 1` ticks, including one tick when `size = 0`.

## L1-based relational specification

After migrating Level 1 to raw time events, canonical counting produces `(cost, result)` for Level 1 and `(cost, option (final_cells, result))` for Level 2. The researcher approved equality of returned values with independent linear resource bounds for Level 2. The specification is recorded with consistent argument names below:

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
        (run_count (program_l2 input))
        (count (Fib_L1 input)) /\
      all_finite (run_count (program_l2 input)).
```

Correctness relative to Level 0 follows through Level 1's established correctness. The relation rejects `None` and intentionally leaves `cost_l1` unconstrained. The approved contract retains explicit finiteness; the relational clause can discharge it using L1's checked termination theorem. The implementation also proves finiteness directly from its exact return theorem.

Common-library arguments remain level-neutral, such as `program`, `array`, `size`, `index`, and `value`. The cross-level specification uses the `_l1` and `_l2` suffixes consistently. These names distinguish a successful `result` from an optional `outcome` without placing Fibonacci-specific names in common code.

## Common library and Fibonacci example

The implemented module responsibilities are:

| Common library | Fibonacci example |
| --- | --- |
| Polymorphic array events and their canonical state/option interpretation | The L1-based Level 2 specification and `Derive` construction |
| Allocation growth and returned-index laws; initialized-read, uninitialized-read, and invalid-access behavior | The chosen `iter` implementation and its loop invariant |
| Successful read/set length preservation and allocation monotonicity | Successful execution, functional correctness, and termination of `Fib_L2` |
| A reusable theorem deriving the intermediate-length guarantee from monotonicity, successful termination, and a final bound | Application of that theorem with the Fibonacci input-dependent space bound |
| Interpreter-owned time accounting and generic accumulation laws | Charge placement for the example's non-array work and concrete linear-bound witnesses |
| Shared function-entry, iteration-entry, and primitive-arithmetic combinators | Consistent use of those combinators in the derived algorithm |

The Fibonacci module imports the common module. The common module depends only on generic library infrastructure and is polymorphic in the cell and result types. Fibonacci reference functions, recurrences, and input-dependent linear constants belong with the example.

Existing ITree iteration, interpreter, postcondition, and finiteness support should be reused. Additional generic helper lemmas belong in the common module when the derivation needs them.

### Source layout

- `theories/Cost.v`: singleton time effect, shared charging combinators, counting and tick-ignoring interpretations, and generic cost laws.
- `theories/Array.v`: polymorphic array events, canonical state/option interpretation emitting time events, and generic array and monotone-space theorems.
- `theories/Fibonacci.v`: Level 0 reference, revised L1 cost specification, `Spec_L1`, the migrated `Fib_L1` derivation, and L1-specific proofs.
- `theories/FibonacciL2.v`: `Spec_L2`, the `Fib_L2` derivation, its chosen loop invariant, and L2-specific proofs.
- `theories/Examples.v`: executable observations and assumption checks for both levels and shared machinery.

### Interfaces and construction constraints

The array-event interface is polymorphic in `A`; the constructor names below avoid Rocq's reserved `Set` keyword:

```coq
Variant ArrayE (A : Type) : Type -> Type :=
| ArrayAlloc : nat -> ArrayE A nat
| ArrayRead : nat -> ArrayE A A
| ArraySet : nat -> A -> ArrayE A unit.
```

The target declarations are:

```coq
Derive (Fib_L1 : nat -> itree TimeE nat) in
  (Spec_L1 Fib_L1) as Fib_L1_spec.

Derive (Fib_L2 : nat -> itree (ArrayE nat +' TimeE) nat) in
  (Spec_L2 Fib_L2) as Fib_L2_spec.
```

The unknown targets are constructed during their Derive proofs. L1 retains its naive recursive algorithm. L2 uses the shared charged iteration combinator and genuine mutable-array operations; its algorithm and retained array contents remain implementation choices. Reference programs and specification-only cost recurrences may guide specifications and proofs, while the computational target obtains results through its own charged operations.

### Assurance and verification scope

Rocq checks result correctness, successful execution, termination, uniform resource bounds, the generic intermediate-space consequence, canonical interpreter laws, and preservation of outcomes when ticks are ignored. Source review checks compliance with shared charging operations, complete and nonduplicated charge placement, reference-function independence, and the required construction mechanisms. This carries forward the existing reviewed cost-fidelity approach rather than claiming that arbitrary raw ITree terms have checked fidelity.

Implementation verification includes a clean project build, executable observations, inspection of derived computational terms, and assumption reports for the main example and common-library theorems. The intended assumption reports remain closed under the global context. The current milestone provides counting and tick-ignoring interpretations; complete removal of time-event runtime overhead is reserved for an extraction-stage design.

## Shared unit-tick events

The researcher requested that both Level 1 and Level 2 emit abstract time events, with canonical counting interpretation for proofs and an interpretation that ignores ticks for execution and eventual extraction. This extends the Level 2 interpreter-owned-counter decision to a common event interface and a migration of Level 1.

The researcher rejected the writer-event proposal and chose a dedicated singleton effect:

```coq
Variant TimeE : Type -> Type :=
| Tick : TimeE unit.

Definition tick : itree TimeE unit := trigger Tick.
```

The common interface provides canonical counting and tick-ignoring interpretations. Each event increments the private counter by exactly one under counting and supplies `tt` under ignoring. A generic checked theorem relates the two interpretations by equality of their computational results after discarding the counted cost.

The array interpreter retains its state/option semantics and emits the approved unit ticks for array operations. The shared time interpretation then counts or ignores both those automatic ticks and explicit ticks for non-array work.

| Array operation | Automatically emitted unit ticks |
| --- | --- |
| `alloc size` | `size + 1` |
| `read index` | `1`, including on failure |
| `set index value` | `1`, including on failure |

These charges belong in the common interpreter, so individual examples receive them automatically. Every charge uses a unit `Tick` event.

The approved L2 non-array convention is:

| Work | Explicit unit ticks |
| --- | --- |
| Function entry, including base cases | `1` |
| Each `iter` body entry, including its terminating invocation | `1` |
| Each arithmetic operation on data values | `1` |

The iteration-entry tick covers comparisons, index maintenance, and branching. The callback's representation as a Gallina function does not add a second entry charge; target-program functions called from it receive their normal entry charges. These are project-wide rules. The common combinators `function_entry`, `cost_iter`, and `cost_add` insert the ticks and provide reusable laws. Their use remains a construction discipline: arbitrary raw trees and pure arithmetic can bypass these helpers. The approved assurance scope above retains review of their use.

L1 now uses the approved uniform rules. Its recurrence is `T(0) = T(1) = 1` and `T(input + 2) = 2 + T(input + 1) + T(input)`. Its input-two and input-five costs are four and twenty-two instead of three and fifteen. `fib_cost_bound` proves `T(input) <= 2^input`, with bound constant one. `Fib_L1_count_from` connects the actual program to the revised exact recurrence for every input and initial counter.

Interpreting visible time events introduces `Tau` steps, so the existing immediate L1 `observe = RetF` theorems need suitable `Leaf` or `eutt` formulations with the revised numerical costs.

### Extraction evidence and scope

A temporary extracted OCaml example successfully executed an `iter`-based Fibonacci computation under a handler that ignored time events. It returned the expected values for inputs `0`, `1`, `2`, `5`, and `10`, without maintaining or returning a cost counter.

With the final singleton effect, the generated code had no charge payload or charge-expression computation. It still constructed and handled time-event nodes, including under ordinary inlining directives. Ignoring ticks therefore supports non-counting execution but does not automatically establish complete removal of time-instrumentation overhead. The approved milestone provides the shared counting and tick-ignoring interpretations; full runtime erasure belongs to a later extraction design.

## Implementation

`Fib_L2` uses a two-cell rolling array. Allocation creates two `None` cells, and the program initializes them to zero and one. Each nonterminal loop iteration reads both cells, adds their values through `cost_add`, and updates the cells. The terminating iteration reads the first cell as the result. Only the remaining iteration count is loop-carried.

`Fib_L2_count_from` proves the exact all-input execution, including an arbitrary initial counter. Starting from the canonical empty array and zero counter, the outcome is:

```text
cost:        6 * input + 8
final array: [Some (Fib_L0 input); Some (Fib_L0 (S input))]
result:      Fib_L0 input
```

The occurrences of `Fib_L0` describe the theorem, not the computational body. The `Spec_L2` proof witnesses `time_constant = 8` and `space_constant = 2`. The stronger theorem `Fib_L2_intermediate_bound` bounds every canonical residual array by two cells. This constant-space implementation satisfies the approved linear upper bound without adding a full-table requirement to the specification.

The executable checks in `theories/Examples.v` cover inputs zero, one, two, five, and ten at both levels; tick-ignoring execution; polymorphic Boolean storage; allocation base indices; uninitialized and invalid accesses; failed-continuation short-circuiting; the terminal iteration charge; and uncharged Tau prefixes. The file also inspects the computational terms. The current assumption audit uses `checks/assumptions.txt` and the fail-closed `make assumptions` target, which replaced the original print-only reports after this implementation's retrospective.

## Implementation verification

The following checks passed in the prepared `cs2-rocq92` switch:

```sh
opam exec --switch=cs2-rocq92 -- make clean
opam exec --switch=cs2-rocq92 -- make -j2 build
opam exec --switch=cs2-rocq92 -- make examples
```

All five source files compiled from a clean build. The replay confirmed the following values and counted costs:

| Input | Result at both levels | L1 cost | L2 cost |
| --- | --- | --- | --- |
| `0` | `0` | `1` | `8` |
| `1` | `1` | `1` | `14` |
| `2` | `1` | `4` | `20` |
| `5` | `5` | `22` | `38` |
| `10` | `55` | `265` | `68` |

Every centralized assumption report was closed under the global context. The printed derived terms contained their own charged computations.

### Independent implementation review

The compile gate passed for all five source files. Their recorded compilation times ranged from 0.394 seconds to 2.921 seconds.

The standards review found no documented-standard violations or actionable coding/proof smells. It checked the singleton effect, shared charging machinery, separation of generic and Fibonacci-specific proofs, construction inside Derive, and the stated assurance scope.

The specification review found no missing, incorrect, or out-of-scope requirements. Its source-level cost-fidelity inspection confirmed genuine array use, charged iteration and arithmetic, no reference-function shortcuts, and the revised L1 recurrence. It also checked the intermediate-state and handler-prefix space arguments.

Review summary: build gate passed; standards findings zero; specification findings zero. This remains reviewed fidelity under the approved assurance model, not a universal fidelity theorem for arbitrary candidate programs.

## Feasibility evidence

A temporary prototype compiled under the active Rocq 9.2 toolchain using `ITree.iter`, `stateE`, and `interp_state` from `ITree.Events.State`. It filled a preallocated list-backed table of `n + 1` abstract cells with Fibonacci values and interpreted all state events into a closed `itree void1`.

Executable examples for inputs `0`, `1`, and `5` returned the expected full tables and Fibonacci results; their proofs reported no assumptions. This establishes API compatibility and these concrete evaluations. It does not establish all-input correctness, termination, or resource bounds, and it does not approve the full-table algorithm or the list representation.

A second temporary probe verified the earlier direct reachability formulation, which the monotone-space approach supersedes.

A third temporary probe compiled allocation, read, and set events with a canonical `interp_state` handler. Allocation appended zero cells and returned the old length. It proved allocation's exact length increase, length preservation for reads and sets, and a generic `has_post` theorem that any return's final length is at least the initial length. A small `iter` computation exercised repeated allocation, writes, and reads. The final-state specification above and a parameterized `Derive` syntax check also compiled. The relevant proofs reported no assumptions.

The third probe used provisional default-zero reads and no-op writes for invalid indices; those policies are not approved. Its costs were placeholders. The parameterized `Derive` check reused a supplied witness rather than deriving Fibonacci.

A fourth temporary probe compiled the polymorphic `option A` model for both `nat` and `bool`. Its provisional read interface returned optional values and distinguished uninitialized cells from bounds errors. The researcher superseded that interface with direct-valued reads and option failure in the canonical interpretation.

A fifth temporary probe compiled direct-valued reads under `interp_state` into ExtLib's `optionT (itree void1)`, using the installed `MonadIter_optionT` instance. Both uninitialized and out-of-bounds reads aborted with `None`; initialized reads supplied `nat` or `bool` directly. Valid writes stored `Some v`, and invalid writes aborted. The probe also exercised allocation and `iter` and checked successful-primitive length monotonicity without assumptions.

An extension of the fifth probe placed the time counter in interpreter-owned state and had raw computations return only their result. A separate provisional tick event and provisional array-event charges produced closed outcomes of type `option ((cells * nat) * result)`. Exact counter increments, executable accumulation examples, and a success-only specification shape compiled without assumptions. The researcher subsequently approved counter ownership, singleton ticks, and the automatic array charging schedule. The all-input Fibonacci derivations were completed during implementation.

A module-separation probe compiled the common array interpretation independently, without the project's load-path mapping. Its loaded libraries were limited to Corelib, Stdlib, ExtLib, ITree, and their Paco dependencies. A separate client imported that common module and Fibonacci, defined the example-specific specification shape, and exercised the same interpreter at both `nat` and `bool`. The common module's length and counter laws and client examples reported no assumptions. The time-accounting extension remained explicitly provisional.

An initial shared-time probe used writer events. The singleton-time probe superseded it with the exact `TimeE` above and standard `interp_state` and `interp`. A coinductive proof established `eutt` preservation of results for arbitrary trees and initial counters without assumptions. A small raw-effect `Derive` probe and an array/state/option interpretation emitting unit ticks also compiled. The array composition preserved successful values and `None` failures under tick ignoring. Private repeated-tick emission in the array handler verified the subsequently approved allocation count `size + 1` and one tick per read/set attempt.

An L1-based relational-specification probe compiled the proposed relation with an abstract raw L1 reference. An all-input toy proof related a one-tick identity reference to an allocated-cell-and-`iter` identity implementation with cost four, proving the specification with time constant four and space constant one. It also proved that a failed-read candidate could not satisfy the relation. These theorems reported no assumptions and verified that different costs are permitted. They do not constitute the Fibonacci derivation, the L1 migration, or complete runtime erasure.

A separate common-library bridge probe proved interpreter length monotonicity on successful leaves and used existing `Subtree.subtree`, subtree leaf inclusion, closed finiteness, and `Leaf_eutt_l` to derive the intermediate-state bound from the final-state relation. It verified actual allocation and set continuation boundaries on the all-input iter toy example. The relevant proofs reported no assumptions. The same client verified that L2's explicit finiteness conjunct follows from its relational clause once counted L1 is known finite.

A uniform-rule probe compiled polymorphic common constructors for function entry, iteration-body entry, and primitive arithmetic. Immediate iteration termination cost one tick; one continuing invocation followed by termination cost two. A temporary naive Fibonacci computation using function-entry and addition constructors evaluated to costs one, one, four, and twenty-two on inputs zero, one, two, and five. The changed specification-only recurrence's all-input exponential bound was proved without assumptions. The actual L1 migration subsequently supplied the all-input program-to-recurrence theorem.
