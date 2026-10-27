# Level 3 Design Interview

The researcher approved the consolidated design on 2026-10-28 after confirming all seven interview decisions. `Fib_L3` is now implemented: its all-input proofs, clean compilation, and full integrated `make check` pass. Independent standards and specification reviews found no actionable issues. See [Implementation](#implementation) for the chosen algorithm and proved results.

## Requested requirements

- Build `Fib_L3`.
- Require an `O(log n)` time-cost bound in its specification.
- Require an `O(1)` space-cost bound in its specification.

## Existing context

The project's [cost conventions](agents/cost-conventions.md) apply to future examples. The unit-cost, array-cell model counts arithmetic operations and allocated array cells independently of their bit length. Shared combinators and interpreter laws support checked resource bounds; source review checks cost fidelity.

`Fib_L2` already uses two array cells throughout execution. Its exact accumulated cost is `6 * input + 8`. Its specification requires linear upper bounds for time and space, even though its implementation has a stronger constant array-space bound. See the [Level 2 interview](level-2-design-interview.md).

## Confirmed requirements: round 1

The researcher answered yes to all four questions.

1. `Spec_L3` uses `Fib_L2` as its direct behavioral reference. It compares successful returned values, requires termination for every natural-number input, and bounds L3's resources independently.
2. The all-input time bound is `time_constant * (Nat.log2 input + 1)`. The space bound is `space_constant`, with both positive constants independent of the input. The constant array-length bound holds throughout execution, using the shared monotonicity argument.
3. Persistent Fibonacci data lives in the mutable array. A fixed number of scalar control values and bounded arithmetic temporaries are allowed; input-sized auxiliary lists, tables, and recursive stacks are excluded by source review alongside cost fidelity.
4. Multiplication and natural-number subtraction may be one-tick primitives. Their charged helpers will extend the shared arithmetic support.

### Approved relational contract

The approved relation has the following typechecked form:

```coq
Definition Spec_L3
    (program_l3 : nat -> itree (ArrayE nat +' TimeE) nat) : Prop :=
  exists time_constant space_constant : nat,
    0 < time_constant /\ 0 < space_constant /\ forall input,
      eutt
        (fun '(cost_l3, outcome_l3) '(cost_l2, outcome_l2) =>
          match outcome_l3, outcome_l2 with
          | Some (array_l3, result_l3), Some (array_l2, result_l2) =>
              result_l3 = result_l2 /\
              cost_l3 <= time_constant * (Nat.log2 input + 1) /\
              length array_l3 <= space_constant
          | _, _ => False
          end)
        (run_count (program_l3 input)) (run_count (Fib_L2 input)) /\
      all_finite (run_count (program_l3 input)).
```

The relation leaves L2's accumulated cost and array contents unconstrained. Correctness relative to Level 0 follows through the existing levels.

## Feasibility evidence

The following throwaway probes preceded implementation. Their results and limitations are preserved as feasibility evidence, not as verification of the integrated implementation.

An in-memory Rocq probe in the `cs2-rocq92` switch typechecked a relational specification using `run_count (Fib_L2 input)` as the reference, the proposed logarithmic time bound, a constant final-array-length bound, rejection of either failed outcome, and explicit `all_finite` for the candidate.

The probe checked that `Nat.log2 input + 1` is positive for every input and evaluates to `1, 1, 2, 2, 3, 4` on inputs `0, 1, 2, 3, 4, 8`. It also typechecked polymorphic charged multiplication and natural-subtraction helpers and proved that each contributes exactly one tick for every pair of operands and initial counter. Both helper theorems reported “Closed under the global context.”

This evidence established the proposed contract's type compatibility and the primitive helpers' exact charges. It did not establish a logarithmic Fibonacci algorithm or its all-input correctness and resource bounds.

### Iterative fast-doubling probe

A separate throwaway prototype compiled in the same switch using the existing array and time interpreters. It allocates two cells, initializes them to zero and one, constructs a binary mask in a charged loop, and processes the input from its most significant bit in a second charged loop. Only scalar control values cross iteration boundaries; Fibonacci data persists in the two cells.

For cells containing `a = F(k)` and `b = F(k + 1)`, each bit step computes:

```text
c = a * ((b + b) - a)
d = a * a + b * b
e = c + d

next bit 0: store (c, d)
next bit 1: store (d, e)
```

The probe evaluates both counting and tick-ignoring execution successfully on inputs `0, 1, 2, 3, 5, 8, 10`, returning `0, 1, 1, 2, 5, 21, 55`. Those results also agree with L2 on the tested inputs.

The probe proves all-input successful termination and resource bounds under the loop-control charging interpretation: index-only halving, mask updates, comparisons, and branching are covered by iteration-entry ticks. The actual mask-building scan is explicit and charged; the program does not invoke a pure logarithm computation to conceal that scan.

The exact accumulated cost is:

```text
T(0) = 9
T(input) = 8 + 13 * (Nat.log2 input + 1), when input > 0
```

Consequently, the probe checks the proposed time bound with constant `21` and the throughout-execution array bound with constant `2`. It also checks pending array-handler prefixes. Every reported resource-theorem assumption check is closed under the global context.

All-input Fibonacci correctness remained unproved in this feasibility probe. At that stage, the derivation still needed the fast-doubling identities, the processed-prefix invariant, and the relation to L2. The probe established an available implementation shape; it did not commit the design to that algorithm or those exact cost constants.

## Confirmed requirements: round 2

The researcher answered yes to questions five and six, requested both as project-wide rules, and agreed to question seven.

5. The algorithm and concrete resource-bound witnesses remain derivation choices within the approved specification and construction constraints. This is now a project-wide [program-construction rule](../AGENTS.md#program-construction).
6. Each target is constructed inside its `Derive` proof, and target-program loops use shared charged iteration. This is also a project-wide program-construction rule.
7. Index-only halving, mask maintenance, comparisons, and branching belong to the iteration-entry charge. Preprocessing scans are exposed as charged computation; Fibonacci-data arithmetic receives separate operation ticks. The [cost conventions](agents/cost-conventions.md) now record this boundary explicitly.

The approved L3 declaration is:

```coq
Derive (Fib_L3 : nat -> itree (ArrayE nat +' TimeE) nat) in
  (Spec_L3 Fib_L3) as Fib_L3_spec.
```

## Approved consolidated design

The relation and construction declaration above, the confirmed storage discipline, and the shared cost conventions form the L3 contract. The derivation chooses the algorithm and positive resource-bound witnesses. At approval, iterative fast doubling was a checked resource-feasible candidate.

### Integration

The approved integration plan was:

- Add `theories/FibonacciL3.v` for `Spec_L3`, the `Derive` construction, Fibonacci-specific mathematics and invariants, and L3 correctness, termination, and resource theorems.
- Extend `theories/Cost.v` with the approved charged arithmetic primitives and their generic laws. Place any additional reusable array or iteration proof rules in `theories/Array.v`, following the existing separation from example-specific proofs.
- Register the new source in the build, add executable observations and constructed-term inspection to `theories/Examples.v`, and extend `checks/assumptions.txt` with the new headline theorems.
- Document the implementation and its verification evidence in the README after those checks pass.

### Verification and assurance

Rocq checks successful execution, returned-value agreement with L2, all-input termination, the uniform logarithmic time bound, and the constant final-array bound. A theorem for any program satisfying `Spec_L3` derives the throughout-execution array bound through the shared monotonicity result; existing handler-prefix machinery also applies. Tick-ignoring execution preserves the computational outcome through the shared interpreter laws.

Source review checks cost fidelity, the fixed-storage construction discipline, and construction inside `Derive`. Computational targets obtain results through their own charged operations; reference functions and specification-only cost recurrences may guide proofs.

The verification gate is `opam exec --switch=cs2-rocq92 -- make check`, including the build, executable observations, strict assumption audit, and existing guardrail regressions. Every audited theorem must report “Closed under the global context.” Finite samples supplement the all-input proofs.

## Implementation

[`theories/FibonacciL3.v`](../theories/FibonacciL3.v) implements the approved `Spec_L3` and constructs `Fib_L3` inside its `Derive` proof. The derivation chose iterative fast doubling and the positive witnesses `time_constant = 21` and `space_constant = 2`. Neither the algorithm nor these witnesses is imposed on other candidates by the specification.

The target enters through `function_entry`, allocates two cells, and initializes them to zero and one. It then uses two `cost_iter` loops, with both bodies written inline in the derivation:

1. **Construct the mask.** Starting from `(input, 1)`, the loop halves a scalar quotient and doubles a scalar mask until it finds the most significant bit. Input zero produces mask zero. This preprocessing scan is explicit charged iteration, not a hidden logarithm or power computation.
2. **Process the bits.** The loop carries the remaining input and mask, reads the Fibonacci pair from the two cells, applies the fast-doubling formulas recorded above, and stores the next pair. It halves the mask after each bit. At mask zero, the terminal invocation reads and returns the first cell.

Persistent Fibonacci data lives in the array. The target uses a fixed number of scalar controls and arithmetic temporaries; it calls neither `Fib_L0`, `Fib_L1`, nor `Fib_L2`, and it contains no calls to specification-only cost functions, `Nat.log2`, or `Nat.pow`. The earlier levels retain their behavior.

The shared `cost_mul` and `cost_sub` helpers in `Cost.v` each emit one tick. `count_mul_leaf` and `count_sub_leaf` prove their exact charges; `Array.v` supplies the corresponding `run_count_mul_leaf` and `run_count_sub_leaf` laws. Subtraction is truncated natural-number subtraction. For the doubling formula, `Fib_L0_monotone_step` establishes `a <= b`, so `(b + b) - a` is the intended nonnegative difference. `Fib_L0_double_pair` proves the identities used by the bit-step proof.

The doubling proof `fib_l3_doubling_count` uses the new shared `run_count_cost_iter_rank_invariant` with `step_cost = 12` and `exit_cost = 2`, including iteration-entry ticks. The rule separates the proof-only remaining rank from the runtime state. The processed prefix, target, and exponent occur only in the proof; the loop carries only the remaining input and mask. Together with the mask-loop proof, this establishes all-input correctness and exact accumulated cost.

`Fib_L3_count_from` proves the exact outcome from an empty array and any initial counter. `Fib_L3_leaf` and `Fib_L3_count` specialize it to canonical execution from zero:

```text
cost:        fib_l3_cost input
final array: [Some (Fib_L0 input); Some (Fib_L0 (S input))]
result:      Fib_L0 input

fib_l3_cost 0 = 9
fib_l3_cost input = 8 + 13 * (Nat.log2 input + 1), when input > 0
```

`fib_l3_cost_bound` bounds this cost by `21 * (Nat.log2 input + 1)`. `Fib_L3_spec` relates the successful returned value to L2 and proves the resource bounds and explicit finiteness requirement. `Fib_L3_terminates` exposes termination separately, and `Fib_L3_erases` gives the same successful array/value outcome under tick ignoring. As with the shared count-ignore outcome theorem, this is not a claim of full runtime overhead erasure.

`Spec_L3_intermediate_bound` derives a uniform constant bound on canonical residual array lengths for any program satisfying `Spec_L3`. For this implementation, `Fib_L3_intermediate_bound` bounds those arrays by two cells, and `Fib_L3_handler_intermediate_bound` covers pending handler prefixes as well. These results use termination and the shared monotonicity theorems. They count allocated array cells, not the bit storage of growing natural numbers or concrete runtime storage. Source review remains responsible for checking the fixed-storage construction discipline and cost fidelity.

## Implementation verification

`FibonacciL3.v` compiles with its all-input correctness, termination, exact-cost, and space proofs. The extended `Examples.v` also compiles. Its L3 counted examples cover `0, 1, 2, 3, 4, 5, 7, 8, 10, 15, 16`; the tick-ignoring example covers `10`. Printed observations cover all three derived levels at `0, 1, 2, 5, 10`, with L3 costs `9, 21, 34, 47, 60` respectively.

After `opam exec --switch=cs2-rocq92 -- make clean`, all six source files compiled in dependency order. Compilation took 0.678 seconds for `Cost.v`, 2.201 for `Array.v`, 0.454 for `Fibonacci.v`, 0.479 for `FibonacciL2.v`, 0.791 for `FibonacciL3.v`, and 0.531 for `Examples.v`.

`opam exec --switch=cs2-rocq92 -- make check` then passed the build, executable replay, strict assumption audit, and guardrail regressions. All 58 registered theorem reports were “Closed under the global context.” All 45 guardrail tests passed. The assumption-audit driver's default import now includes L3 and its exported dependencies.

### Independent implementation review

Both reviews examined the complete working-tree change relative to the session's starting commit, `43cce24a4f2ccbba76ab3bfd4f4ed331d2d736cf`, including the new source and interview record. The clean six-file compilation and integrated verification gate passed before review.

The standards review found no documented-standard violations or actionable code/proof smells. It checked notation, module boundaries, construction inside `Derive`, source-level cost fidelity, and the fixed-storage discipline. The specification review found no missing, incorrect, partial, or out-of-scope requirements.

Review summary: build gate passed; standards findings zero; specification findings zero. Source review remains part of the approved assurance model, alongside the checked all-input theorems and shared laws.

The [L2 implementation verification record](level-2-design-interview.md#implementation-verification) preserves the earlier baseline's successful clean build, assumption audit, and independent reviews. Those historical results do not verify or review the L3 extension.
