# Level 0 to Level 1 Design Interview

> **Historical baseline.** This document preserves the original L1 design and its verification evidence. The [project-wide cost conventions](agents/cost-conventions.md) supersede its invocation-only model, and the L1 revision is now implemented. See the [README](../README.md) for the current implementation and verification status, and the [Level 2 design interview](level-2-design-interview.md) for design decisions. The build and review results below concern only the original baseline.

The researcher approved the consolidated design on 2026-10-27. This document records the agreed requirements and the feasibility checks that informed them.

## Established requirements

- Use Rocq 9.2 and keep all project artifacts in English.
- Limit the initial implementation to the pure Fibonacci reference and a derived, naive recursive Level 1 baseline.
- Expose a closed iTree with interpreted, observable cost at the public specification boundary.
- Have the researcher supply or approve the specifications, Derive declarations, cost semantics, and implementation constraints.
- Have the AI construct the implementation while proving the approved Derive goals.
- Require the correct Fibonacci result, termination for every input, and a uniform exponential cost bound. Quantify the bound's constant before the input.
- Name the public Level 1 specification `Spec_L1`.
- Name the derived Level 1 implementation `Fib_L1`.
- Charge one tick on entry to every Fibonacci invocation, including the outermost invocation and base cases. The Level 1 cost measure counts invocations only.
- Address cost fidelity separately from the bound on the returned cost.
- Check the build, executable examples, and assumptions of the main theorems without bypassing core obligations with axioms or admitted proofs.

## Verified toolchain facts

On 2026-10-27, the active opam switch was `cs2-rocq92`, with:

| Package | Installed version |
| --- | --- |
| `rocq-core` | `9.2.0` |
| `rocq-stdlib` | `9.2.0` |
| `coq-itree` | `5.2.1` |
| `coq-paco` | `4.2.3` |
| `coq-ext-lib` | `0.13.2` |

`opam exec -- rocq --version` reported Rocq 9.2, compiled with OCaml 5.4.1. A temporary smoke test compiled with `opam exec -- rocq compile` and checked:

- `From Corelib Require Derive.`
- `From ITree Require Import ITree ITreeFacts.`
- The documented `Derive ... in ... as ...` command constructing a transparent closed iTree returning a result-cost pair.
- `≈` between that computation and its return value, including a separate example with one finite `Tau` step.
- `Print Assumptions` reporting that the smoke-test derivation theorem was closed under the global context.

These initial probes confirmed the basic imports and APIs in the installed combination. The completed development's verification is recorded at the end of this document.

A second temporary probe compiled a partial specification using `From ITree.Props Require Import HasPost.` The specification quantified a positive constant before the input and constrained both components of the returned pair through `has_post`. The probe verified that both infinite `Tau` divergence and an uncharged reference-function shortcut satisfy this partial specification. The counterexample theorems and a small Derive example reported no axioms through `Print Assumptions`.

A further temporary probe compiled the strengthened contract with `forall n, all_finite (p n)`, using `From ITree.Props Require Import Finite.` It checked the closed-tree equivalence between this termination property and `forall n, exists outcome, outcome ∈ p n`, rejected infinite `Tau` divergence, and established that the combined contract entails a finite return with the required result and bounded cost for every input. These probe theorems and the corresponding Derive example reported no axioms.

The library's generic `has_post_Leaf` lemma depends on `Eqdep.Eq_rect_eq.eq_rect_eq`. The combined-contract probe avoided this dependency with a direct closed-tree specialization. This is a proof-engineering observation for the eventual assumption audit.

## Relationship to the paper

[Don't Sweat Interaction Trees](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.16), Section 2, Figure 3, and pages 16:6-16:7, constructs an unknown target program through a constructive equivalence proof. The paper explicitly notes that the equivalence theorem does not itself require the target to be simpler; the proof steps determine the resulting construction.

That distinction also matters here: result correctness and a bounded returned cost do not, by themselves, establish faithful accounting of the implementation. The paper's local-variable-lifting framework does not supply this prototype's cost semantics. Its state and loop results may become relevant at later refinement levels.

## Approved assurance boundary

- A candidate such as `Ret (Fib_L0 n, T n)` is not an acceptable solution merely because it returns the expected result and cost number.
- The approved approach assigns inspection of the implementation's cost discipline to agents, rather than requiring a machine-checked restricted construction representation in the initial milestone.
- After considering a partial-correctness-only milestone, the researcher requested an all-input termination conjunct, initially expressed through `Leaf`. The result-independent library predicate `all_finite` provides the same guarantee for the closed public target.
- The current contract combines partial correctness through `has_post` with all-input finiteness. Together they require total correctness; termination is a Rocq-checked obligation, while cost fidelity remains an agent-reviewed obligation.

The partial-correctness-only proposal is superseded. Although `has_post` alone admits divergence, the finiteness conjunct rules it out. Executable examples still supplement the all-input proofs.

The researcher approved this assurance boundary together with the specification and implementation constraints below.

## Agreed meaning: cost fidelity

The researcher approved this meaning: the implementation follows the agreed charging rules, and its reported cost is exactly the total accumulated under those rules.

This meaning covers both:

1. Charging the work that the cost model requires, with no omitted or duplicate charges.
2. Accumulating those charges correctly, without independently fabricating the reported total.

Under the approved invocation-count model, every Fibonacci invocation, including the outermost call and base cases, incurs exactly one charge. Numerical agreement with a separately computed recurrence is insufficient to establish that the construction follows these rules.

Cost fidelity does not mean machine-time accuracy, a cost upper bound, or termination. Its meaning and its enforcement mechanism are separate decisions.

The meaning is agreed independently of its enforcement mechanism. The approved approach assigns cost-fidelity review to agents while retaining checked laws for the cost primitives.

## Approved specification

The following approved contract incorporates the requested termination property and specification name, using the result-cost pair representation:

```coq
Import HasPostNotations.

Definition CostM (A : Type) := itree void1 (A * nat).

Definition Spec_L1 (p : nat -> CostM nat) : Prop :=
  (exists c : nat,
     0 < c /\
     forall n : nat,
       p n ⤳ (fun '(r, k) => r = Fib_L0 n /\ k <= c * 2 ^ n)) /\
  (forall n : nat, all_finite (p n)).
```

The corresponding approved declaration is:

```coq
Derive (Fib_L1 : nat -> CostM nat) in
  (Spec_L1 Fib_L1) as Fib_L1_spec.
```

The uniform constant is shared by all inputs. The postcondition constrains the returned result and cost, and the finiteness conjunct requires a return for every input without naming its value. For closed `void1` trees, `all_finite` and `any_finite` coincide, and `finite_leaf_non_interactive` relates finiteness to an existential `Leaf` witness.

Agent review separately assesses cost fidelity. A terminating shortcut that fabricates the returned cost can still satisfy the checked contract and must be rejected by this review.

## Agreed counting convention

The researcher approved one tick per Fibonacci invocation, including the outermost call and both base cases. Addition, pattern matching, and monadic plumbing have no separate charge in this model.

The required cost recurrence is:

```text
T(0) = 1
T(1) = 1
T(n + 2) = 1 + T(n + 1) + T(n)
```

The corresponding example costs for inputs `0`, `1`, `2`, and `5` are `1`, `1`, `3`, and `15`. The general bound remains `T(n) <= 2^n`, with the public existential constant witnessed by `1`.

### Exact cost and growth rate

The recurrence has the exact solution `T(n) = 2 * Fib_L0 (n + 1) - 1`. Thus the invocation count is related to the Fibonacci sequence, whose growth is itself exponential: mathematically, `T(n)` is `Theta(phi^n)`, where `phi = (1 + sqrt(5)) / 2`.

The public `2^n` bound is a convenient upper bound, not an exact cost or a tight growth rate. The exact identity remains an optional lemma rather than an additional acceptance criterion. Its mathematical statement here does not claim that it has already been checked in Rocq.

## Agreed computational boundary

The researcher approved this construction constraint: the computational body of `Fib_L1` must not depend on `Fib_L0` or a separately computed cost recurrence. These functions may appear in specifications and proofs, while the implementation obtains its result from its own naive recursive subcomputations and its cost through the approved cost operations.

Agents will review this constraint as part of cost fidelity. The AI still chooses the proof steps and necessary implementation helpers within the approved naive-recursion requirement.

## Agreed recursion mechanism and extension scope

The researcher approved structural recursion over the natural-number input for this baseline, with the AI choosing the guarded recursion skeleton inside the Derive proof. The program remains unknown when the declaration is entered; it is not defined separately and wrapped afterward. A separate all-input `all_finite` proof remains required because structural recursion of the Rocq function alone does not establish finiteness of its returned iTree.

A temporary independent unary-recursion probe compiled under the installed versions. It constructed a program through Derive using interpreted tick and writer bind, returned the input value, accumulated exactly `n + 1` cost, established the uniform exponential bound with constant `1`, and proved all-input finiteness. A base-result hole was determined by the proof after the recursion skeleton was chosen. The derived program remained transparent, and evaluation of input `4` produced `RetF (4, 5)`.

`Print Assumptions` reported no axioms for the probe theorem. Its final proof used exact observation equations to avoid a UIP dependency encountered through a generic library postcondition-bind proof route. At design time, this established a small instance of the mechanism; the Fibonacci derivation was subsequently completed during implementation.

This choice applies to the initial Fibonacci baseline only. The researcher explicitly leaves `iter` available for later levels and `mrec` available for other examples. The public behavioral specification does not impose structural recursion as a general construction requirement.

Future uses of iteration or mutual recursion must supply suitable termination proofs and explicit, comparable accounting rules. In particular, iteration must not make loop work disappear under an invocation-only cost convention. Recursive-call or state effects introduced internally must be interpreted before the public closed-tree boundary. Their implementation and compatibility checks belong to the later milestones.

## Approved engineering defaults

- Keep the public result-cost pair and a small writer-style interface with pure, interpreted tick, and cost-accumulating bind.
- Pin the verified Rocq and ITree package versions listed above in a small opam project, with a standard Makefile-based build.
- Keep the cost interface, Fibonacci development, and executable examples in a small set of source files.
- Check primitive cost laws, the derived program's functional and cost results, its all-input finiteness, and its connection to the invocation-count recurrence.
- Inspect the main theorem assumptions, run the executable examples, and document the agent-reviewed cost-fidelity constraints in the English README.

## Implementation confirmation

The researcher explicitly approved proceeding with the Level 0 to Level 1 implementation. The initial source layout is `theories/Cost.v` for the cost interface, `theories/Fibonacci.v` for the reference, specification, derivation, and general proofs, and `theories/Examples.v` for executable observations and assumption checks. The logical library prefix is `RefineToITree`.

## Implementation verification

On 2026-10-27, `opam exec -- make clean && opam exec -- make build` compiled all three source files under the verified Rocq 9.2 stack. `opam exec -- make examples` then successfully replayed the executable observations and assumption reports from an up-to-date build.

The four observations were `(0, 1)`, `(1, 1)`, `(1, 3)`, and `(5, 15)` for inputs `0`, `1`, `2`, and `5`. The finite-Tau composition example also compiled, preserving one tick across two Tau prefixes.

The audit reported `Closed under the global context` for `Fib_L1_spec`, `Fib_L1_observe`, `Fib_L1_terminates`, `Fib_L1_leaf`, `fib_cost_bound`, `cost_bind_leaf`, `cost_bind_finite`, and the finite-Tau example. The printed `Fib_L1` term contains its own two recursive calls and writer operations, with no computational use of `Fib_L0` or `fib_cost`.

The README documents the build, approved specification, theorem inventory, and remaining source-review boundary. The fresh-switch setup recipe is documented but has not been executed; the tested compatibility claim concerns the prepared switch and pinned package versions above.

## Independent implementation review

The standards review found no documented-standard violations. It noted one optional, low-priority duplication: the exact observation induction appears both inside the Derive proof and in the exported `Fib_L1_observe` theorem. The initial prototype retains these explicit arguments to keep the constructive proof local and the public theorem separate without adding a new proof abstraction.

The specification review found no missing, incorrect, or out-of-scope requirements. Its independent cost-fidelity inspection passed: the program charges each invocation once, performs both recursive subcomputations, adds their returned results, accumulates costs through the approved operations, and does not compute through `Fib_L0` or `fib_cost`. This is source-review evidence under the approved assurance boundary, not a universal cost-fidelity theorem for every candidate satisfying `Spec_L1`.
