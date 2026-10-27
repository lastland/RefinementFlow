# Specification-Driven Program Construction

This project studies proof-driven construction of programs under researcher-approved functional, termination, and cost requirements.

## Language

**Level 0**:
The pure, naive recursive Fibonacci reference used to define the required results.
_Avoid_: Optimized reference, derived baseline

**Level 1**:
The naive recursive Fibonacci baseline derived under the project-wide charging rules and used as the behavioral reference for Level 2.
_Avoid_: Optimized Fibonacci, unhandled cost computation

**Level 2**:
The second derived Fibonacci implementation, specified relative to Level 1, with a uniform linear accumulated-cost bound and a linear bound on mutable-array length throughout execution.
_Avoid_: Bit-complexity guarantee, final-state bound without a monotonicity argument

**Level 3**:
The Fibonacci level specified relative to Level 2, required to satisfy a uniform logarithmic accumulated-cost bound and a constant bound on mutable-array length throughout execution.
_Avoid_: Bit-complexity guarantee, unmeasured growing auxiliary storage

**Level 4**:
The sequential Fibonacci level specified relative to Level 3, with a uniform affine accumulated-cost bound in `Nat.log2 input + 1`: an additive constant plus a positive coefficient strictly below `13`, both independent of input. It requires a constant bound on mutable-array length throughout execution and retains L3's storage discipline: persistent Fibonacci data in the array, scalar controls, and bounded arithmetic temporaries. Array-cell bounds are checked; the scalar-storage discipline requires source review.
_Avoid_: Batched Fibonacci queries, current parallel Fibonacci level, optimal sequential algorithm, machine-time or bit-space guarantee

**Derivation**:
A proof-driven construction that produces an implementation together with a checked theorem for a researcher-approved specification.
_Avoid_: Automatic synthesis by Derive

**Accumulated cost**:
The number of ticks accumulated by a terminating computation under the project-wide charging rules.
_Avoid_: Machine running time, observation fuel

**Parallel time**:
The cost of the longest dependency chain of charged operations in a terminating computation. Sequential costs add; costs of independent parallel branches combine by maximum.
_Avoid_: Accumulated cost, machine running time, observation fuel

**Serialization**:
The sequential execution of a parallel program's same child computations with fork/join coordination and its charges removed. Computational operations and their charges are preserved, including any duplicated work in the children.
_Avoid_: Tick ignoring, separately optimized sequential algorithm

**Worker budget**:
The input-independent maximum number of execution workers available concurrently, including the worker executing the parent computation. A waiting parent's saved continuation consumes storage without necessarily reserving a worker.
_Avoid_: Queued-task count, suspended-continuation count

**Tick**:
An abstract time-cost action that contributes exactly one unit to accumulated cost under the canonical counting interpretation.
_Avoid_: Weighted charge, elapsed time, observation fuel

**Invocation count**:
The number of Fibonacci invocations in a computation, including the outermost invocation and all base-case invocations. It is one component of Level 1's accumulated cost, which also includes charges for data arithmetic.
_Avoid_: Total accumulated cost, addition count, machine running time, Tau count

**Unit-cost, array-cell model**:
The project's resource abstraction in which arithmetic and indexed array operations have constant abstract cost, and array space counts all allocated entries, including uninitialized entries, independently of their bit length.
_Avoid_: Machine running time, bit-space complexity

**Cost fidelity**:
Compliance with the agreed charge-placement and cost-accumulation rules: the implementation charges the required work and reports exactly the accumulated total. A cost bound or a numerically correct total alone does not establish this compliance.
_Avoid_: Cost bound alone, machine-time accuracy

**Observation fuel**:
An evaluator allowance for inspecting an execution, distinct from the computation's accumulated cost.
_Avoid_: Modeled cost, termination proof
