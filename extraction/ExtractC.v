(* Rocq 9.2 JSON is a build-time interface to the C generator.  Extract the
   actual implementations constructed inside the L1-L4 Derive proofs.  Run
   this client with rocq repl from the repository root, after building them. *)
From Stdlib Require Import Extraction Arith.
From RefineToITree Require Import FibonacciL4.

Extraction Language JSON.
Set Extraction Output Directory "build/c".
Extraction NoInline ITree.bind function_entry cost_iter
  cost_add cost_mul cost_sub array_alloc array_read array_set
  Nat.add Nat.mul Nat.sub Nat.div2 Nat.leb.
(* Keep L3/L4 first: extraction order determines registered helper names. *)
Extraction "targets.json" Fib_L3 Fib_L4 Fib_L1 Fib_L2.
