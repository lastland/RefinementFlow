(* Independent clients of the shared source constructs.  Extract these with
   the same imports, root order, and NoInline registry as ExtractC.v: adding
   fixture roots must not rename the production AST or its registered helpers.
   The negative clients are intentionally outside the approved C fragment. *)
From Stdlib Require Import Extraction Arith.
From RefineToITree Require Import FibonacciL4.
Import ITreeNotations.
Local Open Scope itree_scope.

Definition StateSwapFixture (input : nat) : itree (ArrayE nat +' TimeE) nat :=
  cost_iter (fun state =>
    let '(remaining, (first, second)) := state in
    match remaining with
    | 0 => Ret (inr (first + 10 * second))
    | S rest => Ret (inl (rest, (second, first)))
    end) (input, (1, 2)).

Definition DirectArithmeticFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  Ret (((input + 6) * 3 - input) + Nat.div2 input).

(* A read and its returned expression must retain their values across a write
   to the same cell.  The later read must see the write, including its order. *)
Definition SequencingFixture (input : nat) : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 2 ;;
  array_set 0 input ;;
  array_set 1 3 ;;
  saved <- (value <- array_read 0 ;; Ret (value + 7)) ;;
  array_set 0 (input + 1) ;;
  changed <- array_read 0 ;;
  array_set 1 changed ;;
  later <- array_read 1 ;;
  Ret (saved * 100 + later).

Definition ConditionalFixture (input : nat) : itree (ArrayE nat +' TimeE) nat :=
  chosen <- (if input <=? 4 then cost_add input 11 else cost_mul input 3) ;;
  match input with
  | 0 => Ret (chosen + 100)
  | S rest => Ret (chosen + rest)
  end.

(* Both branches initialize the cell; rejecting every conditional write would
   be too restrictive, just as accepting a one-branch write would be unsound. *)
Definition BranchInitializationFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 1 ;;
  (if input <=? 4 then array_set 0 (input + 1)
   else array_set 0 (input * 2)) ;;
  array_read 0.

(* A direct TimeE client, independent of Fibonacci: each predecessor call adds
   three to a base value of seven.  This exercises singleton self-recursion,
   function-entry erasure, and charged arithmetic without mutable arrays. *)
Fixpoint RecursiveCountdownFixture (input : nat) : itree TimeE nat :=
  function_entry (fun input =>
    match input with
    | 0 => Ret 7
    | S rest => value <- RecursiveCountdownFixture rest ;; cost_add value 3
    end) input.

(* These are generated and executed separately, without unsigned-overflow
   instrumentation: C's chosen wraparound deliberately differs from Nat.sub. *)
Definition CostSubFixture (input : nat) : itree (ArrayE nat +' TimeE) nat :=
  cost_sub 0 input.
Definition PureSubFixture (input : nat) : itree (ArrayE nat +' TimeE) nat :=
  Ret (0 - input).

Definition UninitializedFixture (_input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 1 ;; array_read 0.

Definition OutOfBoundsReadFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 1 ;; array_set 0 input ;; array_read 1.

Definition OutOfBoundsWriteFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 1 ;; array_set 1 input ;; Ret input.

Definition DynamicReadFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 2 ;; array_set 0 1 ;; array_set 1 2 ;; array_read input.

Definition DynamicWriteFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 2 ;; array_set input 1 ;; Ret input.

Definition DynamicSizeFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc input ;; Ret input.

Definition MultipleAllocationFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 1 ;; array_alloc 1 ;; Ret input.

Definition AllocationInLoopFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  cost_iter (fun remaining =>
    match remaining with
    | 0 => Ret (inr input)
    | S rest => array_alloc 1 ;; Ret (inl rest)
    end) input.

Definition AllocationInBranchFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  if input <=? 4 then array_alloc 1 ;; Ret input else Ret input.

Definition BranchOnlyInitializationFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 1 ;;
  (if input <=? 4 then array_set 0 input else Ret tt) ;;
  array_read 0.

Definition LoopOnlyInitializationFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  array_alloc 1 ;;
  cost_iter (fun remaining =>
    match remaining with
    | 0 => Ret (inr tt)
    | S rest => array_set 0 input ;; Ret (inl rest)
    end) input ;;
  array_read 0.

Definition RawTauFixture (input : nat) : itree (ArrayE nat +' TimeE) nat :=
  Tau (Ret input).

Fixpoint FixtureRecursiveHelper (input : nat) : nat :=
  match input with
  | 0 => 0
  | S rest => S (FixtureRecursiveHelper rest)
  end.

Definition RecursiveHelperFixture (input : nat)
    : itree (ArrayE nat +' TimeE) nat :=
  Ret (FixtureRecursiveHelper input).

Definition RawEffectFixture (input : nat) : itree (ArrayE nat +' TimeE) nat :=
  trigger Tick ;; Ret input.

Extraction Language JSON.
Set Extraction Output Directory "build/c".
Extraction NoInline ITree.bind function_entry cost_iter
  cost_add cost_mul cost_sub array_alloc array_read array_set
  Nat.add Nat.mul Nat.sub Nat.div2 Nat.leb.
Extraction NoInline FixtureRecursiveHelper.
Extraction "fixtures.json" Fib_L3 Fib_L4 Fib_L1 Fib_L2
  StateSwapFixture DirectArithmeticFixture SequencingFixture ConditionalFixture
  BranchInitializationFixture RecursiveCountdownFixture CostSubFixture PureSubFixture
  UninitializedFixture OutOfBoundsReadFixture OutOfBoundsWriteFixture
  DynamicReadFixture DynamicWriteFixture DynamicSizeFixture
  MultipleAllocationFixture AllocationInLoopFixture AllocationInBranchFixture
  BranchOnlyInitializationFixture LoopOnlyInitializationFixture
  RawTauFixture RecursiveHelperFixture RawEffectFixture.
