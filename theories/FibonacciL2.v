From Corelib Require Derive.
From Stdlib Require Import List Arith Lia.
From RefineToITree Require Export Array Fibonacci.
Import ListNotations.
Import Subtree.
Import ITreeNotations LeafNotations.
Local Open Scope itree_scope.

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

(** The only loop-carried value is the remaining iteration count. Both
    Fibonacci data values live in the mutable array. This rule describes
    bodies without defining a completed Fibonacci program. *)
Lemma fib_l2_loop_count
    (body : nat -> itree (ArrayE nat +' TimeE) (nat + nat)) :
  body 0 = (value <- array_read 0 ;; Ret (inr value)) ->
  (forall remaining, body (S remaining) =
    (previous <- array_read 0 ;;
    current <- array_read 1 ;;
    sum <- cost_add current previous ;;
    array_set 0 current ;;
    array_set 1 sum ;; Ret (inl remaining))) ->
  forall remaining index cost,
    (cost + 6 * remaining + 2,
      Some ([Some (Fib_L0 (index + remaining));
             Some (Fib_L0 (S (index + remaining)))], Fib_L0 (index + remaining)))
      ∈ run_count_from (cost_iter body remaining)
        [Some (Fib_L0 index); Some (Fib_L0 (S index))] cost.
Proof.
  intros Hzero Hstep initial_remaining initial_index cost.
  set (target := initial_index + initial_remaining).
  eapply run_count_cost_iter_nat_invariant with
    (step_cost := 6) (exit_cost := 2)
    (invariant := fun remaining array => exists index,
      array = [Some (Fib_L0 index); Some (Fib_L0 (S index))] /\
      index + remaining = target).
  - intros array c [index [Harray Htarget]].
    subst array.
    assert (Hindex : index = target) by lia.
    subst index.
    rewrite Hzero.
    eapply run_count_read_bind; [reflexivity|].
    replace (c + 2) with (S (S c)) by lia.
    apply run_count_from_ret; reflexivity.
  - intros remaining array c [index [Harray Htarget]].
    subst array.
    exists [Some (Fib_L0 (S index)); Some (Fib_L0 (S (S index)))].
    split.
    + exists (S index); split; [reflexivity|lia].
    + rewrite Hstep.
      eapply run_count_read_bind; [reflexivity|].
      eapply run_count_read_bind; [reflexivity|].
      eapply run_count_bind_leaf; [apply run_count_add_leaf|].
      eapply run_count_set_bind; [cbn; lia|].
      eapply run_count_set_bind; [cbn; lia|].
      cbn [set_cell]. replace (c + 6) with (S (S (S (S (S (S c)))))) by lia.
      apply run_count_from_ret; reflexivity.
  - exists initial_index; split; reflexivity.
Qed.

(** Compose entry and array initialization with the invariant-based loop rule. *)
Lemma fib_l2_program_count
    (program : nat -> itree (ArrayE nat +' TimeE) nat)
    (body : nat -> itree (ArrayE nat +' TimeE) (nat + nat)) :
  body 0 = (value <- array_read 0 ;; Ret (inr value)) ->
  (forall remaining, body (S remaining) =
    (previous <- array_read 0 ;;
    current <- array_read 1 ;;
    sum <- cost_add current previous ;;
    array_set 0 current ;;
    array_set 1 sum ;; Ret (inl remaining))) ->
  (forall input, program input = function_entry (fun input =>
    array_alloc 2 ;;
    array_set 0 0 ;;
    array_set 1 1 ;; cost_iter body input) input) ->
  forall input cost,
    (cost + 6 * input + 8,
      Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input))
      ∈ run_count_from (program input) [] cost.
Proof.
  intros Hzero Hstep Hprogram input cost; rewrite Hprogram.
  apply run_count_function_entry_leaf.
  apply run_count_init_pair_bind.
  replace (cost + 6 * input + 8) with ((S cost + 5) + 6 * input + 2) by lia.
  exact (fib_l2_loop_count body Hzero Hstep input 0 (S cost + 5)).
Qed.

Derive (Fib_L2 : nat -> itree (ArrayE nat +' TimeE) nat) in
  (Spec_L2 Fib_L2) as Fib_L2_spec.
Proof.
  [Fib_L2]: refine (fun input => function_entry (fun input =>
    array_alloc 2 ;;
    array_set 0 0 ;;
    array_set 1 1 ;;
    cost_iter (fun remaining => match remaining with
      | 0 => value <- array_read 0 ;; Ret (inr value)
      | S remaining =>
          previous <- array_read 0 ;;
          current <- array_read 1 ;;
          sum <- cost_add current previous ;;
          array_set 0 current ;;
          array_set 1 sum ;; Ret (inl remaining)
      end) input) input).
  assert (Hexact : forall input cost,
    (cost + 6 * input + 8,
      Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input))
      ∈ run_count_from (Fib_L2 input) [] cost).
  { eapply fib_l2_program_count; [| | intros; reflexivity]; intros; reflexivity. }
  exists 8, 2; split; [lia|]; split; [lia|]; intro input; split.
  - rewrite (closed_leaf_eutt _ _ (Hexact input 0)), Fib_L1_count.
    apply eutt_Ret; cbn; repeat split; lia.
  - eapply closed_leaf_finite; exact (Hexact input 0).
Qed.

Theorem Fib_L2_count_from input cost :
  (cost + 6 * input + 8,
    Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input))
    ∈ run_count_from (Fib_L2 input) [] cost.
Proof. eapply fib_l2_program_count; [| | intros; reflexivity]; intros; reflexivity. Qed.

Theorem Fib_L2_leaf input :
  (6 * input + 8,
    Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input))
    ∈ run_count (Fib_L2 input).
Proof. exact (Fib_L2_count_from input 0). Qed.

Theorem Fib_L2_count input :
  run_count (Fib_L2 input) ≈
    Ret (6 * input + 8,
      Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input)).
Proof. apply closed_leaf_eutt, Fib_L2_leaf. Qed.

Theorem Fib_L2_terminates input : all_finite (run_count (Fib_L2 input)).
Proof. eapply closed_leaf_finite; apply Fib_L2_leaf. Qed.

Theorem Fib_L2_erases input :
  run_ignore (Fib_L2 input) ≈
    Ret (Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input)).
Proof.
  apply closed_leaf_eutt; eapply count_leaf_ignore; apply Fib_L2_leaf.
Qed.

(** The relational contract alone supplies a uniform bound for every
    canonical residual, via the common monotone-state theorem. *)
Theorem Spec_L2_intermediate_bound program_l2 :
  Spec_L2 program_l2 ->
  exists space_constant, 0 < space_constant /\ forall input tail array cost,
    subtree (run_count_from tail array cost) (run_count (program_l2 input)) ->
    length array <= space_constant * (input + 1).
Proof.
  intros [time_constant [space_constant [Ht [Hs Hspec]]]].
  exists space_constant; split; [exact Hs|].
  intros input; destruct (Hspec input) as [Hrel Hfin].
  apply final_bound_subtree; [exact Hfin|].
  intros cost outcome Hleaf.
  destruct (Leaf_eutt_l _ _ _ Hrel Hleaf) as [[cost_l1 result_l1] [Hreference Hpost]].
  destruct outcome as [[array_l2 result_l2]|]; [exact (proj2 (proj2 Hpost))|exact Hpost].
Qed.

Theorem Fib_L2_intermediate_bound input tail array cost :
  subtree (run_count_from tail array cost) (run_count (Fib_L2 input)) ->
  length array <= 2.
Proof.
  eapply final_bound_subtree_leaf; [apply Fib_L2_leaf|cbn; lia].
Qed.
