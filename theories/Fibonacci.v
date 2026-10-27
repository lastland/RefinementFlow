From Corelib Require Derive.
From Stdlib Require Import Arith Lia.
From RefineToITree Require Export Cost.
Import ITreeNotations LeafNotations HasPostNotations.
Local Open Scope itree_scope.

(** Level 0: the direct, naive recursive reference. *)
Fixpoint Fib_L0 (input : nat) : nat :=
  match input with
  | 0 => 0
  | S previous => match previous with
    | 0 => 1
    | S earlier => Fib_L0 previous + Fib_L0 earlier
    end
  end.

(** Specification only: every invocation costs one entry tick; every
    non-base invocation also costs one data-addition tick. *)
Fixpoint fib_cost (input : nat) : nat :=
  match input with
  | 0 => 1
  | S previous => match previous with
    | 0 => 1
    | S earlier => 2 + fib_cost previous + fib_cost earlier
    end
  end.

Lemma Fib_L0_step input :
  Fib_L0 (S (S input)) = Fib_L0 (S input) + Fib_L0 input.
Proof. reflexivity. Qed.

(** Proof-only identities of the reference, independent of any derived level.
    Constructed programs obtain these values through charged operations. *)
Lemma Fib_L0_monotone_step input :
  Fib_L0 input <= Fib_L0 (S input).
Proof.
  destruct input as [|input].
  - cbn [Fib_L0]; lia.
  - rewrite Fib_L0_step; lia.
Qed.

Lemma Fib_L0_double_pair input :
  Fib_L0 (2 * input) =
    Fib_L0 input *
      ((Fib_L0 (S input) + Fib_L0 (S input)) - Fib_L0 input) /\
  Fib_L0 (S (2 * input)) =
    Fib_L0 input * Fib_L0 input +
    Fib_L0 (S input) * Fib_L0 (S input).
Proof.
  induction input as [|input [Heven Hodd]].
  - cbn [Fib_L0]; auto.
  - replace (2 * S input) with (S (S (2 * input))) by lia.
    rewrite !Fib_L0_step.
    pose proof (Fib_L0_monotone_step input) as Hmono.
    split; nia.
Qed.

Lemma Fib_L0_double input :
  Fib_L0 (2 * input) =
    Fib_L0 input *
      ((Fib_L0 (S input) + Fib_L0 (S input)) - Fib_L0 input).
Proof. exact (proj1 (Fib_L0_double_pair input)). Qed.

Lemma Fib_L0_double_succ input :
  Fib_L0 (S (2 * input)) =
    Fib_L0 input * Fib_L0 input +
    Fib_L0 (S input) * Fib_L0 (S input).
Proof. exact (proj2 (Fib_L0_double_pair input)). Qed.

Lemma fib_cost_step input :
  fib_cost (S (S input)) = 2 + fib_cost (S input) + fib_cost input.
Proof. reflexivity. Qed.
Lemma fib_cost_positive input : 0 < fib_cost input.
Proof. destruct input as [|[|input]]; cbn [fib_cost]; lia. Qed.
Lemma fib_cost_bound : forall input, fib_cost input <= 2 ^ input.
Proof.
  assert (H : forall input,
    fib_cost (S input) <= 2 ^ (S input) /\
    fib_cost (S (S input)) <= 2 ^ (S (S input))).
  { intro index; induction index as [|index [IHprevious IHcurrent]].
    - cbn; lia.
    - split; [exact IHcurrent |].
      rewrite fib_cost_step.
      assert (Hpow : 1 <= 2 ^ index).
      { assert (Hnonzero : 2 ^ index <> 0) by (apply Nat.pow_nonzero; lia).
        lia. }
      cbn [Nat.pow] in *; nia. }
  intros [|input]; [cbn; lia | exact (proj1 (H input))].
Qed.

Definition Spec_L1 (program : nat -> itree TimeE nat) : Prop :=
  (exists time_constant : nat, 0 < time_constant /\ forall input,
    count (program input) ⤳ (fun '(cost,result) =>
      result = Fib_L0 input /\ cost <= time_constant * 2 ^ input)) /\
  (forall input, all_finite (count (program input))).

(** Fibonacci-specific induction rule, reusable inside and after Derive.
    Its hypotheses expose the program's own recursion and charging helpers;
    neither specification recurrence is used by the computational program. *)
Lemma fib_count_from (program : nat -> itree TimeE nat) :
  program 0 = function_entry (fun _ : nat => Ret 0) 0 ->
  program 1 = function_entry (fun _ : nat => Ret 1) 1 ->
  (forall input, program (S (S input)) =
    function_entry (fun _ : nat =>
      left <- program (S input) ;;
      right <- program input ;; cost_add left right) (S (S input))) ->
  forall input cost,
    (cost + fib_cost input, Fib_L0 input) ∈ count_from (program input) cost.
Proof.
  intros Hzero Hone Hstep.
  assert (H : forall input,
    (forall cost, (cost + fib_cost input, Fib_L0 input)
      ∈ count_from (program input) cost) /\
    (forall cost, (cost + fib_cost (S input), Fib_L0 (S input))
      ∈ count_from (program (S input)) cost)).
  { induction input as [|input [IHprevious IHcurrent]].
    - split; intro cost; [rewrite Hzero | rewrite Hone]; cbn [fib_cost Fib_L0];
        apply count_function_entry_leaf;
        apply LeafRet; rewrite observe_count; cbn;
        replace (cost + 1) with (S cost) by lia; reflexivity.
    - split; [exact IHcurrent |]; intro cost.
      rewrite Hstep, fib_cost_step, Fib_L0_step.
      apply count_function_entry_leaf.
      eapply count_bind_leaf; [exact (IHcurrent (S cost)) |].
      eapply count_bind_leaf;
        [exact (IHprevious (S cost + fib_cost (S input))) |].
      replace (cost + (2 + fib_cost (S input) + fib_cost input))
        with (S (S cost + fib_cost (S input) + fib_cost input)) by lia.
      apply count_add_leaf. }
  intros input; exact (proj1 (H input)).
Qed.

(** The target is unknown at declaration. The proof chooses inline guarded
    recursion and the two base results.
    Raw code returns only values and never calls Fib_L0 or fib_cost. *)
Derive (Fib_L1 : nat -> itree TimeE nat) in (Spec_L1 Fib_L1) as Fib_L1_spec.
Proof.
  [Fib_L1]: refine (fix go (input : nat) {struct input} : itree TimeE nat :=
    function_entry (fun input =>
      match input with
      | 0 => Ret 0
      | S previous => match previous with
        | 0 => Ret 1
        | S earlier =>
            left <- go previous ;;
            right <- go earlier ;; cost_add left right
        end
      end) input).
  assert (Hexact : forall input cost,
    (cost + fib_cost input, Fib_L0 input) ∈ count_from (Fib_L1 input) cost).
  { apply fib_count_from; intros; reflexivity. }
  split.
  - exists 1; split; [lia |]; intro input.
    eapply closed_leaf_has_post; [exact (Hexact input 0) |].
    cbn; split; [reflexivity |].
    pose proof (fib_cost_bound input); lia.
  - intro input; eapply closed_leaf_finite; exact (Hexact input 0).
Qed.

(** Source-discipline laws contain no reference computation or cost oracle. *)
Lemma Fib_L1_zero : Fib_L1 0 = function_entry (fun _ : nat => Ret 0) 0.
Proof. reflexivity. Qed.
Lemma Fib_L1_one : Fib_L1 1 = function_entry (fun _ : nat => Ret 1) 1.
Proof. reflexivity. Qed.
Lemma Fib_L1_step input :
  Fib_L1 (S (S input)) =
    function_entry (fun _ : nat =>
      left <- Fib_L1 (S input) ;;
      right <- Fib_L1 input ;; cost_add left right) (S (S input)).
Proof. reflexivity. Qed.

Theorem Fib_L1_count_from input cost :
  (cost + fib_cost input, Fib_L0 input) ∈ count_from (Fib_L1 input) cost.
Proof.
  apply fib_count_from; [exact Fib_L1_zero | exact Fib_L1_one | exact Fib_L1_step].
Qed.
Theorem Fib_L1_leaf input :
  (fib_cost input, Fib_L0 input) ∈ count (Fib_L1 input).
Proof. exact (Fib_L1_count_from input 0). Qed.
Theorem Fib_L1_count input :
  count (Fib_L1 input) ≈ Ret (fib_cost input, Fib_L0 input).
Proof. apply closed_leaf_eutt, Fib_L1_leaf. Qed.
Theorem Fib_L1_terminates input : all_finite (count (Fib_L1 input)).
Proof. eapply closed_leaf_finite; apply Fib_L1_leaf. Qed.
Theorem Fib_L1_erases input :
  ignore_time (Fib_L1 input) ≈ Ret (Fib_L0 input).
Proof.
  apply closed_leaf_eutt; eapply count_leaf_ignore; apply Fib_L1_leaf.
Qed.
