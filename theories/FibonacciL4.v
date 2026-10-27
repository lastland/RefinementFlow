From Corelib Require Derive.
From Stdlib Require Import List Arith Lia.
From RefineToITree Require Export FibonacciL3.
Import ListNotations Subtree ITreeNotations LeafNotations.
Local Open Scope itree_scope.

(** Algorithm-independent contract. All resource witnesses are uniform over
    inputs. The leading coefficient improves on L3's actual coefficient 13,
    not merely its logarithmic bound witness 21. Generic array monotonicity
    turns the final bound into a throughout-execution bound below.
    As in L3, persistent Fibonacci data lives in the array; bounded scalar
    controls and fixed arithmetic temporaries are a source-reviewed constraint,
    not a machine-checked bound on scalar payload sizes. *)
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

Lemma fib_l4_double_odd prefix :
  Fib_L0 (S (S (2 * prefix))) =
    Fib_L0 (S prefix) * (Fib_L0 prefix + Fib_L0 prefix + Fib_L0 (S prefix)).
Proof.
  rewrite Fib_L0_step, Fib_L0_double, Fib_L0_double_succ.
  pose proof (Fib_L0_monotone_step prefix).
  nia.
Qed.

(** A body-equality premise, not a completed executable target. Each branch
    computes only the two needed coordinates, using six charged operations. *)
Definition fib_l4_doubling_body_rule
    (body : nat * nat -> itree (ArrayE nat +' TimeE) ((nat * nat) + nat)) : Prop :=
  forall remaining mask, body (remaining, mask) =
    match mask with
    | 0 => value <- array_read 0 ;; Ret (inr value)
    | S _ =>
        let bit := mask <=? remaining in
        let remaining' := if bit then remaining - mask else remaining in
        a <- array_read 0 ;; b <- array_read 1 ;;
        next_a <- (if bit then
          aa <- cost_mul a a ;; bb <- cost_mul b b ;; cost_add aa bb
          else twice_b <- cost_add b b ;; difference <- cost_sub twice_b a ;;
            cost_mul a difference) ;;
        next_b <- (if bit then
          twice_a <- cost_add a a ;; sum <- cost_add twice_a b ;; cost_mul b sum
          else aa <- cost_mul a a ;; bb <- cost_mul b b ;; cost_add aa bb) ;;
        array_set 0 next_a ;; array_set 1 next_b ;;
        Ret (inl (remaining', Nat.div2 mask))
    end.

(** One continuing invocation: entry, two reads, six arithmetic operations,
    and two writes. The entry tick is already present in the initial counter. *)
Lemma fib_l4_doubling_step body : fib_l4_doubling_body_rule body ->
  forall remaining mask prefix cost, 0 < mask ->
  let bit := mask <=? remaining in
  let prefix' := if bit then 2 * prefix + 1 else 2 * prefix in
  (cost + 11,
    Some ([Some (Fib_L0 prefix'); Some (Fib_L0 (S prefix'))],
      inl ((if bit then remaining - mask else remaining), Nat.div2 mask))) ∈
    run_count_from (body (remaining, mask))
      [Some (Fib_L0 prefix); Some (Fib_L0 (S prefix))] (S cost).
Proof.
  intros Hbody remaining mask prefix cost Hmask.
  unfold fib_l4_doubling_body_rule in Hbody; rewrite Hbody.
  destruct mask as [|mask]; [lia |].
  cbv beta iota zeta.
  eapply run_count_read_bind; [reflexivity |].
  eapply run_count_read_bind; [reflexivity |].
  destruct (S mask <=? remaining).
  - eapply run_count_bind_leaf.
    { eapply run_count_bind_leaf; [apply run_count_mul_leaf |].
      eapply run_count_bind_leaf; [apply run_count_mul_leaf |].
      apply run_count_add_leaf. }
    eapply run_count_bind_leaf.
    { eapply run_count_bind_leaf; [apply run_count_add_leaf |].
      eapply run_count_bind_leaf; [apply run_count_add_leaf |].
      apply run_count_mul_leaf. }
    eapply run_count_set_bind; [cbn; lia |].
    eapply run_count_set_bind; [cbn; lia |].
    cbv beta iota zeta delta [set_cell].
    replace (2 * prefix + 1) with (S (2 * prefix)) by lia.
    rewrite fib_l4_double_odd, Fib_L0_double_succ.
    replace (cost + 11) with (11 + cost) by lia.
    apply run_count_from_ret; reflexivity.
  - eapply run_count_bind_leaf.
    { eapply run_count_bind_leaf; [apply run_count_add_leaf |].
      eapply run_count_bind_leaf; [apply run_count_sub_leaf |].
      apply run_count_mul_leaf. }
    eapply run_count_bind_leaf.
    { eapply run_count_bind_leaf; [apply run_count_mul_leaf |].
      eapply run_count_bind_leaf; [apply run_count_mul_leaf |].
      apply run_count_add_leaf. }
    eapply run_count_set_bind; [cbn; lia |].
    eapply run_count_set_bind; [cbn; lia |].
    cbv beta iota zeta delta [set_cell].
    rewrite Fib_L0_double, Fib_L0_double_succ.
    replace (cost + 11) with (11 + cost) by lia.
    apply run_count_from_ret; reflexivity.
Qed.

Lemma fib_l4_doubling_zero body : fib_l4_doubling_body_rule body ->
  forall remaining prefix cost,
  (cost + 2, Some ([Some (Fib_L0 prefix); Some (Fib_L0 (S prefix))],
    Fib_L0 prefix)) ∈
    run_count_from (cost_iter body (remaining, 0))
      [Some (Fib_L0 prefix); Some (Fib_L0 (S prefix))] cost.
Proof.
  intros Hbody remaining prefix cost.
  eapply run_count_cost_iter_step with (cost' := cost + 2)
    (array' := [Some (Fib_L0 prefix); Some (Fib_L0 (S prefix))])
    (step := inr (Fib_L0 prefix)).
  - unfold fib_l4_doubling_body_rule in Hbody; rewrite Hbody.
    eapply run_count_read_bind; [reflexivity |].
    replace (cost + 2) with (S (S cost)) by lia.
    apply run_count_from_ret; reflexivity.
  - reflexivity.
Qed.

(** L3's processed-prefix invariant, with an eleven-tick continuing step.
    Prefix, target, exponent, and rank are proof data, not target state. *)
Lemma fib_l4_doubling_count body : fib_l4_doubling_body_rule body ->
  forall exponent remaining prefix target cost,
    remaining < 2 * 2 ^ exponent ->
    target = prefix * (2 * 2 ^ exponent) + remaining ->
    (cost + 11 * S exponent + 2,
      Some ([Some (Fib_L0 target); Some (Fib_L0 (S target))], Fib_L0 target)) ∈
      run_count_from (cost_iter body (remaining, 2 ^ exponent))
        [Some (Fib_L0 prefix); Some (Fib_L0 (S prefix))] cost.
Proof.
  intros Hbody exponent remaining prefix target cost Hremaining Htarget.
  set (invariant := fun iterations_left (state : nat * nat) (array : array_state nat) =>
    let '(remaining, mask) := state in
    exists prefix, array = [Some (Fib_L0 prefix); Some (Fib_L0 (S prefix))] /\
      match iterations_left with
      | 0 => mask = 0 /\ remaining = 0 /\ prefix = target
      | S exponent => mask = 2 ^ exponent /\ remaining < 2 * mask /\
          target = prefix * (2 * mask) + remaining
      end).
  eapply run_count_cost_iter_rank_invariant with
    (invariant := invariant) (step_cost := 11) (exit_cost := 2).
  - intros [rest mask] array c Hinv.
    destruct Hinv as [index [-> [-> [-> ->]]]].
    unfold fib_l4_doubling_body_rule in Hbody; rewrite Hbody.
    eapply run_count_read_bind; [reflexivity |].
    replace (c + 2) with (S (S c)) by lia.
    apply run_count_from_ret; reflexivity.
  - intros iterations_left [rest mask] array c Hinv.
    destruct Hinv as [index [-> [Hmask [Hrest Htotal]]]].
    subst mask.
    pose proof (binary_prefix_rank_step target index rest iterations_left Hrest Htotal)
      as [Hpositive Hnext].
    cbn zeta in Hnext.
    set (bit := 2 ^ iterations_left <=? rest) in *.
    set (prefix' := if bit then 2 * index + 1 else 2 * index) in *.
    set (remaining' := if bit then rest - 2 ^ iterations_left else rest) in *.
    exists (remaining', Nat.div2 (2 ^ iterations_left)),
      [Some (Fib_L0 prefix'); Some (Fib_L0 (S prefix'))]; split.
    + exists prefix'; split; [reflexivity |]; exact Hnext.
    + apply fib_l4_doubling_step; assumption.
  - exists prefix; repeat split; assumption.
Qed.

(** Specification/proof-only exact accumulated cost: the charged mask scan
    adds one tick per bit to the eleven-tick doubling loop. *)
Definition fib_l4_cost input :=
  match input with 0 => 9 | S _ => 8 + 12 * (Nat.log2 input + 1) end.

Lemma fib_l4_cost_bound input :
  fib_l4_cost input <= 8 + 12 * (Nat.log2 input + 1).
Proof. destruct input; unfold fib_l4_cost; cbn; lia. Qed.

Lemma fib_l4_cost_saving input : 0 < input ->
  fib_l4_cost input + (Nat.log2 input + 1) = fib_l3_cost input.
Proof. destruct input; [lia |]; unfold fib_l4_cost, fib_l3_cost; lia. Qed.

(** Compose entry, initialization, and both loops without fixing the target
    before Derive. Initial cost is arbitrary; initial array is empty. *)
Lemma fib_l4_program_count
    (program : nat -> itree (ArrayE nat +' TimeE) nat)
    (mask_body : nat * nat -> itree (ArrayE nat +' TimeE) ((nat * nat) + nat))
    (body : nat * nat -> itree (ArrayE nat +' TimeE) ((nat * nat) + nat)) :
  mask_body_rule mask_body -> fib_l4_doubling_body_rule body ->
  (forall input, program input = function_entry (fun input =>
    array_alloc 2 ;; array_set 0 0 ;; array_set 1 1 ;;
    mask <- cost_iter mask_body (input, 1) ;;
    cost_iter body (input, mask)) input) ->
  forall input cost,
    (cost + fib_l4_cost input,
      Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input)) ∈
      run_count_from (program input) [] cost.
Proof.
  intros Hmask Hbody Hprogram input cost; rewrite Hprogram.
  apply run_count_function_entry_leaf.
  apply run_count_init_pair_bind.
  eapply run_count_bind_leaf.
  - apply mask_count_all; exact Hmask.
  - rewrite Nat.mul_1_l.
    destruct input as [|input].
    + change ((cost + 9, Some ([Some (Fib_L0 0); Some (Fib_L0 1)], Fib_L0 0)) ∈
        run_count_from (cost_iter body (0, 0))
          [Some (Fib_L0 0); Some (Fib_L0 1)] ((S cost + 5) + 1)).
      replace (cost + 9) with (((S cost + 5) + 1) + 2) by lia.
      apply fib_l4_doubling_zero; exact Hbody.
    + change ((cost + (8 + 12 * (Nat.log2 (S input) + 1)),
          Some ([Some (Fib_L0 (S input)); Some (Fib_L0 (S (S input)))], Fib_L0 (S input))) ∈
        run_count_from (cost_iter body (S input, 2 ^ Nat.log2 (S input)))
          [Some (Fib_L0 0); Some (Fib_L0 1)]
          ((S cost + 5) + (Nat.log2 (S input) + 1))).
      replace (cost + (8 + 12 * (Nat.log2 (S input) + 1)))
        with (((S cost + 5) + (Nat.log2 (S input) + 1)) +
          11 * S (Nat.log2 (S input)) + 2) by lia.
      apply fib_l4_doubling_count; [exact Hbody | | lia].
      pose proof (Nat.log2_spec (S input) ltac:(lia)) as Hlog.
      cbn [Nat.pow] in Hlog; nia.
Qed.

Derive (Fib_L4 : nat -> itree (ArrayE nat +' TimeE) nat) in
  (Spec_L4 Fib_L4) as Fib_L4_spec.
Proof.
  [Fib_L4]: refine (fun input => function_entry (fun input =>
    array_alloc 2 ;; array_set 0 0 ;; array_set 1 1 ;;
    mask <- cost_iter (fun state =>
      let '(quotient, mask) := state in
      match quotient with
      | 0 => Ret (inr 0) | 1 => Ret (inr mask)
      | S (S _) => Ret (inl (Nat.div2 quotient, mask + mask))
      end) (input, 1) ;;
    cost_iter (fun state =>
      let '(remaining, mask) := state in
      match mask with
      | 0 => value <- array_read 0 ;; Ret (inr value)
      | S _ =>
          let bit := mask <=? remaining in
          let remaining' := if bit then remaining - mask else remaining in
          a <- array_read 0 ;; b <- array_read 1 ;;
          next_a <- (if bit then
            aa <- cost_mul a a ;; bb <- cost_mul b b ;; cost_add aa bb
            else twice_b <- cost_add b b ;; difference <- cost_sub twice_b a ;;
              cost_mul a difference) ;;
          next_b <- (if bit then
            twice_a <- cost_add a a ;; sum <- cost_add twice_a b ;; cost_mul b sum
            else aa <- cost_mul a a ;; bb <- cost_mul b b ;; cost_add aa bb) ;;
          array_set 0 next_a ;; array_set 1 next_b ;;
          Ret (inl (remaining', Nat.div2 mask))
      end) (input, mask)) input).
  assert (Hexact : forall input cost,
    (cost + fib_l4_cost input,
      Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input)) ∈
      run_count_from (Fib_L4 input) [] cost).
  { eapply fib_l4_program_count; [| | intros; reflexivity].
    - unfold mask_body_rule; intros; reflexivity.
    - unfold fib_l4_doubling_body_rule; intros; reflexivity. }
  exists 12, 8, 2; split; [lia |]; split; [lia |]; split; [lia |].
  intro input; split.
  - rewrite (closed_leaf_eutt _ _ (Hexact input 0)), Fib_L3_count.
    apply eutt_Ret; cbn; repeat split; try lia.
    apply fib_l4_cost_bound.
  - eapply closed_leaf_finite; exact (Hexact input 0).
Qed.

Theorem Fib_L4_count_from input cost :
  (cost + fib_l4_cost input,
    Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input)) ∈
    run_count_from (Fib_L4 input) [] cost.
Proof.
  eapply fib_l4_program_count; [| | intros; reflexivity].
  - unfold mask_body_rule; intros; reflexivity.
  - unfold fib_l4_doubling_body_rule; intros; reflexivity.
Qed.

Theorem Fib_L4_leaf input :
  (fib_l4_cost input,
    Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input)) ∈
    run_count (Fib_L4 input).
Proof. exact (Fib_L4_count_from input 0). Qed.

Theorem Fib_L4_count input :
  run_count (Fib_L4 input) ≈
    Ret (fib_l4_cost input,
      Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input)).
Proof. apply closed_leaf_eutt, Fib_L4_leaf. Qed.

Theorem Fib_L4_terminates input : all_finite (run_count (Fib_L4 input)).
Proof. eapply closed_leaf_finite; apply Fib_L4_leaf. Qed.

Theorem Fib_L4_erases input :
  run_ignore (Fib_L4 input) ≈
    Ret (Some ([Some (Fib_L0 input); Some (Fib_L0 (S input))], Fib_L0 input)).
Proof.
  apply closed_leaf_eutt; eapply count_leaf_ignore; apply Fib_L4_leaf.
Qed.

(** Every satisfying program inherits the constant bound at canonical
    residuals from termination, success, and nondecreasing array length. *)
Theorem Spec_L4_intermediate_bound program_l4 : Spec_L4 program_l4 ->
  exists space_constant, 0 < space_constant /\ forall input tail array cost,
    subtree (run_count_from tail array cost) (run_count (program_l4 input)) ->
    length array <= space_constant.
Proof.
  intros [time_constant [additive_constant [space_constant [Ht [Hlt [Hs Hspec]]]]]].
  exists space_constant; split; [exact Hs |].
  intros input; destruct (Hspec input) as [Hrel Hfin].
  apply final_bound_subtree; [exact Hfin |].
  intros cost outcome Hleaf.
  destruct (Leaf_eutt_l _ _ _ Hrel Hleaf)
    as [[cost_l3 outcome_l3] [Hreference Hpost]].
  destruct outcome as [[array_l4 result_l4]|];
    destruct outcome_l3 as [[array_l3 result_l3]|]; try contradiction.
  exact (proj2 (proj2 Hpost)).
Qed.

Theorem Fib_L4_intermediate_bound input tail array cost :
  subtree (run_count_from tail array cost) (run_count (Fib_L4 input)) ->
  length array <= 2.
Proof.
  eapply final_bound_subtree_leaf; [apply Fib_L4_leaf | cbn; lia].
Qed.

Theorem Fib_L4_handler_intermediate_bound input :
  forall X (event : (ArrayE nat +' TimeE) X)
    (continuation : X -> itree (ArrayE nat +' TimeE) nat) array
    (pending : itree TimeE (option (array_state nat * X))) cost,
    subtree pending (unOptionT (h_effects X event array)) ->
    subtree
      (count_from (outcome <- pending ;; match outcome with
        | None => Ret None
        | Some (array', value) => Tau (array_to_time_from (continuation value) array')
        end) cost)
      (run_count (Fib_L4 input)) -> length array <= 2.
Proof.
  eapply final_bound_handler_subtree_leaf; [apply Fib_L4_leaf | cbn; lia].
Qed.

(** This compares exact accumulated costs, rather than bound witnesses. *)
Theorem Fib_L4_improves_L3 input : 0 < input ->
  fib_l4_cost input < fib_l3_cost input.
Proof. intro H; pose proof (fib_l4_cost_saving input H); lia. Qed.
