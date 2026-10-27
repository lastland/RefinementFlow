From Stdlib Require Import Arith Lia.
From RefineToITree Require Export Array.
Import ITreeNotations LeafNotations SumNotations.
Local Open Scope itree_scope.
Local Open Scope sum_scope.

(** Proof-only control arithmetic: logarithms and powers describe the mask,
    without prescribing executable target code. *)
Lemma div2_bounds input :
  2 * Nat.div2 input <= input < 2 * S (Nat.div2 input).
Proof.
  pose proof (Nat.div2_odd input) as Hdecomposition.
  destruct (Nat.odd input); cbn in Hdecomposition; lia.
Qed.

Lemma log2_div2 input :
  2 <= input -> Nat.log2 input = S (Nat.log2 (Nat.div2 input)).
Proof.
  intro Hinput.
  pose proof (div2_bounds input) as Hbounds.
  set (half := Nat.div2 input) in *.
  assert (Hhalf : 0 < half) by lia.
  assert (Hcases : input = 2 * half \/ input = 2 * half + 1) by lia.
  destruct Hcases as [Heven | Hodd].
  - transitivity (Nat.log2 (2 * half)).
    + exact (f_equal Nat.log2 Heven).
    + apply Nat.log2_double; exact Hhalf.
  - transitivity (Nat.log2 (2 * half + 1)).
    + exact (f_equal Nat.log2 Hodd).
    + apply Nat.log2_succ_double; exact Hhalf.
Qed.

(* Proof-only witnesses for the charged mask scan, including its zero exit. *)
Definition binary_mask input :=
  match input with 0 => 0 | S _ => 2 ^ Nat.log2 input end.

Definition mask_scan_cost input :=
  match input with 0 => 1 | S _ => Nat.log2 input + 1 end.

(** Removing the next most significant bit extends the processed prefix.
    This scalar invariant is independent of array contents. *)
Lemma binary_prefix_step target prefix remaining mask :
  0 < mask -> remaining < 2 * mask ->
  target = prefix * (2 * mask) + remaining ->
  let bit := mask <=? remaining in
  let prefix' := if bit then 2 * prefix + 1 else 2 * prefix in
  let remaining' := if bit then remaining - mask else remaining in
  remaining' < mask /\ target = prefix' * mask + remaining'.
Proof.
  intros Hmask Hremaining Htarget.
  destruct (mask <=? remaining) eqn:Hbit; cbn.
  - apply Nat.leb_le in Hbit; split; nia.
  - apply Nat.leb_gt in Hbit; split; nia.
Qed.

(** The same control step at a power-of-two mask, including the last bit.
    The rank and processed prefix remain proof data, not loop state. *)
Lemma binary_prefix_rank_step target prefix remaining exponent :
  remaining < 2 * 2 ^ exponent ->
  target = prefix * (2 * 2 ^ exponent) + remaining ->
  let mask := 2 ^ exponent in
  let bit := mask <=? remaining in
  let prefix' := if bit then 2 * prefix + 1 else 2 * prefix in
  let remaining' := if bit then remaining - mask else remaining in
  0 < mask /\
  match exponent with
  | 0 => Nat.div2 mask = 0 /\ remaining' = 0 /\ prefix' = target
  | S exponent' => Nat.div2 mask = 2 ^ exponent' /\
      remaining' < 2 * Nat.div2 mask /\
      target = prefix' * (2 * Nat.div2 mask) + remaining'
  end.
Proof.
  intros Hremaining Htarget; cbn zeta.
  assert (Hpositive : 0 < 2 ^ exponent).
  { pose proof (Nat.pow_nonzero 2 exponent ltac:(lia)); lia. }
  split; [exact Hpositive |].
  pose proof (binary_prefix_step target prefix remaining (2 ^ exponent)
    Hpositive Hremaining Htarget) as Hstep.
  cbn zeta in Hstep; destruct Hstep as [Hr Ht].
  destruct exponent as [|exponent].
  - cbn [Nat.pow Nat.div2] in *; repeat split; lia.
  - change (Nat.div2 (2 * 2 ^ exponent) = 2 ^ exponent /\
      (if 2 ^ S exponent <=? remaining then remaining - 2 ^ S exponent else remaining)
        < 2 * Nat.div2 (2 * 2 ^ exponent) /\
      target = (if 2 ^ S exponent <=? remaining then 2 * prefix + 1 else 2 * prefix)
        * (2 * Nat.div2 (2 * 2 ^ exponent)) +
        (if 2 ^ S exponent <=? remaining then remaining - 2 ^ S exponent else remaining)).
    rewrite Nat.div2_double.
    cbn [Nat.pow] in Hr, Ht |- *; repeat split; nia.
Qed.

Definition mask_body_rule {A}
    (body : nat * nat -> itree (ArrayE A +' TimeE) ((nat * nat) + nat))
    : Prop :=
  forall quotient scale, body (quotient, scale) =
    match quotient with
    | 0 => Ret (inr 0)
    | 1 => Ret (inr scale)
    | S (S _) => Ret (inl (Nat.div2 quotient, scale + scale))
    end.

(** Each invocation, including the exit check, costs one iteration-entry tick.
    Halving and scale updates are control arithmetic; the array is unchanged. *)
Lemma mask_count {A}
    (body : nat * nat -> itree (ArrayE A +' TimeE) ((nat * nat) + nat)) :
  mask_body_rule body ->
  forall input, 0 < input -> forall scale (array : array_state A) cost,
    (cost + (Nat.log2 input + 1), Some (array, scale * 2 ^ Nat.log2 input))
      ∈ run_count_from (cost_iter body (input, scale)) array cost.
Proof.
  intros Hbody; unfold mask_body_rule in Hbody.
  intro input; induction input using (well_founded_induction lt_wf).
  intros Hpositive scale array cost.
  destruct input as [|[|input]]; [lia | |].
  - cbn [Nat.log2 Nat.log2_iter Nat.pred Nat.pow].
    rewrite Nat.mul_1_r.
    eapply run_count_cost_iter_step with (cost' := S cost)
      (array' := array) (step := inr scale).
    + rewrite Hbody; apply run_count_from_ret; reflexivity.
    + cbn; f_equal; lia.
  - set (input' := S (S input)) in *.
    pose proof (div2_bounds input') as Hbounds.
    assert (Hhalf : 0 < Nat.div2 input') by (unfold input' in *; lia).
    pose proof (log2_div2 input' ltac:(unfold input'; lia)) as Hlog.
    eapply run_count_cost_iter_step with (cost' := S cost)
      (array' := array) (step := inl (Nat.div2 input', scale + scale)).
    + rewrite Hbody; apply run_count_from_ret; reflexivity.
    + change ((cost + (Nat.log2 input' + 1),
        Some (array, scale * 2 ^ Nat.log2 input')) ∈
        run_count_from (cost_iter body
          (Nat.div2 input', scale + scale)) array (S cost)).
      replace (cost + (Nat.log2 input' + 1))
        with (S cost + (Nat.log2 (Nat.div2 input') + 1)) by lia.
      replace (scale * 2 ^ Nat.log2 input')
        with ((scale + scale) * 2 ^ Nat.log2 (Nat.div2 input')).
      * apply H; [apply Nat.lt_div2; unfold input'; lia | exact Hhalf].
      * rewrite Hlog; cbn [Nat.pow]; nia.
Qed.

(** The zero case needs only its exit equation, not the full body rule. *)
Lemma mask_zero {A}
    (body : nat * nat -> itree (ArrayE A +' TimeE) ((nat * nat) + nat)) :
  (forall scale, body (0, scale) = Ret (inr 0)) ->
  forall scale (array : array_state A) cost,
    (cost + 1, Some (array, 0)) ∈
      run_count_from (cost_iter body (0, scale)) array cost.
Proof.
  intros Hbody scale array cost.
  eapply run_count_cost_iter_step with (cost' := S cost)
    (array' := array) (step := inr 0).
  - rewrite Hbody; apply run_count_from_ret; reflexivity.
  - cbn; f_equal; lia.
Qed.

(** Uniform scan rule: scale and the unchanged array are arbitrary. *)
Lemma mask_count_all {A}
    (body : nat * nat -> itree (ArrayE A +' TimeE) ((nat * nat) + nat)) :
  mask_body_rule body ->
  forall input scale (array : array_state A) cost,
    (cost + mask_scan_cost input, Some (array, scale * binary_mask input)) ∈
      run_count_from (cost_iter body (input, scale)) array cost.
Proof.
  intros Hbody [|input] scale array cost.
  - cbn [binary_mask mask_scan_cost]; rewrite Nat.mul_0_r.
    apply mask_zero; intros; apply Hbody.
  - apply mask_count; [exact Hbody | lia].
Qed.
