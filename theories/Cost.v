From Stdlib Require Import Arith Lia.
From Paco Require Import paco.
From ITree Require Export ITree ITreeFacts Events.State.
From ITree.Events Require Import StateFacts.
From ITree.Props Require Export HasPost Finite Leaf.
Import ITreeNotations LeafNotations HasPostNotations.
Local Open Scope itree_scope.

(** Time is write-only: every event denotes exactly one abstract cost unit. *)
Variant TimeE : Type -> Type := Tick : TimeE unit.
Definition tick : itree TimeE unit := trigger Tick.

Definition function_entry {E Input Result} `{TimeE -< E}
    (program : Input -> itree E Result) (input : Input) : itree E Result :=
  trigger Tick ;; program input.

Definition iter_body_entry {E State Result} `{TimeE -< E}
    (program : State -> itree E (State + Result)) (state : State)
    : itree E (State + Result) :=
  trigger Tick ;; program state.

(** The callback is charged here, including its terminating invocation.
    It must not receive a second function-entry charge just for being a
    Gallina function. Control/index work is included in this entry charge. *)
Definition cost_iter {E State Result} `{TimeE -< E}
    (program : State -> itree E (State + Result)) (state : State)
    : itree E Result :=
  ITree.iter (iter_body_entry program) state.

Definition cost_add {E} `{TimeE -< E} (left right : nat) : itree E nat :=
  trigger Tick ;; Ret (left + right).

Definition cost_mul {E} `{TimeE -< E} (left right : nat) : itree E nat :=
  trigger Tick ;; Ret (left * right).

Definition cost_sub {E} `{TimeE -< E} (left right : nat) : itree E nat :=
  trigger Tick ;; Ret (left - right).

Definition h_count (Result : Type) (event : TimeE Result) (cost : nat)
    : itree void1 (nat * Result) :=
  match event with Tick => Ret (S cost, tt) end.
Definition count_from {Result} (program : itree TimeE Result) (cost : nat)
    : itree void1 (nat * Result) := interp_state h_count program cost.
Definition count {Result} (program : itree TimeE Result) := count_from program 0.
Definition h_ignore (Result : Type) (event : TimeE Result) : itree void1 Result :=
  match event with Tick => Ret tt end.
Definition ignore_time {Result} (program : itree TimeE Result) : itree void1 Result :=
  interp h_ignore program.
Definition time_reply {Result} (event : TimeE Result) : Result :=
  match event with Tick => tt end.

(** Direct observation equations avoid dependent inversion/UIP. *)
Lemma observe_count Result (program : itree TimeE Result) cost :
  observe (count_from program cost) =
  match observe program with
  | RetF result => RetF (cost, result)
  | TauF next => TauF (count_from next cost)
  | VisF event next => TauF (count_from (next (time_reply event)) (S cost))
  end.
Proof.
  unfold count_from, interp_state, interp, Basics.iter, MonadIter_stateT0,
    Basics.iter, MonadIter_itree.
  unfold ITree.iter, ITree.bind, ITree.map, ITree.subst, observe; cbn.
  destruct (_observe program); try reflexivity; destruct e; reflexivity.
Qed.
Lemma observe_ignore Result (program : itree TimeE Result) :
  observe (ignore_time program) =
  match observe program with
  | RetF result => RetF result
  | TauF next => TauF (ignore_time next)
  | VisF event next => TauF (ignore_time (next (time_reply event)))
  end.
Proof.
  unfold ignore_time, interp, Basics.iter, MonadIter_itree.
  unfold ITree.iter, ITree.bind, ITree.map, ITree.subst, observe; cbn.
  destruct (_observe program); try reflexivity; destruct e; reflexivity.
Qed.
Lemma count_tick cost :
  observe (count_from tick cost) = TauF (count_from (Ret tt) (S cost)).
Proof. reflexivity. Qed.

Theorem count_ignore_result Result (program : itree TimeE Result) cost :
  eutt (fun counted result => snd counted = result)
    (count_from program cost) (ignore_time program).
Proof.
  revert program cost; pcofix CIH; intros program cost; pstep; red.
  rewrite observe_count, observe_ignore.
  destruct (observe program) as [result | next | X event next]; cbn.
  - constructor; reflexivity.
  - constructor; right; apply CIH.
  - destruct event; cbn; constructor; right; apply CIH.
Qed.

(** Closed trees are deterministic: a finite return witness also establishes
    termination and its postconditions. No generic visible-event inversion
    or axiomatic extensionality is needed. *)
Lemma closed_leaf_finite {Result} (program : itree void1 Result) result :
  result ∈ program -> all_finite program.
Proof.
  intro H; induction H as [program H | program next H Hleaf IH |
    X event program next value H Hleaf IH].
  - eapply all_finiteRet; exact H.
  - eapply all_finiteTau; eassumption.
  - destruct event.
Qed.
Lemma closed_leaf_eutt {Result} (program : itree void1 Result) result :
  result ∈ program -> program ≈ Ret result.
Proof.
  intro H; induction H as [program H | program next H Hleaf IH |
    X event program next value H Hleaf IH].
  - rewrite (itree_eta program), H; reflexivity.
  - rewrite (itree_eta program), H; cbn; apply eqit_Tau_l; exact IH.
  - destruct event.
Qed.
Lemma closed_leaf_has_post {Result} (program : itree void1 Result) result
    (post : Result -> Prop) :
  result ∈ program -> post result -> program ⤳ post.
Proof.
  intros H Hpost; unfold has_post.
  induction H as [program H | program next H Hleaf IH |
    X event program next value H Hleaf IH].
  - pstep; red; rewrite H; constructor; exact Hpost.
  - pstep; red; rewrite !H; apply EqTau; left; exact IH.
  - destruct event.
Qed.

(** A returned value in an interpretation comes from a source return. These
    facts are independent of the interpreted effects and resource model. *)
Lemma interp_leaf_source {E F R} (handler : E ~> itree F) (program : itree E R) value :
  value ∈ interp handler program -> value ∈ program.
Proof.
  intro H.
  assert (Hsub : Subtree.subtree program program) by (constructor; reflexivity).
  pose proof (Subtree.Leaf_interp_subtree_inv handler program program Hsub) as Hpost.
  destruct (Leaf_eutt_l _ _ _ Hpost H) as [x [_ Hsource]]; exact Hsource.
Qed.

Lemma interp_state_leaf_source {E F S R}
    (handler : E ~> Monads.stateT S (itree F)) (program : itree E R) state value :
  value ∈ interp_state handler program state -> snd value ∈ program.
Proof.
  intro H.
  assert (Hsub : Subtree.subtree program program) by (constructor; reflexivity).
  pose proof (Subtree.Leaf_interp_state_subtree_inv handler program program state Hsub) as Hpost.
  destruct (Leaf_eutt_l _ _ _ Hpost H) as [x [_ Hsource]]; exact Hsource.
Qed.

(** Accumulation rule: the continuation receives the actual final counter,
    not a program-selected writer total. *)
Lemma count_bind_leaf {Input Result} (program : itree TimeE Input)
    (next : Input -> itree TimeE Result) cost middle final input result :
  (middle, input) ∈ count_from program cost ->
  (final, result) ∈ count_from (next input) middle ->
  (final, result) ∈ count_from (program >>= next) cost.
Proof.
  intros Hprogram Hnext; unfold count_from in *.
  rewrite interp_state_bind.
  eapply Leaf_bind; [exact Hprogram | exact Hnext].
Qed.
Lemma count_function_entry_leaf {Input Result}
    (program : Input -> itree TimeE Result) input cost final result :
  (final, result) ∈ count_from (program input) (S cost) ->
  (final, result) ∈ count_from (function_entry program input) cost.
Proof.
  intro H; unfold function_entry.
  eapply count_bind_leaf; [| exact H].
  eapply LeafTau; [rewrite observe_count; reflexivity |].
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.
Lemma count_add_leaf left right cost :
  (S cost, left + right) ∈ count_from (cost_add left right) cost.
Proof.
  eapply LeafTau; [rewrite observe_count; reflexivity |].
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.
Lemma count_mul_leaf left right cost :
  (S cost, left * right) ∈ count_from (cost_mul left right) cost.
Proof.
  eapply LeafTau; [rewrite observe_count; reflexivity |].
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.
Lemma count_sub_leaf left right cost :
  (S cost, left - right) ∈ count_from (cost_sub left right) cost.
Proof.
  eapply LeafTau; [rewrite observe_count; reflexivity |].
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.
Lemma count_iter_body_entry_leaf {State Result}
    (program : State -> itree TimeE (State + Result)) state cost final result :
  (final, result) ∈ count_from (program state) (S cost) ->
  (final, result) ∈ count_from (iter_body_entry program state) cost.
Proof. apply count_function_entry_leaf. Qed.
Lemma count_iter_terminal_leaf {State Result} (state : State) (result : Result) cost :
  (S cost, result) ∈
    count_from (cost_iter (fun _ : State => Ret (inr result)) state) cost.
Proof.
  eapply LeafTau; [rewrite observe_count; reflexivity |].
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.
Lemma count_leaf_ignore {Result} (program : itree TimeE Result) cost result :
  (cost, result) ∈ count program -> result ∈ ignore_time program.
Proof.
  intro H.
  destruct (Leaf_eutt_l _ _ _ (count_ignore_result Result program 0) H)
    as [value [Hleaf Heq]].
  cbn in Heq; subst; exact Hleaf.
Qed.

(** Changing the initial counter shifts the accumulated total, preserving the
    computation and its result. *)
Lemma count_offset R (program : itree TimeE R) initial extra :
  eutt (fun '(c,x) '(d,y) => c + extra = d /\ x = y)
    (count_from program initial) (count_from program (initial + extra)).
Proof.
  revert program initial; pcofix CIH; intros program initial; pstep; red.
  rewrite !observe_count.
  destruct (observe program) as [x|next|X event next]; cbn.
  - constructor; split; reflexivity.
  - constructor; right; apply CIH.
  - destruct event; cbn; constructor; right.
    replace (S (initial + extra)) with (S initial + extra) by lia.
    apply CIH.
Qed.
Lemma count_shift_leaf R (program : itree TimeE R) work value extra :
  (work,value) ∈ count program -> (extra+work,value) ∈ count_from program extra.
Proof.
  intro H.
  destruct (Leaf_eutt_l _ _ _ (count_offset R program 0 extra) H)
    as [[cost result] [Hleaf [Hcost Hvalue]]].
  cbn in Hcost, Hvalue; subst result.
  replace (extra + work) with cost by lia; exact Hleaf.
Qed.

(** Sequential, array-free loops use the same entry discipline as array loops.
    The rank and invariant are proof data, not executable countdowns. *)
Lemma count_ret_leaf {R} (result : R) cost :
  (cost, result) ∈ count_from (Ret result) cost.
Proof. apply LeafRet; rewrite observe_count; reflexivity. Qed.

Lemma count_cost_iter_step {State R}
    (body : State -> itree TimeE (State + R)) state cost middle step final result :
  (middle, step) ∈ count_from (body state) (S cost) ->
  (match step with
   | inl next => (final, result) ∈ count_from (cost_iter body next) middle
   | inr value => (final, result) = (middle, value)
   end) ->
  (final, result) ∈ count_from (cost_iter body state) cost.
Proof.
  intros Hbody Hnext; unfold cost_iter; rewrite unfold_iter.
  eapply count_bind_leaf; [apply count_iter_body_entry_leaf; exact Hbody |].
  destruct step as [next|value]; cbn in *.
  - eapply LeafTau; [rewrite observe_count; reflexivity | exact Hnext].
  - inversion Hnext; subst; apply count_ret_leaf.
Qed.

Lemma count_cost_iter_rank_invariant {State R}
    (body : State -> itree TimeE (State + R))
    (invariant : nat -> State -> Prop) (step_cost exit_cost : nat) (result : R) :
  (forall state cost, invariant 0 state ->
    (cost + exit_cost, inr result) ∈ count_from (body state) (S cost)) ->
  (forall remaining state cost, invariant (S remaining) state ->
    exists state', invariant remaining state' /\
      (cost + step_cost, inl state') ∈ count_from (body state) (S cost)) ->
  forall remaining state cost, invariant remaining state ->
    (cost + step_cost * remaining + exit_cost, result) ∈
      count_from (cost_iter body state) cost.
Proof.
  intros Hzero Hstep remaining; induction remaining as [|remaining IH];
    intros state cost Hinv.
  - eapply count_cost_iter_step with (middle := cost + exit_cost)
      (step := inr result); [apply Hzero; exact Hinv |].
    rewrite Nat.mul_0_r, Nat.add_0_r; reflexivity.
  - destruct (Hstep remaining state cost Hinv) as [state' [Hinv' Hbody]].
    eapply count_cost_iter_step with (middle := cost + step_cost)
      (step := inl state'); [exact Hbody |].
    cbn -[Nat.mul Nat.add].
    rewrite Nat.mul_succ_r.
    replace (cost + (step_cost * remaining + step_cost) + exit_cost)
      with ((cost + step_cost) + step_cost * remaining + exit_cost) by lia.
    apply IH; exact Hinv'.
Qed.

(** Observation fuel bounds evaluation only; it is not accumulated cost. *)
Fixpoint observe_closed {Result} (fuel : nat) (program : itree void1 Result)
    : option Result :=
  match fuel with
  | 0 => None
  | S remaining => match observe program with
    | RetF result => Some result
    | TauF next => observe_closed remaining next
    | VisF event _ => match event with end
    end
  end.
Lemma observe_closed_leaf {Result} fuel (program : itree void1 Result) result :
  observe_closed fuel program = Some result -> result ∈ program.
Proof.
  revert program; induction fuel as [|fuel IH]; intros program H; cbn in H.
  - discriminate.
  - destruct (observe program) as [value | next | X event next] eqn:Hprogram.
    + inversion H; subst; apply LeafRet; exact Hprogram.
    + eapply LeafTau; [exact Hprogram | apply IH; exact H].
    + destruct event.
Qed.
Lemma observe_closed_terminates {Result} fuel (program : itree void1 Result) result :
  observe_closed fuel program = Some result -> all_finite program.
Proof.
  intro H; apply (closed_leaf_finite program result).
  eapply observe_closed_leaf; exact H.
Qed.
