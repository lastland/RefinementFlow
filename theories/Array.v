From Stdlib Require Import List Arith Lia Morphisms.
From Paco Require Import paco.
From ExtLib Require Export Data.Monads.OptionMonad.
From ITree Require Import Events.State Events.StateFacts.
From RefineToITree Require Export Cost.
Import ListNotations.
Import Subtree.
Import ITreeNotations LeafNotations HasPostNotations SumNotations.
Local Open Scope itree_scope.
Local Open Scope sum_scope.

(** Flat, append-only allocation; uninitialized cells count as space. *)
Variant ArrayE (A : Type) : Type -> Type :=
| ArrayAlloc : nat -> ArrayE A nat
| ArrayRead : nat -> ArrayE A A
| ArraySet : nat -> A -> ArrayE A unit.
Arguments ArrayAlloc {A} _.
Arguments ArrayRead {A} _.
Arguments ArraySet {A} _ _.

Definition array_alloc {A E} `{ArrayE A -< E} (size : nat) : itree E nat :=
  trigger (ArrayAlloc size).
Definition array_read {A E} `{ArrayE A -< E} (index : nat) : itree E A :=
  trigger (ArrayRead index).
Definition array_set {A E} `{ArrayE A -< E} (index : nat) (value : A)
    : itree E unit := trigger (ArraySet index value).

Definition array_state (A : Type) := list (option A).

Fixpoint set_cell {A} (index : nat) (value : A) (array : array_state A)
    : array_state A :=
  match array, index with
  | [], _ => []
  | _ :: tail, 0 => Some value :: tail
  | cell :: tail, S index' => cell :: set_cell index' value tail
  end.

Definition array_step {A X} (event : ArrayE A X) (array : array_state A)
    : option (array_state A * X) :=
  match event with
  | ArrayAlloc size => Some (array ++ repeat None size, length array)
  | ArrayRead index =>
      match nth_error array index with
      | Some (Some value) => Some (array, value)
      | _ => None
      end
  | ArraySet index value =>
      if index <? length array then Some (set_cell index value array, tt)
      else None
  end.

Lemma alloc_behavior A size (array : array_state A) :
  array_step (ArrayAlloc size) array =
    Some (array ++ repeat None size, length array).
Proof. reflexivity. Qed.
Lemma alloc_length A size (array : array_state A) :
  length (array ++ repeat (@None A) size) = length array + size.
Proof. rewrite length_app, repeat_length; reflexivity. Qed.
Lemma read_initialized A index (array : array_state A) value :
  nth_error array index = Some (Some value) ->
  array_step (ArrayRead index) array = Some (array, value).
Proof. intro H; unfold array_step; rewrite H; reflexivity. Qed.
Lemma read_uninitialized A index (array : array_state A) :
  nth_error array index = Some None -> array_step (ArrayRead index) array = None.
Proof. intro H; unfold array_step; rewrite H; reflexivity. Qed.
Lemma read_oob A index (array : array_state A) :
  nth_error array index = None -> array_step (ArrayRead index) array = None.
Proof. intro H; unfold array_step; rewrite H; reflexivity. Qed.
Lemma read_bounds A index (array : array_state A) :
  length array <= index -> array_step (ArrayRead index) array = None.
Proof. intro H; apply read_oob, nth_error_None; exact H. Qed.
Lemma alloc_fresh A size (array : array_state A) offset :
  offset < size ->
  nth_error (array ++ repeat (@None A) size) (length array + offset) = Some None.
Proof.
  intro H; rewrite nth_error_app2 by lia.
  replace (length array + offset - length array) with offset by lia.
  apply nth_error_repeat; exact H.
Qed.
Lemma set_valid A index (value : A) array :
  index < length array ->
  array_step (ArraySet index value) array = Some (set_cell index value array, tt).
Proof. intro H; unfold array_step; apply Nat.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma set_oob A index (value : A) array :
  length array <= index -> array_step (ArraySet index value) array = None.
Proof.
  intro H; unfold array_step; destruct (index <? length array) eqn:Hi;
    [apply Nat.ltb_lt in Hi; lia | reflexivity].
Qed.
Lemma set_cell_length A index (value : A) array :
  length (set_cell index value array) = length array.
Proof. revert index; induction array as [|cell tail IH]; intros [|index]; cbn; auto. Qed.
Lemma set_cell_same A index (value : A) array :
  index < length array -> nth_error (set_cell index value array) index = Some (Some value).
Proof.
  revert index; induction array as [|cell tail IH]; intros [|index] H; cbn in *;
    try lia; auto; apply IH; lia.
Qed.
Lemma set_cell_other A index other (value : A) array :
  other <> index -> nth_error (set_cell index value array) other = nth_error array other.
Proof.
  revert index other; induction array as [|cell tail IH];
    intros [|index] [|other] H; cbn; auto; try contradiction.
Qed.
Lemma read_success_length A index (array array' : array_state A) value :
  array_step (ArrayRead index) array = Some (array', value) ->
  length array' = length array.
Proof.
  cbn; destruct (nth_error array index) as [[x|]|]; intro H; inversion H; reflexivity.
Qed.
Lemma set_success_length A index (value : A) array array' result :
  array_step (ArraySet index value) array = Some (array', result) ->
  length array' = length array.
Proof.
  unfold array_step; destruct (index <? length array); intro H; inversion H; subst.
  apply set_cell_length.
Qed.
Lemma step_success_monotone A X (event : ArrayE A X) array array' result :
  array_step event array = Some (array', result) -> length array <= length array'.
Proof.
  destruct event as [size|index|index value]; intro H.
  - cbn in H; inversion H; subst; rewrite alloc_length; lia.
  - pose proof (read_success_length A index array array' result H); lia.
  - pose proof (set_success_length A index value array array' result H); lia.
Qed.

(** Only this private helper repeats ticks. There is no weighted time event.
    Its zero case still emits the operation's overhead tick. *)
Local Fixpoint allocation_ticks {R} (size : nat) (tail : itree TimeE R)
    : itree TimeE R :=
  match size with
  | 0 => Vis Tick (fun _ => tail)
  | S size' => Vis Tick (fun _ => allocation_ticks size' tail)
  end.

Definition h_array_time {A} (X : Type) (event : ArrayE A X) (array : array_state A)
    : optionT (itree TimeE) (array_state A * X) :=
  mkOptionT
    (match event as event' in ArrayE _ Y
       return itree TimeE (option (array_state A * Y)) with
     | ArrayAlloc size => allocation_ticks size (Ret (array_step (ArrayAlloc size) array))
     | ArrayRead index => Vis Tick (fun _ => Ret (array_step (ArrayRead index) array))
     | ArraySet index value => Vis Tick (fun _ => Ret (array_step (ArraySet index value) array))
     end).

Definition h_effects {A} (X : Type) (event : (ArrayE A +' TimeE) X)
    (array : array_state A) : optionT (itree TimeE) (array_state A * X) :=
  match event with
  | (event' |) => h_array_time X event' array
  | (| event') => mkOptionT (result <- trigger event' ;;
      Ret (Some (array, result)))
  end.
Definition array_to_time_from {A R} (program : itree (ArrayE A +' TimeE) R)
    (array : array_state A) : itree TimeE (option (array_state A * R)) :=
  unOptionT (interp_state h_effects program array).
Definition array_to_time {A R} (program : itree (ArrayE A +' TimeE) R) :=
  array_to_time_from program [].
Definition run_count_from {A R} (program : itree (ArrayE A +' TimeE) R)
    (array : array_state A) (initial_cost : nat) :=
  count_from (array_to_time_from program array) initial_cost.
Definition run_count {A R} (program : itree (ArrayE A +' TimeE) R) :=
  run_count_from program [] 0.
Definition run_ignore {A R} (program : itree (ArrayE A +' TimeE) R) :=
  ignore_time (array_to_time program).
Theorem arrays_count_ignore_result A R (program : itree (ArrayE A +' TimeE) R) :
  eutt (fun counted result => snd counted = result) (run_count program) (run_ignore program).
Proof. apply count_ignore_result. Qed.
Theorem arrays_count_ignore_result_from A R (program : itree (ArrayE A +' TimeE) R)
    array initial_cost :
  eutt (fun counted result => snd counted = result)
    (run_count_from program array initial_cost)
    (ignore_time (array_to_time_from program array)).
Proof. apply count_ignore_result. Qed.

Local Lemma allocation_ticks_exact R size initial_cost (result : R) :
  (initial_cost + S size, result) ∈
    count_from (allocation_ticks size (Ret result)) initial_cost.
Proof.
  revert initial_cost; induction size as [|size IH]; intro initial_cost.
  - eapply LeafTau; [rewrite observe_count; reflexivity |].
    apply LeafRet; rewrite observe_count; cbn.
    replace (initial_cost + 1) with (S initial_cost) by lia; reflexivity.
  - eapply LeafTau; [rewrite observe_count; reflexivity |].
    replace (initial_cost + S (S size)) with (S initial_cost + S size) by lia.
    apply IH.
Qed.
Lemma alloc_time_exact A size (array : array_state A) initial_cost :
  (initial_cost + (size + 1), Some (array ++ repeat None size, length array)) ∈
    count_from (unOptionT (h_array_time nat (ArrayAlloc size) array)) initial_cost.
Proof. replace (size + 1) with (S size) by lia; apply allocation_ticks_exact. Qed.
Lemma read_attempt_time A index (array : array_state A) initial_cost :
  (S initial_cost, array_step (ArrayRead index) array) ∈
    count_from (unOptionT (h_array_time A (ArrayRead index) array)) initial_cost.
Proof.
  eapply LeafTau; [rewrite observe_count; reflexivity |].
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.
Lemma set_attempt_time A index (value : A) array initial_cost :
  (S initial_cost, array_step (ArraySet index value) array) ∈
    count_from (unOptionT (h_array_time unit (ArraySet index value) array)) initial_cost.
Proof.
  eapply LeafTau; [rewrite observe_count; reflexivity |].
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.

(** StateFacts' plain-itree law does not cover this optionT codomain. *)
Lemma unfold_state_option {E F S R}
    (handler : E ~> Monads.stateT S (optionT (itree F)))
    (program : itree E R) array :
  unOptionT (interp_state handler program array) ≅
  match observe program with
  | RetF result => Ret (Some (array, result))
  | TauF tail => Tau (unOptionT (interp_state handler tail array))
  | VisF event continuation => outcome <- unOptionT (handler _ event array) ;;
      match outcome with
        | None => Ret None
        | Some (array', result) =>
            Tau (unOptionT (interp_state handler (continuation result) array'))
        end
  end.
Proof.
  unfold interp_state, interp, Basics.iter, MonadIter_stateT0,
    Basics.iter, MonadIter_optionT, Basics.iter, MonadIter_itree; cbn.
  rewrite unfold_iter.
  cbn. destruct (observe program) eqn:Hprogram; cbn.
  - rewrite !bind_ret_l; reflexivity.
  - rewrite !bind_ret_l; reflexivity.
  - rewrite !bind_bind. setoid_rewrite bind_ret_l.
    eapply eqit_bind; [reflexivity |].
    intros [[array' result]|]; cbn; rewrite !bind_ret_l; reflexivity.
Qed.

Lemma state_option_invariant {E F S R}
    (handler : E ~> Monads.stateT S (optionT (itree F)))
    (P : S -> Prop)
    (Hhandler : forall X (event : E X) array array' result,
      P array -> Some (array', result) ∈ unOptionT (handler X event array) -> P array')
    (program : itree E R) array :
  P array -> unOptionT (interp_state handler program array) ⤳
    (fun outcome => match outcome with Some (array', _) => P array' | None => True end).
Proof.
  unfold has_post. revert program array.
  ginit. gcofix CIH. intros program array Harray.
  rewrite !unfold_state_option.
  destruct (observe program) as [result|tail|X event continuation]; cbn.
  - gstep; red; constructor; exact Harray.
  - gstep; red; constructor; gfinal; left; apply CIH; exact Harray.
  - guclo (@eqit_Leaf_clo_bind F (option (S * R)) (option (S * R))).
    econstructor; [reflexivity |].
    intros [[array' result]|] ? Hleaf _ <-; cbn.
    + gstep; red; constructor; gfinal; left; apply CIH.
      eapply Hhandler; eauto.
    + gstep; red; constructor; exact I.
Qed.

#[global] Instance eq_itree_state_option {E F S R}
    (handler : E ~> Monads.stateT S (optionT (itree F))) :
  Proper (eq_itree eq ==> eq ==> eq_itree eq)
    (fun (program : itree E R) array => unOptionT (interp_state handler program array)).
Proof.
  intros program program' Heq array array' <-.
  revert program program' Heq array.
  ginit. gcofix CIH. intros program program' Heq array.
  rewrite !unfold_state_option.
  punfold Heq; repeat red in Heq.
  destruct Heq; subst; pclearbot; try discriminate; cbn.
  - gstep; constructor; auto.
  - gstep; constructor; gfinal; left; eapply CIH; eauto.
  - guclo eqit_clo_bind. econstructor; [reflexivity|].
    intros [[next result]|] ? []; cbn.
    + gstep; constructor; gfinal; left; eapply CIH; exact (REL result).
    + gstep; constructor; reflexivity.
Qed.

Lemma state_option_bind {E F S X R}
    (handler : E ~> Monads.stateT S (optionT (itree F)))
    (program : itree E X) (continuation : X -> itree E R) array :
  unOptionT (interp_state handler (program >>= continuation) array) ≅
  (outcome <- unOptionT (interp_state handler program array) ;;
    match outcome with
      | None => Ret None
      | Some (array', result) => unOptionT (interp_state handler (continuation result) array')
      end).
Proof.
  revert program continuation array.
  ginit. gcofix CIH. intros program continuation array.
  rewrite (unfold_state_option handler (program >>= continuation) array),
    (unfold_state_option handler program array), observe_bind.
  destruct (observe program).
  - cbn -[interp_state unOptionT]; rewrite bind_ret_l.
    rewrite unfold_state_option; gfinal; right.
    eapply paco2_mon_bot with (gf := eqit_ eq false false id).
    + match goal with |- paco2 _ _ ?t ?u => change (t ≅ u) end; reflexivity.
    + intros; assumption.
  - cbn -[interp_state unOptionT]; rewrite bind_tau.
    gstep; constructor; gbase; apply CIH.
  - cbn -[interp_state unOptionT]; rewrite bind_bind.
    guclo eqit_clo_bind. econstructor; [reflexivity|].
    intros [[array' result]|] ? []; cbn -[interp_state unOptionT].
    + rewrite bind_tau. gstep; constructor.
      ITree.fold_subst. gbase; apply CIH.
    + rewrite bind_ret_l; gstep; constructor; reflexivity.
Qed.

Lemma run_count_bind A X R (program : itree (ArrayE A +' TimeE) X)
    (continuation : X -> itree (ArrayE A +' TimeE) R) array cost :
  run_count_from (program >>= continuation) array cost ≅
  (counted <- run_count_from program array cost ;;
    match snd counted with
      | None => Ret (fst counted, None)
      | Some (array', result) => run_count_from (continuation result) array' (fst counted)
      end).
Proof.
  unfold run_count_from, array_to_time_from.
  rewrite state_option_bind. unfold count_from; rewrite interp_state_bind.
  apply eqit_bind; [reflexivity|].
  intros [cost' [[array' result]|]]; cbn; [reflexivity|].
  rewrite interp_state_ret; reflexivity.
Qed.
Lemma run_count_bind_leaf A X R (program : itree (ArrayE A +' TimeE) X)
    (continuation : X -> itree (ArrayE A +' TimeE) R)
    array cost array' cost' result final_cost outcome :
  (cost', Some (array', result)) ∈ run_count_from program array cost ->
  (final_cost, outcome) ∈ run_count_from (continuation result) array' cost' ->
  (final_cost, outcome) ∈ run_count_from (program >>= continuation) array cost.
Proof.
  intros Hprogram Htail; rewrite run_count_bind.
  eapply Leaf_bind; [exact Hprogram|exact Htail].
Qed.
Lemma run_count_bind_failure A X R (program : itree (ArrayE A +' TimeE) X)
    (continuation : X -> itree (ArrayE A +' TimeE) R) array cost final_cost :
  (final_cost, None) ∈ run_count_from program array cost ->
  (final_cost, None) ∈ run_count_from (program >>= continuation) array cost.
Proof.
  intro H; rewrite run_count_bind; eapply Leaf_bind; [exact H|apply Leaf_Ret].
Qed.

#[global] Instance eq_itree_array_to_time_from A R :
  Proper (eq_itree eq ==> eq ==> eq_itree eq) (@array_to_time_from A R).
Proof. exact (eq_itree_state_option h_effects). Qed.
#[global] Instance eq_itree_run_count_from A R :
  Proper (eq_itree eq ==> eq ==> eq ==> eq_itree eq) (@run_count_from A R).
Proof.
  intros program program' Heq array array' <- cost cost' <-.
  unfold run_count_from, count_from.
  apply eq_itree_interp_state; [apply eq_itree_array_to_time_from; assumption || reflexivity|reflexivity].
Qed.

(** This unfolding law lets loop proofs use the usual ITree.iter invariant
    and the generic bind rule, rather than unfolding the interpreters. *)
Lemma run_count_iter_unfold A State R
    (body : State -> itree (ArrayE A +' TimeE) (State + R)) state array cost :
  run_count_from (ITree.iter body state) array cost ≅
  run_count_from (step <- body state ;; match step with
    | inl state' => Tau (ITree.iter body state')
    | inr result => Ret result
    end) array cost.
Proof. rewrite (unfold_iter body state); reflexivity. Qed.

(** Direct Leaf rules keep client proofs independent of dependent inversion
    of interp_state (which can otherwise introduce an unnecessary UIP axiom). *)
Lemma run_count_from_observe A R (program program' : itree (ArrayE A +' TimeE) R)
    array cost final_cost outcome :
  observe program = observe program' ->
  (final_cost, outcome) ∈ run_count_from program' array cost ->
  (final_cost, outcome) ∈ run_count_from program array cost.
Proof.
  intros Hobs Hleaf; unfold run_count_from, array_to_time_from in *.
  rewrite (unfold_state_option h_effects program array),
    (unfold_state_option h_effects program' array), Hobs in *; exact Hleaf.
Qed.
Lemma run_count_from_ret A R (program : itree (ArrayE A +' TimeE) R)
    array cost result :
  observe program = RetF result ->
  (cost, Some (array, result)) ∈ run_count_from program array cost.
Proof.
  intro Hobs; unfold run_count_from, array_to_time_from.
  rewrite (unfold_state_option h_effects program array), Hobs; cbn.
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.
Lemma run_count_from_tau A R (program tail : itree (ArrayE A +' TimeE) R)
    array cost final_cost outcome :
  observe program = TauF tail ->
  (final_cost, outcome) ∈ run_count_from tail array cost ->
  (final_cost, outcome) ∈ run_count_from program array cost.
Proof.
  intros Hobs Hleaf; unfold run_count_from, array_to_time_from in *.
  rewrite (unfold_state_option h_effects program array), Hobs; cbn.
  eapply LeafTau; [rewrite observe_count; reflexivity|exact Hleaf].
Qed.
Lemma run_count_from_event A R X (event : (ArrayE A +' TimeE) X)
    (program : itree (ArrayE A +' TimeE) R)
    (continuation : X -> itree (ArrayE A +' TimeE) R)
    array cost array' cost' result final_cost outcome :
  observe program = VisF event continuation ->
  (cost', Some (array', result)) ∈ count_from (unOptionT (h_effects X event array)) cost ->
  (final_cost, outcome) ∈ run_count_from (continuation result) array' cost' ->
  (final_cost, outcome) ∈ run_count_from program array cost.
Proof.
  intros Hobs Hhandler Htail; unfold run_count_from, array_to_time_from in *.
  rewrite (unfold_state_option h_effects program array), Hobs; cbn.
  unfold count_from in *; rewrite interp_state_bind.
  eapply Leaf_bind; [exact Hhandler|].
  cbn; rewrite interp_state_tau; apply Leaf_Tau; exact Htail.
Qed.
Lemma run_count_from_failure A R X (event : (ArrayE A +' TimeE) X)
    (program : itree (ArrayE A +' TimeE) R)
    (continuation : X -> itree (ArrayE A +' TimeE) R) array cost final_cost :
  observe program = VisF event continuation ->
  (final_cost, None) ∈ count_from (unOptionT (h_effects X event array)) cost ->
  (final_cost, None) ∈ run_count_from program array cost.
Proof.
  intros Hobs Hhandler; unfold run_count_from, array_to_time_from.
  rewrite (unfold_state_option h_effects program array), Hobs; cbn.
  unfold count_from in *; rewrite interp_state_bind.
  eapply Leaf_bind; [exact Hhandler|].
  apply LeafRet; reflexivity.
Qed.

Lemma run_count_alloc_bind A R size
    (continuation : nat -> itree (ArrayE A +' TimeE) R) array cost final_cost outcome :
  (final_cost, outcome) ∈
    run_count_from (continuation (length array))
      (array ++ repeat None size) (cost + (size + 1)) ->
  (final_cost, outcome) ∈
    run_count_from (array_alloc (A := A) size >>= continuation) array cost.
Proof.
  intro H; eapply run_count_from_event with (event := (ArrayAlloc size |)).
  - unfold array_alloc, ITree.bind, ITree.subst, ITree.trigger; cbn; reflexivity.
  - apply alloc_time_exact.
  - eapply run_count_from_observe with (program' := continuation (length array));
      [reflexivity|exact H].
Qed.
Lemma run_count_read_bind A R index (value : A)
    (continuation : A -> itree (ArrayE A +' TimeE) R) array cost final_cost outcome :
  nth_error array index = Some (Some value) ->
  (final_cost, outcome) ∈ run_count_from (continuation value) array (S cost) ->
  (final_cost, outcome) ∈
    run_count_from (array_read index >>= continuation) array cost.
Proof.
  intros Hread Htail; eapply run_count_from_event with (event := (ArrayRead index |)).
  - unfold array_read, ITree.bind, ITree.subst, ITree.trigger; cbn; reflexivity.
  - pose proof (read_attempt_time A index array cost) as H.
    rewrite (read_initialized A index array value Hread) in H; exact H.
  - eapply run_count_from_observe with (program' := continuation value);
      [reflexivity|exact Htail].
Qed.
Lemma run_count_set_bind A R index (value : A)
    (continuation : unit -> itree (ArrayE A +' TimeE) R) array cost final_cost outcome :
  index < length array ->
  (final_cost, outcome) ∈
    run_count_from (continuation tt) (set_cell index value array) (S cost) ->
  (final_cost, outcome) ∈
    run_count_from (array_set index value >>= continuation) array cost.
Proof.
  intros Hvalid Htail; eapply run_count_from_event with (event := (ArraySet index value |)).
  - unfold array_set, ITree.bind, ITree.subst, ITree.trigger; cbn; reflexivity.
  - pose proof (set_attempt_time A index value array cost) as H.
    rewrite (set_valid A index value array Hvalid) in H; exact H.
  - eapply run_count_from_observe with (program' := continuation tt);
      [reflexivity|exact Htail].
Qed.

(** Starting from the empty array, allocation costs three ticks (one operation
    plus two cells), and the two valid sets cost one tick each. The continuation
    may succeed or fail; its exact counted leaf is preserved. These five ticks
    do not include a target-function entry charge. *)
Lemma run_count_init_pair_bind {A R} (first second : A)
    (next : itree (ArrayE A +' TimeE) R) cost final_cost outcome :
  (final_cost, outcome) ∈
    run_count_from next [Some first; Some second] (cost + 5) ->
  (final_cost, outcome) ∈
    run_count_from
      (array_alloc 2 ;; array_set 0 first ;; array_set 1 second ;; next) [] cost.
Proof.
  intro Hnext; apply run_count_alloc_bind; cbn.
  apply run_count_set_bind; [cbn; lia|].
  apply run_count_set_bind; [cbn; lia|].
  cbn; replace (S (S (cost + 3))) with (cost + 5) by lia.
  exact Hnext.
Qed.

Lemma run_count_tick_bind A R
    (continuation : unit -> itree (ArrayE A +' TimeE) R) array cost final_cost outcome :
  (final_cost, outcome) ∈ run_count_from (continuation tt) array (S cost) ->
  (final_cost, outcome) ∈
    run_count_from (trigger Tick >>= continuation) array cost.
Proof.
  intro Htail; eapply run_count_from_event with (event := (| Tick)).
  - unfold ITree.bind, ITree.subst, ITree.trigger; cbn; reflexivity.
  - cbn; rewrite bind_trigger.
    eapply LeafTau; [rewrite observe_count; reflexivity|].
    apply LeafRet; rewrite observe_count; reflexivity.
  - eapply run_count_from_observe with (program' := continuation tt);
      [reflexivity|exact Htail].
Qed.

Lemma run_count_function_entry_leaf A Input R
    (program : Input -> itree (ArrayE A +' TimeE) R) input
    array cost final_cost outcome :
  (final_cost, outcome) ∈ run_count_from (program input) array (S cost) ->
  (final_cost, outcome) ∈ run_count_from (function_entry program input) array cost.
Proof.
  intro H; exact (run_count_tick_bind A R (fun _ => program input)
    array cost final_cost outcome H).
Qed.
Lemma run_count_iter_body_entry_leaf A State R
    (body : State -> itree (ArrayE A +' TimeE) (State + R)) state
    array cost final_cost outcome :
  (final_cost, outcome) ∈ run_count_from (body state) array (S cost) ->
  (final_cost, outcome) ∈ run_count_from (iter_body_entry body state) array cost.
Proof.
  intro H; exact (run_count_tick_bind A (State + R) (fun _ => body state)
    array cost final_cost outcome H).
Qed.
Lemma run_count_add_leaf A left right (array : array_state A) cost :
  (S cost, Some (array, left + right)) ∈
    run_count_from (cost_add left right) array cost.
Proof.
  eapply run_count_tick_bind with (continuation := fun _ => Ret (left + right)).
  apply run_count_from_ret; reflexivity.
Qed.
Lemma run_count_mul_leaf A left right (array : array_state A) cost :
  (S cost, Some (array, left * right)) ∈
    run_count_from (cost_mul left right) array cost.
Proof.
  eapply run_count_tick_bind with (continuation := fun _ => Ret (left * right)).
  apply run_count_from_ret; reflexivity.
Qed.
Lemma run_count_sub_leaf A left right (array : array_state A) cost :
  (S cost, Some (array, left - right)) ∈
    run_count_from (cost_sub left right) array cost.
Proof.
  eapply run_count_tick_bind with (continuation := fun _ => Ret (left - right)).
  apply run_count_from_ret; reflexivity.
Qed.
Lemma run_count_iter_step A State R
    (body : State -> itree (ArrayE A +' TimeE) (State + R)) state
    array cost array' cost' step final_cost outcome :
  (cost', Some (array', step)) ∈ run_count_from (body state) array cost ->
  (match step with
   | inl state' => (final_cost, outcome) ∈ run_count_from (ITree.iter body state') array' cost'
   | inr result => (final_cost, outcome) = (cost', Some (array', result))
   end) ->
  (final_cost, outcome) ∈ run_count_from (ITree.iter body state) array cost.
Proof.
  intros Hbody Hnext; rewrite run_count_iter_unfold.
  eapply run_count_bind_leaf; [exact Hbody|].
  destruct step as [state'|result]; cbn in *.
  - eapply run_count_from_tau; [reflexivity|exact Hnext].
  - inversion Hnext; subst; apply run_count_from_ret; reflexivity.
Qed.
Lemma run_count_cost_iter_step A State R
    (body : State -> itree (ArrayE A +' TimeE) (State + R)) state
    array cost array' cost' step final_cost outcome :
  (cost', Some (array', step)) ∈ run_count_from (body state) array (S cost) ->
  (match step with
   | inl state' => (final_cost, outcome) ∈ run_count_from (cost_iter body state') array' cost'
   | inr result => (final_cost, outcome) = (cost', Some (array', result))
   end) ->
  (final_cost, outcome) ∈ run_count_from (cost_iter body state) array cost.
Proof.
  intros Hbody Hnext; unfold cost_iter in *.
  eapply run_count_iter_step; [apply run_count_iter_body_entry_leaf; exact Hbody|exact Hnext].
Qed.
Lemma run_count_cost_iter_failure A State R
    (body : State -> itree (ArrayE A +' TimeE) (State + R)) state
    array cost final_cost :
  (final_cost, None) ∈ run_count_from (body state) array (S cost) ->
  (final_cost, None) ∈ run_count_from (cost_iter body state) array cost.
Proof.
  intro H; unfold cost_iter; rewrite run_count_iter_unfold.
  apply run_count_bind_failure, run_count_iter_body_entry_leaf; exact H.
Qed.

(** The remaining rank is proof-only: runtime state need not be a countdown.
    Both costs include the automatic iteration-entry tick, so the body
    premises start at [S cost]. *)
Lemma run_count_cost_iter_rank_invariant {A State R}
    (body : State -> itree (ArrayE A +' TimeE) (State + R))
    (invariant : nat -> State -> array_state A -> Prop)
    (step_cost exit_cost : nat) (final_array : array_state A) (result : R) :
  (forall state array cost, invariant 0 state array ->
    (cost + exit_cost, Some (final_array, inr result)) ∈
      run_count_from (body state) array (S cost)) ->
  (forall remaining state array cost, invariant (S remaining) state array ->
    exists state' array', invariant remaining state' array' /\
      (cost + step_cost, Some (array', inl state')) ∈
        run_count_from (body state) array (S cost)) ->
  forall remaining state array cost, invariant remaining state array ->
    (cost + step_cost * remaining + exit_cost, Some (final_array, result)) ∈
      run_count_from (cost_iter body state) array cost.
Proof.
  intros Hzero Hstep remaining; induction remaining as [|remaining IH];
    intros state array cost Hinv.
  - eapply run_count_cost_iter_step with
      (array' := final_array) (cost' := cost + exit_cost)
      (step := inr result).
    + exact (Hzero state array cost Hinv).
    + cbn; rewrite Nat.mul_0_r.
      replace (cost + 0 + exit_cost) with (cost + exit_cost) by lia.
      reflexivity.
  - destruct (Hstep remaining state array cost Hinv)
      as [state' [array' [Hinv' Hbody]]].
    eapply run_count_cost_iter_step with
      (array' := array') (cost' := cost + step_cost)
      (step := inl state').
    + exact Hbody.
    + cbn -[Nat.mul Nat.add].
      rewrite Nat.mul_succ_r.
      replace (cost + (step_cost * remaining + step_cost) + exit_cost)
        with ((cost + step_cost) + step_cost * remaining + exit_cost)
        by lia.
      exact (IH state' array' (cost + step_cost) Hinv').
Qed.

(** The invariant relates the remaining countdown to the current array.
    Each application fixes the final array and result. Both [step_cost] and
    [exit_cost] include the automatic iteration-entry tick: the body premises
    start at [S cost]. *)
Lemma run_count_cost_iter_nat_invariant {A R}
    (body : nat -> itree (ArrayE A +' TimeE) (nat + R))
    (invariant : nat -> array_state A -> Prop)
    (step_cost exit_cost : nat) (final_array : array_state A) (result : R) :
  (forall array cost, invariant 0 array ->
    (cost + exit_cost, Some (final_array, inr result)) ∈
      run_count_from (body 0) array (S cost)) ->
  (forall remaining array cost, invariant (S remaining) array ->
    exists array', invariant remaining array' /\
      (cost + step_cost, Some (array', inl remaining)) ∈
        run_count_from (body (S remaining)) array (S cost)) ->
  forall remaining array cost, invariant remaining array ->
    (cost + step_cost * remaining + exit_cost, Some (final_array, result)) ∈
      run_count_from (cost_iter body remaining) array cost.
Proof.
  intros Hzero Hstep remaining; induction remaining as [|remaining IH];
    intros array cost Hinv.
  - eapply run_count_cost_iter_step with
      (array' := final_array) (cost' := cost + exit_cost)
      (step := inr result).
    + exact (Hzero array cost Hinv).
    + cbn; rewrite Nat.mul_0_r.
      replace (cost + 0 + exit_cost) with (cost + exit_cost) by lia.
      reflexivity.
  - destruct (Hstep remaining array cost Hinv)
      as [array' [Hinv' Hbody]].
    eapply run_count_cost_iter_step with
      (array' := array') (cost' := cost + step_cost)
      (step := inl remaining).
    + exact Hbody.
    + cbn -[Nat.mul Nat.add].
      rewrite Nat.mul_succ_r.
      replace (cost + (step_cost * remaining + step_cost) + exit_cost)
        with ((cost + step_cost) + step_cost * remaining + exit_cost)
        by lia.
      exact (IH array' (cost + step_cost) Hinv').
Qed.

Lemma run_count_trigger_leaf A X (event : (ArrayE A +' TimeE) X)
    array cost final_cost outcome :
  (final_cost, outcome) ∈ count_from (unOptionT (h_effects X event array)) cost ->
  (final_cost, outcome) ∈ run_count_from (trigger event) array cost.
Proof.
  intro H; destruct outcome as [[array' result]|].
  - eapply run_count_from_event with (event := event).
    + reflexivity.
    + exact H.
    + apply run_count_from_ret; reflexivity.
  - eapply run_count_from_failure; [reflexivity|exact H].
Qed.
Lemma run_count_alloc_leaf A size (array : array_state A) cost :
  (cost + (size + 1), Some (array ++ repeat None size, length array)) ∈
    run_count_from (array_alloc (A := A) size) array cost.
Proof. apply run_count_trigger_leaf; apply alloc_time_exact. Qed.
Lemma run_count_read_leaf A index (array : array_state A) cost :
  (S cost, array_step (ArrayRead index) array) ∈
    run_count_from (array_read index) array cost.
Proof. apply run_count_trigger_leaf; apply read_attempt_time. Qed.
Lemma run_count_set_leaf A index (value : A) array cost :
  (S cost, array_step (ArraySet index value) array) ∈
    run_count_from (array_set index value) array cost.
Proof. apply run_count_trigger_leaf; apply set_attempt_time. Qed.
Lemma run_count_read_failure A R index
    (continuation : A -> itree (ArrayE A +' TimeE) R) array cost :
  array_step (ArrayRead index) array = None ->
  (S cost, None) ∈
    run_count_from (array_read index >>= continuation) array cost.
Proof.
  intro H; apply run_count_bind_failure.
  rewrite <- H; apply run_count_read_leaf.
Qed.
Lemma run_count_set_failure A R index (value : A)
    (continuation : unit -> itree (ArrayE A +' TimeE) R) array cost :
  length array <= index ->
  (S cost, None) ∈
    run_count_from (array_set index value >>= continuation) array cost.
Proof.
  intro H; apply run_count_bind_failure.
  rewrite <- (set_oob A index value array H); apply run_count_set_leaf.
Qed.

Local Lemma allocation_ticks_leaf R size (tail : itree TimeE R) outcome :
  outcome ∈ allocation_ticks size tail -> outcome ∈ tail.
Proof.
  induction size; cbn; intros H; apply Leaf_Vis_inv in H as [reply H]; auto.
Qed.
Lemma h_effects_monotone A X (event : (ArrayE A +' TimeE) X) array array' result :
  Some (array', result) ∈ unOptionT (h_effects X event array) ->
  length array <= length array'.
Proof.
  destruct event as [event|event]; cbn.
  - destruct event as [size|index|index value].
    + intro H; apply allocation_ticks_leaf, Leaf_Ret_inv in H.
      eapply (step_success_monotone A _ (ArrayAlloc size)); symmetry; exact H.
    + intro H; apply Leaf_Vis_inv in H as [reply H]. apply Leaf_Ret_inv in H.
      eapply (step_success_monotone A _ (ArrayRead index)); symmetry; exact H.
    + intro H; apply Leaf_Vis_inv in H as [reply H]. apply Leaf_Ret_inv in H.
      eapply (step_success_monotone A _ (ArraySet index value)); symmetry; exact H.
  - destruct event; rewrite bind_trigger. intro H.
    apply Leaf_Vis_inv in H as [reply H]; destruct reply.
    apply Leaf_Ret_inv in H; inversion H; subst; lia.
Qed.
Lemma array_to_time_from_monotone A R (program : itree (ArrayE A +' TimeE) R)
    array array' result :
  Some (array', result) ∈ array_to_time_from program array ->
  length array <= length array'.
Proof.
  intro Hleaf.
  assert (Hinv : array_to_time_from program array ⤳
    (fun outcome => match outcome with
      | Some (array', _) => length array <= length array' | None => True end)).
  { apply state_option_invariant.
    - intros X event a a' value Hlen Hstep.
      pose proof (h_effects_monotone A X event a a' value Hstep); lia.
    - lia. }
  destruct (Leaf_eutt_l _ _ _ Hinv Hleaf) as [outcome [_ Hpost]]. exact Hpost.
Qed.
Lemma run_count_from_monotone A R (program : itree (ArrayE A +' TimeE) R)
    array initial_cost final_cost array' result :
  (final_cost, Some (array', result)) ∈ run_count_from program array initial_cost ->
  length array <= length array'.
Proof.
  intro H. apply array_to_time_from_monotone with (program := program) (result := result).
  pose proof (Leaf_interp_state_subtree_inv h_count
    (array_to_time_from program array) (array_to_time_from program array) initial_cost) as Hpost.
  assert (Hsub : subtree (array_to_time_from program array) (array_to_time_from program array))
    by (constructor; reflexivity).
  specialize (Hpost Hsub).
  destruct (Leaf_eutt_l _ _ _ Hpost H) as [outcome [_ Hraw]]. exact Hraw.
Qed.

Lemma subtree_finite {E R} (tail program : itree E R) :
  subtree tail program -> all_finite program -> all_finite tail.
Proof.
  intro H; induction H; intro Hfin.
  - rewrite H; exact Hfin.
  - apply all_finite_Tau_inv, IHsubtree, Hfin.
  - rewrite H; eapply all_finite_Vis_inv, IHsubtree; exact Hfin.
Qed.

(** A successful final-state bound controls every canonical residual that is
    an existing library subtree. Finiteness rules out vacuous divergence. *)
Theorem final_bound_subtree A R (program : itree (ArrayE A +' TimeE) R)
    initial_array initial_cost bound :
  all_finite (run_count_from program initial_array initial_cost) ->
  (forall cost outcome, (cost, outcome) ∈ run_count_from program initial_array initial_cost ->
    match outcome with Some (array, _) => length array <= bound | None => False end) ->
  forall tail array cost,
    subtree (run_count_from tail array cost) (run_count_from program initial_array initial_cost) ->
    length array <= bound.
Proof.
  intros Hfin Hpost tail array cost Hsub.
  pose proof (subtree_finite _ _ Hsub Hfin) as Hsuffix.
  apply finite_leaf_non_interactive in Hsuffix.
  destruct Hsuffix as [[final_cost outcome] Hleaf].
  specialize (Hpost _ _ (subtree_image _ _ _ Hsub Hleaf)).
  destruct outcome as [[final_array result]|]; [|contradiction].
  pose proof (run_count_from_monotone A R tail array cost final_cost final_array result Hleaf).
  lia.
Qed.

(** A successful exact leaf of the closed counted tree supplies both termination
    and its unique outcome. Only the final array-length bound is needed in
    addition; the initial array and accumulated cost are arbitrary. *)
Theorem final_bound_subtree_leaf A R (program : itree (ArrayE A +' TimeE) R)
    initial_array initial_cost bound final_cost final_array result :
  (final_cost, Some (final_array, result)) ∈
    run_count_from program initial_array initial_cost ->
  length final_array <= bound ->
  forall tail array cost,
    subtree (run_count_from tail array cost) (run_count_from program initial_array initial_cost) ->
    length array <= bound.
Proof.
  intros Hleaf Hbound; apply final_bound_subtree.
  - eapply closed_leaf_finite; exact Hleaf.
  - intros cost outcome Hother.
    rewrite (closed_leaf_eutt _ _ Hleaf) in Hother.
    apply Leaf_Ret_inv in Hother; inversion Hother; subst; exact Hbound.
Qed.

Lemma subtree_trans {E R} (tail middle program : itree E R) :
  subtree tail middle -> subtree middle program -> subtree tail program.
Proof.
  intros Htail Hmiddle; induction Htail.
  - rewrite H; exact Hmiddle.
  - apply SubtreeTau, IHHtail, Hmiddle.
  - eapply SubtreeVis; [exact H|apply IHHtail, Hmiddle].
Qed.
Lemma subtree_bind_leaf {E X R} (program : itree E X) (continuation : X -> itree E R) result :
  result ∈ program -> subtree (continuation result) (program >>= continuation).
Proof.
  intro H; induction H.
  - rewrite (itree_eta t), H, bind_ret_l. constructor; reflexivity.
  - rewrite (itree_eta t), H, bind_tau.
    eapply subtree_trans; [exact IHLeaf|].
    apply SubtreeTau; constructor; reflexivity.
  - rewrite (itree_eta t), H, bind_vis.
    eapply subtree_trans; [exact IHLeaf|].
    eapply SubtreeVis with (x := x) (k := fun a => k a >>= continuation);
      [reflexivity|constructor; reflexivity].
Qed.
Lemma counted_tau_subtree A R (program tail : itree (ArrayE A +' TimeE) R) array cost :
  observe program = TauF tail ->
  subtree (run_count_from tail array cost) (run_count_from program array cost).
Proof.
  intro Hobs. unfold run_count_from, array_to_time_from.
  rewrite (unfold_state_option h_effects program array), Hobs; cbn.
  unfold count_from; rewrite interp_state_tau.
  apply SubtreeTau; constructor; reflexivity.
Qed.
Lemma counted_handler_subtree A R X (event : (ArrayE A +' TimeE) X)
    (program : itree (ArrayE A +' TimeE) R) (continuation : X -> itree (ArrayE A +' TimeE) R)
    array cost array' cost' result :
  observe program = VisF event continuation ->
  (cost', Some (array', result)) ∈ count_from (unOptionT (h_effects X event array)) cost ->
  subtree (run_count_from (continuation result) array' cost') (run_count_from program array cost).
Proof.
  intros Hobs Hleaf. unfold run_count_from, array_to_time_from.
  rewrite (unfold_state_option h_effects program array), Hobs; cbn.
  unfold count_from in *; rewrite interp_state_bind.
  eapply subtree_trans; [|eapply subtree_bind_leaf; exact Hleaf].
  cbn; rewrite interp_state_tau.
  apply SubtreeTau; constructor; reflexivity.
Qed.

(** Prefix coverage includes ticks inside a handler, not just completed raw
    events. Both subtree premises below are ordinary ITree subtrees. *)
Lemma subtree_bind {E X R} (tail program : itree E X) (continuation : X -> itree E R) :
  subtree tail program -> subtree (tail >>= continuation) (program >>= continuation).
Proof.
  intro H; induction H.
  - constructor; rewrite H; reflexivity.
  - apply SubtreeTau; rewrite <- bind_tau; exact IHsubtree.
  - eapply SubtreeVis with (k := fun value => k value >>= continuation) (x := x).
    + rewrite H; reflexivity.
    + rewrite <- bind_vis; exact IHsubtree.
Qed.
Lemma counted_time_tick_subtree R (program : itree TimeE R) continuation cost :
  observe program = VisF Tick continuation ->
  subtree (count_from (continuation tt) (S cost)) (count_from program cost).
Proof.
  intro H; rewrite (itree_eta (count_from program cost)), observe_count, H; cbn.
  apply SubtreeTau; constructor; reflexivity.
Qed.
Lemma time_tick_subtree R (program : itree TimeE R) continuation :
  observe program = VisF Tick continuation -> subtree (continuation tt) program.
Proof.
  intro H; rewrite (itree_eta program), H; cbn.
  eapply SubtreeVis with (x := tt); [reflexivity|constructor; reflexivity].
Qed.
Lemma counted_handler_prefix_subtree A R X (event : (ArrayE A +' TimeE) X)
    (program : itree (ArrayE A +' TimeE) R) (continuation : X -> itree (ArrayE A +' TimeE) R)
    array cost (pending : itree TimeE (option (array_state A * X))) cost' :
  observe program = VisF event continuation ->
  subtree (count_from pending cost') (count_from (unOptionT (h_effects X event array)) cost) ->
  subtree
    (count_from (outcome <- pending ;; match outcome with
       | None => Ret None
       | Some (array', result) => Tau (array_to_time_from (continuation result) array')
       end) cost')
    (run_count_from program array cost).
Proof.
  intros Hobs Hprefix; unfold run_count_from, array_to_time_from.
  rewrite (unfold_state_option h_effects program array), Hobs; cbn -[interp_state unOptionT].
  unfold count_from in *; rewrite !interp_state_bind.
  apply subtree_bind; exact Hprefix.
Qed.

(** [array] is unchanged while a handler emits its ticks. This theorem
    bounds that very state at every pending handler subtree, including
    allocation's per-cell ticks and the tick of a failing attempt. *)
Theorem final_bound_handler_subtree A R
    (program : itree (ArrayE A +' TimeE) R) initial_array initial_cost bound :
  all_finite (run_count_from program initial_array initial_cost) ->
  (forall cost outcome, (cost, outcome) ∈ run_count_from program initial_array initial_cost ->
    match outcome with Some (array, _) => length array <= bound | None => False end) ->
  forall X (event : (ArrayE A +' TimeE) X)
    (continuation : X -> itree (ArrayE A +' TimeE) R) array
    (pending : itree TimeE (option (array_state A * X))) cost,
  subtree pending (unOptionT (h_effects X event array)) ->
  subtree
    (count_from (outcome <- pending ;; match outcome with
       | None => Ret None
       | Some (array', result) => Tau (array_to_time_from (continuation result) array')
       end) cost)
    (run_count_from program initial_array initial_cost) ->
  length array <= bound.
Proof.
  intros Hfin Hpost X event continuation array pending cost Hpending Hsub.
  pose proof (subtree_finite _ _ Hsub Hfin) as Hsuffix.
  apply finite_leaf_non_interactive in Hsuffix.
  destruct Hsuffix as [[final_cost outcome] Hleaf].
  specialize (Hpost _ _ (subtree_image _ _ _ Hsub Hleaf)).
  destruct outcome as [[final_array result]|]; [|contradiction].
  set (tail := outcome <- pending ;; match outcome with
       | None => Ret None
       | Some (array', value) => Tau (array_to_time_from (continuation value) array')
       end).
  assert (Hrefl : subtree tail tail) by (constructor; reflexivity).
  pose proof (Leaf_interp_state_subtree_inv h_count tail tail cost Hrefl) as Hrawpost.
  destruct (Leaf_eutt_l _ _ _ Hrawpost Hleaf) as [outcome [_ Hraw]].
  unfold tail in Hraw.
  apply Leaf_bind_inv in Hraw as [middle [Hmiddle Htail]].
  destruct middle as [[array' value]|].
  - apply Leaf_Tau_inv in Htail.
    pose proof (array_to_time_from_monotone A R (continuation value) array' final_array result Htail).
    pose proof (h_effects_monotone A X event array array' value
      (subtree_image _ _ _ Hpending Hmiddle)). lia.
  - apply Leaf_Ret_inv in Htail; discriminate.
Qed.

(** The same successful-leaf premises also bound the unchanged array during
    pending handler ticks. Both subtree premises retain the generic rule's
    coverage, including allocation's per-cell ticks; no empty-state or zero-cost
    assumption is imposed. *)
Theorem final_bound_handler_subtree_leaf A R
    (program : itree (ArrayE A +' TimeE) R)
    initial_array initial_cost bound final_cost final_array result :
  (final_cost, Some (final_array, result)) ∈
    run_count_from program initial_array initial_cost ->
  length final_array <= bound ->
  forall X (event : (ArrayE A +' TimeE) X)
    (continuation : X -> itree (ArrayE A +' TimeE) R) array
    (pending : itree TimeE (option (array_state A * X))) cost,
  subtree pending (unOptionT (h_effects X event array)) ->
  subtree
    (count_from (outcome <- pending ;; match outcome with
       | None => Ret None
       | Some (array', result) => Tau (array_to_time_from (continuation result) array')
       end) cost)
    (run_count_from program initial_array initial_cost) ->
  length array <= bound.
Proof.
  intros Hleaf Hbound; apply final_bound_handler_subtree.
  - eapply closed_leaf_finite; exact Hleaf.
  - intros cost outcome Hother.
    rewrite (closed_leaf_eutt _ _ Hleaf) in Hother.
    apply Leaf_Ret_inv in Hother; inversion Hother; subst; exact Hbound.
Qed.
