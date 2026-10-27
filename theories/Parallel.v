From Stdlib Require Import List Arith Lia Morphisms.
From Paco Require Import paco.
From ITree.Events Require Import StateFacts.
From RefineToITree Require Export Array.
Import ListNotations ITreeNotations LeafNotations HasPostNotations SumNotations.
Local Open Scope itree_scope.
Local Open Scope sum_scope.

(** The older unary translate Proper instance in ITree uses dependent
    inversion. Prefer the closed, generalized instance throughout this file. *)
#[local] Remove Hints eq_itree_translate' : typeclass_instances.
#[local] Instance translate_proper_closed {E F R} (handler : E ~> F) :
  Proper (eq_itree eq ==> eq_itree eq) (@translate E F handler R).
Proof.
  intros p q H; eapply eq_itree_translate; [|exact H].
  intros X event; reflexivity.
Qed.

(** Shallow fork/join: children are sequential and array-free. Coordination
    prices belong to the interpreter, so serialization removes no program tick.
    Stable core API: [Prices], [ParallelE], [fork], [lift_serial],
    [run_parent_from], [run_parallel_from], [run_parallel], [serialization]. *)
Record Prices := { fork_cost : nat; join_cost : nat }.
Definition positive_prices (prices : Prices) : Prop :=
  0 < fork_cost prices /\ 0 < join_cost prices.

Variant ForkEvent : Type -> Type :=
| Fork {A B} : itree TimeE A -> itree TimeE B -> ForkEvent (A * B).
Definition ParallelE (A : Type) := ArrayE A +' (ForkEvent +' TimeE).
Definition fork {Element A B} (left : itree TimeE A) (right : itree TimeE B)
    : itree (ParallelE Element) (A * B) := trigger (Fork left right).

Definition serial_injection {A} : (ArrayE A +' TimeE) ~> ParallelE A :=
  fun X event => match event with
  | (ae |) => (ae |)
  | (| te) => (| (| te))
  end.
Definition lift_serial {A R} (program : itree (ArrayE A +' TimeE) R)
    : itree (ParallelE A) R := translate serial_injection program.

(** Interpreter primitive, not a target-program loop. *)
Fixpoint unit_ticks (n : nat) : itree TimeE unit :=
  match n with 0 => Ret tt | S k => trigger Tick ;; unit_ticks k end.

Definition h_parent {A} X (event : ParallelE A X) (array : array_state A)
    : optionT (itree (ForkEvent +' TimeE)) (array_state A * X) :=
  match event with
  | (ae |) => mkOptionT (translate (@inr1 ForkEvent TimeE)
      (unOptionT (h_array_time X ae array)))
  | (| other) => mkOptionT (value <- trigger other ;; Ret (Some (array,value)))
  end.
Definition run_parent_from {A R} (program : itree (ParallelE A) R)
    (array : array_state A) := unOptionT (interp_state h_parent program array).
Definition run_parent {A R} (program : itree (ParallelE A) R) :=
  run_parent_from program [].

Definition parallel_fork prices X (event : ForkEvent X) (ws : nat * nat)
    : itree void1 ((nat * nat) * X) :=
  match event with
  | Fork l r =>
      '(fc, _) <- count (unit_ticks (fork_cost prices)) ;;
      '(wl, x) <- count l ;;
      '(wr, y) <- count r ;;
      '(jc, _) <- count (unit_ticks (join_cost prices)) ;;
      Ret ((fst ws + fc + wl + wr + jc,
            snd ws + fc + Nat.max wl wr + jc), (x,y))
  end.
Definition h_parallel prices X (event : (ForkEvent +' TimeE) X) (ws : nat * nat)
    : itree void1 ((nat * nat) * X) :=
  match event with
  | (fe |) => parallel_fork prices X fe ws
  | (| te) => match te with Tick => Ret ((S (fst ws), S (snd ws)), tt) end
  end.
Definition run_parallel_from prices {A R} (program : itree (ParallelE A) R)
    (array : array_state A) (ws : nat * nat) :=
  interp_state (h_parallel prices) (run_parent_from program array) ws.
Definition run_parallel prices {A R} (program : itree (ParallelE A) R) :=
  run_parallel_from prices program [] (0,0).

Definition serial_fork X (event : ForkEvent X) : itree TimeE X :=
  match event with Fork l r => x <- l ;; y <- r ;; Ret (x,y) end.
Definition h_serialize {A} X (event : ParallelE A X)
    : itree (ArrayE A +' TimeE) X :=
  match event with
  | (ae |) => trigger ae
  | (| (fe |)) => translate (@inr1 (ArrayE A) TimeE) (serial_fork X fe)
  | (| (| te)) => trigger te
  end.
Definition serialization {A R} (program : itree (ParallelE A) R) :=
  interp h_serialize program.

Lemma unit_ticks_exact n cost :
  (cost + n, tt) ∈ count_from (unit_ticks n) cost.
Proof.
  revert cost; induction n as [|n IH]; intro cost.
  - replace (cost + 0) with cost by lia.
    apply LeafRet; rewrite observe_count; reflexivity.
  - eapply count_bind_leaf.
    + eapply LeafTau; [rewrite observe_count; reflexivity |].
      apply LeafRet; rewrite observe_count; reflexivity.
    + replace (cost + S n) with (S cost + n) by lia; apply IH.
Qed.

#[global] Instance eq_itree_run_parent_from A R :
  Proper (eq_itree eq ==> eq ==> eq_itree eq) (@run_parent_from A R).
Proof. exact (eq_itree_state_option h_parent). Qed.

Lemma h_parent_serial_injection A X (event : (ArrayE A +' TimeE) X) array :
  unOptionT (h_parent X (serial_injection X event) array) ≅
  translate (@inr1 ForkEvent TimeE) (unOptionT (h_effects X event array)).
Proof.
  destruct event as [ae|te]; [reflexivity|].
  destruct te; cbn; rewrite !bind_trigger, translate_vis.
  apply eqit_Vis; intro u; rewrite translate_ret; reflexivity.
Qed.

Lemma run_parent_lift_serial A R (program : itree (ArrayE A +' TimeE) R) array :
  run_parent_from (lift_serial program) array ≅
  translate (@inr1 ForkEvent TimeE) (array_to_time_from program array).
Proof.
  revert program array; ginit; gcofix CIH; intros program array.
  unfold lift_serial.
  rewrite (unfold_translate serial_injection program).
  unfold array_to_time_from.
  rewrite (unfold_state_option h_effects program array).
  destruct (observe program) as [value|tail|X event next]; cbn -[interp_state unOptionT].
  - unfold run_parent_from; rewrite unfold_state_option; cbn; rewrite translate_ret; gstep; constructor; reflexivity.
  - unfold run_parent_from at 1; rewrite unfold_state_option; cbn; rewrite translate_tau.
    gstep; constructor; gbase; apply CIH.
  - unfold run_parent_from at 1; rewrite unfold_state_option; cbn -[interp_state unOptionT].
    rewrite translate_bind.
    guclo eqit_clo_bind; econstructor.
    + apply h_parent_serial_injection.
    + intros [[a x]|] ? []; cbn -[interp_state unOptionT].
      * rewrite translate_tau; gstep; constructor; gbase; apply CIH.
      * rewrite translate_ret; gstep; constructor; reflexivity.
Qed.

Lemma parallel_branch_accounting prices A B (left : itree TimeE A)
    (right : itree TimeE B) wl wr x y w s :
  (wl,x) ∈ count left -> (wr,y) ∈ count right ->
  ((w + fork_cost prices + wl + wr + join_cost prices,
    s + fork_cost prices + Nat.max wl wr + join_cost prices),(x,y)) ∈
    parallel_fork prices _ (Fork left right) (w,s).
Proof.
  intros Hl Hr; unfold parallel_fork.
  eapply Leaf_bind; [apply (unit_ticks_exact (fork_cost prices) 0) |].
  cbn; eapply Leaf_bind; [exact Hl |].
  eapply Leaf_bind; [exact Hr |].
  eapply Leaf_bind; [apply (unit_ticks_exact (join_cost prices) 0) |].
  apply LeafRet; reflexivity.
Qed.
Lemma serial_branch_accounting A B (left : itree TimeE A) (right : itree TimeE B)
    wl wr x y :
  (wl,x) ∈ count left -> (wr,y) ∈ count right ->
  (wl+wr,(x,y)) ∈ count (serial_fork _ (Fork left right)).
Proof.
  intros Hl Hr; unfold serial_fork, count.
  eapply count_bind_leaf; [exact Hl |].
  eapply count_bind_leaf; [apply count_shift_leaf; exact Hr |].
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.
Lemma branch_outcome_agreement prices A B (left : itree TimeE A)
    (right : itree TimeE B) wl wr x y :
  (wl,x) ∈ count left -> (wr,y) ∈ count right ->
  eutt (fun parallel serial => snd parallel = snd serial)
    (parallel_fork prices _ (Fork left right) (0,0))
    (count (serial_fork _ (Fork left right))).
Proof.
  intros Hl Hr.
  rewrite (closed_leaf_eutt _ _
    (parallel_branch_accounting prices A B left right wl wr x y 0 0 Hl Hr)),
    (closed_leaf_eutt _ _ (serial_branch_accounting A B left right wl wr x y Hl Hr)).
  apply eutt_Ret; reflexivity.
Qed.

Lemma run_parallel_bind prices A X R (program : itree (ParallelE A) X)
    (next : X -> itree (ParallelE A) R) array ws :
  run_parallel_from prices (program >>= next) array ws ≅
  (counted <- run_parallel_from prices program array ws ;;
    match snd counted with
    | None => Ret (fst counted, None)
    | Some (array', value) => run_parallel_from prices (next value) array' (fst counted)
    end).
Proof.
  unfold run_parallel_from, run_parent_from.
  rewrite state_option_bind, interp_state_bind.
  apply eqit_bind; [reflexivity|].
  intros [ws' [[array' value]|]]; cbn; [reflexivity|].
  rewrite interp_state_ret; reflexivity.
Qed.
Lemma run_parallel_bind_leaf prices A X R (program : itree (ParallelE A) X)
    (next : X -> itree (ParallelE A) R) array ws array' ws' value final outcome :
  (ws', Some (array',value)) ∈ run_parallel_from prices program array ws ->
  (final,outcome) ∈ run_parallel_from prices (next value) array' ws' ->
  (final,outcome) ∈ run_parallel_from prices (program >>= next) array ws.
Proof.
  intros Hp Hn; rewrite run_parallel_bind; eapply Leaf_bind; [exact Hp|exact Hn].
Qed.
Lemma run_parallel_bind_failure prices A X R (program : itree (ParallelE A) X)
    (next : X -> itree (ParallelE A) R) array ws final :
  (final,None) ∈ run_parallel_from prices program array ws ->
  (final,None) ∈ run_parallel_from prices (program >>= next) array ws.
Proof.
  intro H; rewrite run_parallel_bind; eapply Leaf_bind; [exact H|apply Leaf_Ret].
Qed.
Lemma run_parallel_ret prices A R (value : R) (array : array_state A) ws :
  (ws, Some (array,value)) ∈ run_parallel_from prices (Ret value) array ws.
Proof.
  unfold run_parallel_from, run_parent_from.
  rewrite unfold_state_option; cbn; rewrite interp_state_ret; apply Leaf_Ret.
Qed.

#[global] Instance eq_itree_run_parallel_from prices A R :
  Proper (eq_itree eq ==> eq ==> eq ==> eq_itree eq)
    (@run_parallel_from prices A R).
Proof.
  intros p q H a b <- ws ws' <-.
  unfold run_parallel_from, run_parent_from.
  apply eq_itree_interp_state; [|reflexivity].
  apply eq_itree_state_option; [exact H|reflexivity].
Qed.

Lemma parallel_time_count prices R (program : itree TimeE R) cost w s :
  interp_state (h_parallel prices) (translate (@inr1 ForkEvent TimeE) program)
    (w + cost,s + cost) ≅
  ITree.map (fun '(c,x) => ((w+c,s+c),x)) (count_from program cost).
Proof.
  revert program cost; ginit; gcofix CIH; intros program cost.
  rewrite unfold_translate, unfold_interp_state.
  unfold ITree.map; rewrite unfold_bind, observe_count.
  destruct (observe program) as [value|tail|X event next]; cbn.
  - gstep; constructor; reflexivity.
  - gstep; constructor; gbase; apply CIH.
  - destruct event; cbn; rewrite bind_ret_l.
    replace (S (w + cost)) with (w + S cost) by lia.
    replace (S (s + cost)) with (s + S cost) by lia.
    gstep; constructor; gbase; apply CIH.
Qed.

(** Lift any existing canonical serial leaf, including automatic array charges
    and failures, without reproving the serial algorithm's loop invariant. *)
Lemma run_parallel_lift_serial_leaf prices A R
    (program : itree (ArrayE A +' TimeE) R) array cost outcome w s :
  (cost,outcome) ∈ run_count_from program array 0 ->
  ((w+cost,s+cost),outcome) ∈
    run_parallel_from prices (lift_serial program) array (w,s).
Proof.
  intro H; unfold run_parallel_from; rewrite run_parent_lift_serial.
  replace (w,s) with (w+0,s+0) by (f_equal; lia).
  rewrite parallel_time_count.
  unfold ITree.map; eapply Leaf_bind; [exact H|apply Leaf_Ret].
Qed.

Lemma run_parallel_from_event prices A R X (event : ParallelE A X)
    (program : itree (ParallelE A) R) (next : X -> itree (ParallelE A) R)
    array ws array' ws' value final outcome :
  observe program = VisF event next ->
  (ws',Some (array',value)) ∈
    interp_state (h_parallel prices) (unOptionT (h_parent X event array)) ws ->
  (final,outcome) ∈ run_parallel_from prices (next value) array' ws' ->
  (final,outcome) ∈ run_parallel_from prices program array ws.
Proof.
  intros Hobs Hhandler Htail; unfold run_parallel_from, run_parent_from in *.
  rewrite (unfold_state_option h_parent program array), Hobs; cbn.
  rewrite interp_state_bind; eapply Leaf_bind; [exact Hhandler|].
  cbn; rewrite interp_state_tau; apply Leaf_Tau; exact Htail.
Qed.

Lemma run_parallel_from_observe prices A R (program program' : itree (ParallelE A) R)
    array ws final outcome :
  observe program = observe program' ->
  (final,outcome) ∈ run_parallel_from prices program' array ws ->
  (final,outcome) ∈ run_parallel_from prices program array ws.
Proof.
  intros Hobs Hleaf; unfold run_parallel_from, run_parent_from in *.
  rewrite (unfold_state_option h_parent program array),
    (unfold_state_option h_parent program' array), Hobs in *; exact Hleaf.
Qed.

Lemma run_parallel_fork_bind prices Element A B R
    (left : itree TimeE A) (right : itree TimeE B)
    (next : A * B -> itree (ParallelE Element) R)
    wl wr x y array w s final outcome :
  (wl,x) ∈ count left -> (wr,y) ∈ count right ->
  (final,outcome) ∈ run_parallel_from prices (next (x,y)) array
    (w + fork_cost prices + wl + wr + join_cost prices,
     s + fork_cost prices + Nat.max wl wr + join_cost prices) ->
  (final,outcome) ∈ run_parallel_from prices (fork left right >>= next) array (w,s).
Proof.
  intros Hl Hr Hnext.
  eapply run_parallel_from_event with (event := (| (Fork left right |))).
  - unfold fork, ITree.bind, ITree.subst, ITree.trigger; cbn; reflexivity.
  - cbn; rewrite bind_trigger, interp_state_vis.
    eapply Leaf_bind; [apply parallel_branch_accounting; eassumption|].
    cbn; apply Leaf_Tau; rewrite interp_state_ret; apply Leaf_Ret.
  - eapply run_parallel_from_observe; [|exact Hnext]; reflexivity.
Qed.

Lemma run_parallel_tick_bind prices A R
    (next : unit -> itree (ParallelE A) R) array w s final outcome :
  (final,outcome) ∈ run_parallel_from prices (next tt) array (S w,S s) ->
  (final,outcome) ∈ run_parallel_from prices (trigger Tick >>= next) array (w,s).
Proof.
  intro Hnext; eapply run_parallel_from_event with (event := (| (| Tick))).
  - unfold ITree.bind, ITree.subst, ITree.trigger; cbn; reflexivity.
  - cbn; rewrite bind_trigger, interp_state_vis; cbn; rewrite bind_ret_l.
    apply Leaf_Tau; rewrite interp_state_ret; apply Leaf_Ret.
  - eapply run_parallel_from_observe; [|exact Hnext]; reflexivity.
Qed.
Lemma run_parallel_function_entry_leaf prices A Input R
    (program : Input -> itree (ParallelE A) R) input array w s final outcome :
  (final,outcome) ∈ run_parallel_from prices (program input) array (S w,S s) ->
  (final,outcome) ∈ run_parallel_from prices (function_entry program input) array (w,s).
Proof.
  intro H; unfold function_entry; eapply run_parallel_tick_bind; exact H.
Qed.
Lemma run_parallel_add_leaf prices A left right (array : array_state A) w s :
  ((S w,S s),Some (array,left+right)) ∈
    run_parallel_from prices (cost_add left right) array (w,s).
Proof. apply run_parallel_tick_bind; apply run_parallel_ret. Qed.
Lemma run_parallel_mul_leaf prices A left right (array : array_state A) w s :
  ((S w,S s),Some (array,left*right)) ∈
    run_parallel_from prices (cost_mul left right) array (w,s).
Proof. apply run_parallel_tick_bind; apply run_parallel_ret. Qed.
Lemma run_parallel_sub_leaf prices A left right (array : array_state A) w s :
  ((S w,S s),Some (array,left-right)) ∈
    run_parallel_from prices (cost_sub left right) array (w,s).
Proof. apply run_parallel_tick_bind; apply run_parallel_ret. Qed.

Lemma lift_serial_trigger A X (event : (ArrayE A +' TimeE) X) :
  lift_serial (trigger event) ≅ trigger (serial_injection X event).
Proof.
  unfold lift_serial, ITree.trigger; rewrite translate_vis.
  apply eqit_Vis; intro x; apply translate_ret.
Qed.
Lemma run_parallel_array_leaf prices A X (event : ArrayE A X)
    array cost outcome w s :
  (cost,outcome) ∈ run_count_from (trigger event) array 0 ->
  ((w+cost,s+cost),outcome) ∈ run_parallel_from prices (trigger event) array (w,s).
Proof.
  intro H; pose proof (run_parallel_lift_serial_leaf prices A X
    (trigger event) array cost outcome w s H) as Hp.
  change (((w+cost,s+cost),outcome) ∈ run_parallel_from prices
    (lift_serial (trigger (event |))) array (w,s)) in Hp.
  rewrite lift_serial_trigger in Hp; exact Hp.
Qed.
Lemma run_parallel_alloc_leaf prices A size (array : array_state A) w s :
  ((w+(size+1),s+(size+1)),Some (array ++ repeat None size,length array)) ∈
    run_parallel_from prices (array_alloc size) array (w,s).
Proof. apply run_parallel_array_leaf; exact (run_count_alloc_leaf A size array 0). Qed.
Lemma run_parallel_read_leaf prices A index (array : array_state A) w s :
  ((S w,S s),array_step (ArrayRead index) array) ∈
    run_parallel_from prices (array_read index) array (w,s).
Proof.
  replace (S w,S s) with (w+1,s+1) by (f_equal; lia).
  apply run_parallel_array_leaf; apply run_count_read_leaf.
Qed.
Lemma run_parallel_set_leaf prices A index (value : A) array w s :
  ((S w,S s),array_step (ArraySet index value) array) ∈
    run_parallel_from prices (array_set index value) array (w,s).
Proof.
  replace (S w,S s) with (w+1,s+1) by (f_equal; lia).
  apply run_parallel_array_leaf; apply run_count_set_leaf.
Qed.
Lemma run_parallel_alloc_bind prices A R size
    (next : nat -> itree (ParallelE A) R) array w s final outcome :
  (final,outcome) ∈ run_parallel_from prices (next (length array))
    (array ++ repeat None size) (w+(size+1),s+(size+1)) ->
  (final,outcome) ∈ run_parallel_from prices (array_alloc size >>= next) array (w,s).
Proof.
  intro H; eapply run_parallel_bind_leaf; [apply run_parallel_alloc_leaf|exact H].
Qed.
Lemma run_parallel_read_bind prices A R index (value : A)
    (next : A -> itree (ParallelE A) R) array w s final outcome :
  nth_error array index = Some (Some value) ->
  (final,outcome) ∈ run_parallel_from prices (next value) array (S w,S s) ->
  (final,outcome) ∈ run_parallel_from prices (array_read index >>= next) array (w,s).
Proof.
  intros Hr H; eapply run_parallel_bind_leaf; [|exact H].
  rewrite <- (read_initialized A index array value Hr); apply run_parallel_read_leaf.
Qed.
Lemma run_parallel_set_bind prices A R index (value : A)
    (next : unit -> itree (ParallelE A) R) array w s final outcome :
  index < length array ->
  (final,outcome) ∈ run_parallel_from prices (next tt) (set_cell index value array) (S w,S s) ->
  (final,outcome) ∈ run_parallel_from prices (array_set index value >>= next) array (w,s).
Proof.
  intros Hv H; eapply run_parallel_bind_leaf; [|exact H].
  rewrite <- (set_valid A index value array Hv); apply run_parallel_set_leaf.
Qed.

Lemma serialization_bind A X R (program : itree (ParallelE A) X)
    (next : X -> itree (ParallelE A) R) :
  serialization (program >>= next) ≅
    (value <- serialization program ;; serialization (next value)).
Proof. apply interp_bind. Qed.
Lemma serialization_ret A R (value : R) :
  serialization (Ret value : itree (ParallelE A) R) ≅ Ret value.
Proof. apply interp_ret. Qed.
Lemma serialization_lift_serial A R (program : itree (ArrayE A +' TimeE) R) :
  serialization (lift_serial program) ≈ program.
Proof.
  unfold serialization, lift_serial; rewrite interp_translate.
  transitivity (interp (fun X (event : (ArrayE A +' TimeE) X) =>
    (trigger event : itree (ArrayE A +' TimeE) X)) program).
  - apply eutt_interp; [|reflexivity]. intros X [ae|te]; reflexivity.
  - apply interp_trigger_h.
Qed.

(** Proof-only fixed-pool schedules. Worker zero executes the parent and then
    the left child inline. Worker one executes the right child. A child round
    retains exactly one waiting parent continuation; the two children cannot
    fork. Dispatch is eager (zero queued tasks), so it also satisfies a
    one-queued-child bound. Coordination executes on worker zero, not on a
    fictitious third worker. Tau and dispatch transitions consume no ticks.
    These lists are certificates, not allocations in the target program. *)
Inductive pool_round : Type :=
| ParentRound
| ChildrenRound (left_active right_active : bool).
Definition occupied_slots (round : pool_round) : nat :=
  match round with
  | ParentRound => 1
  | ChildrenRound l r => (if l then 1 else 0) + (if r then 1 else 0)
  end.
Definition saved_continuations (round : pool_round) : nat :=
  match round with ParentRound => 0 | ChildrenRound _ _ => 1 end.
Definition queued_children (_ : pool_round) : nat := 0.
Definition open_fork_frames := saved_continuations.

(** Payload-free bookkeeping for the concrete two-lane schedule. A lane reuses
    one task record: running code and a completed result are alternative states
    of that record, not fresh records allocated on every round. During a fork,
    a finished child retains its result until join even when its lane is idle.
    ParentRound includes coordination and resumed parent execution; lane one
    has released its child record by then. Dispatch/join transitions need at
    most the same two records, including for zero-tick children.

    This counts records, NOT the sizes of closures, scalar values, or results
    stored in them. Those payload bounds remain source-review obligations.
    The waiting parent continuation and join bookkeeping remain shared. *)
Inductive task_record_state : Type := RunningTask | RetainedResult.
Definition lane_task_records (round : pool_round) (lane : nat)
    : list task_record_state :=
  match round, lane with
  | ParentRound, 0 => [RunningTask]
  | ChildrenRound l _, 0 => [if l then RunningTask else RetainedResult]
  | ChildrenRound _ r, 1 => [if r then RunningTask else RetainedResult]
  | _, _ => []
  end.
Definition worker_bookkeeping (round : pool_round) (lane : nat) : nat :=
  length (lane_task_records round lane).

Lemma worker_bookkeeping_bound round lane : worker_bookkeeping round lane <= 1.
Proof. destruct round; destruct lane as [|[|lane]]; cbn; lia. Qed.

(** Storage is not occupancy: a completed child still owns its result record. *)
Lemma completed_child_retains_record :
  occupied_slots (ChildrenRound false true) = 1 /\
  lane_task_records (ChildrenRound false true) 0 = [RetainedResult] /\
  worker_bookkeeping (ChildrenRound false true) 0 = 1.
Proof. repeat split; reflexivity. Qed.

Lemma worker_bookkeeping_outside_pool round lane :
  2 <= lane -> worker_bookkeeping round lane = 0.
Proof. destruct round; destruct lane as [|[|lane]]; cbn; intros; try lia; reflexivity. Qed.

(** Total modeled cells/records for these two lanes. The two extra shared
    slots per frame conservatively cover join bookkeeping. This sum is not
    a byte-size or a bound on the payload stored in any of the counted slots. *)
Lemma two_lane_storage_bound round array_cells per_worker shared :
  (forall lane, worker_bookkeeping round lane <= per_worker) ->
  array_cells + queued_children round + saved_continuations round +
    2 * open_fork_frames round <= shared ->
  worker_bookkeeping round 0 + worker_bookkeeping round 1 +
    (array_cells + queued_children round + saved_continuations round +
      2 * open_fork_frames round) <= 2 * per_worker + shared.
Proof. intros Hlocal Hshared; specialize (Hlocal 0) as Hzero; specialize (Hlocal 1); lia. Qed.

Definition schedule_work (trace : list pool_round) : nat :=
  fold_right (fun round total => occupied_slots round + total) 0 trace.

Fixpoint child_rounds (left right : nat) : list pool_round :=
  match left, right with
  | 0, r => repeat (ChildrenRound false true) r
  | S l, 0 => ChildrenRound true false :: child_rounds l 0
  | S l, S r => ChildrenRound true true :: child_rounds l r
  end.

Lemma child_rounds_length left right :
  length (child_rounds left right) = Nat.max left right.
Proof.
  revert right; induction left as [|l IH]; intro r.
  - cbn; apply repeat_length.
  - destruct r; cbn; rewrite IH; [rewrite Nat.max_0_r|]; reflexivity.
Qed.
Lemma child_rounds_work left right :
  schedule_work (child_rounds left right) = left + right.
Proof.
  revert right; induction left as [|l IH]; intro r.
  - cbn; induction r; cbn; auto.
  - destruct r; cbn; rewrite IH; lia.
Qed.
Lemma schedule_work_app first second :
  schedule_work (first ++ second) = schedule_work first + schedule_work second.
Proof.
  induction first as [|round first IH]; [reflexivity|].
  change (occupied_slots round + schedule_work (first ++ second) =
    occupied_slots round + schedule_work first + schedule_work second).
  rewrite IH; lia.
Qed.
Lemma parent_rounds_work cost : schedule_work (repeat ParentRound cost) = cost.
Proof. induction cost; cbn; auto. Qed.
Lemma pool_round_bounds round :
  occupied_slots round <= 2 /\ queued_children round <= 1 /\
  saved_continuations round <= 1 /\ open_fork_frames round <= 1.
Proof.
  destruct round as [|[] []];
    cbv [occupied_slots queued_children saved_continuations open_fork_frames];
    repeat split; lia.
Qed.

Definition fork_rounds prices wl wr : list pool_round :=
  repeat ParentRound (fork_cost prices) ++ child_rounds wl wr ++
  repeat ParentRound (join_cost prices).
Lemma fork_rounds_length prices wl wr :
  length (fork_rounds prices wl wr) = fork_cost prices + Nat.max wl wr + join_cost prices.
Proof. unfold fork_rounds; rewrite !length_app, !repeat_length, child_rounds_length; lia. Qed.
Lemma fork_rounds_work prices wl wr :
  schedule_work (fork_rounds prices wl wr) = fork_cost prices + wl + wr + join_cost prices.
Proof. unfold fork_rounds; rewrite !schedule_work_app, !parent_rounds_work, child_rounds_work; lia. Qed.

(** Each constructor refers to the executed residual source. In particular,
    [PoolFork] must exhibit the two canonical counted child executions; bare
    numerical work/span inequalities cannot construct a certificate. [PoolBind]
    completes its first frame before beginning the continuation. [PoolSerial]
    imports canonical serial executions, including array-handler tick prefixes.
    No constructor accepts recursive forks in a child or overlapping frames. *)
Inductive pool_execution (prices : Prices) : forall R,
    itree (ForkEvent +' TimeE) R -> list pool_round -> R -> Prop :=
| PoolSerial R (program : itree TimeE R) cost result :
    (cost,result) ∈ count program ->
    pool_execution prices R (translate (@inr1 ForkEvent TimeE) program)
      (repeat ParentRound cost) result
| PoolFork A B (left : itree TimeE A) (right : itree TimeE B) wl wr x y :
    (wl,x) ∈ count left -> (wr,y) ∈ count right ->
    pool_execution prices (A*B) (trigger (Fork left right))
      (fork_rounds prices wl wr) (x,y)
| PoolTick : pool_execution prices unit (trigger Tick) [ParentRound] tt
| PoolBind X R (program : itree (ForkEvent +' TimeE) X)
    (next : X -> itree (ForkEvent +' TimeE) R) first second x result :
    pool_execution prices X program first x ->
    pool_execution prices R (next x) second result ->
    pool_execution prices R (program >>= next) (first ++ second) result
| PoolTau R (program : itree (ForkEvent +' TimeE) R) trace result :
    pool_execution prices R program trace result ->
    pool_execution prices R (Tau program) trace result
| PoolEq R (program source : itree (ForkEvent +' TimeE) R) trace result :
    program ≅ source -> pool_execution prices R source trace result ->
    pool_execution prices R program trace result.
Arguments pool_execution prices {R} _ _ _.

#[global] Instance eq_itree_pool_execution prices R :
  Proper (eq_itree eq ==> eq ==> eq ==> iff) (@pool_execution prices R).
Proof.
  intros p q Heq t t' <- x x' <-; split; intro H.
  - eapply PoolEq; [symmetry; exact Heq|exact H].
  - eapply PoolEq; [exact Heq|exact H].
Qed.

Theorem pool_execution_accounting prices R (program : itree (ForkEvent +' TimeE) R)
    trace result : pool_execution prices program trace result ->
  forall w s, ((w + schedule_work trace,s + length trace),result) ∈
    interp_state (h_parallel prices) program (w,s).
Proof.
  intro H; induction H; intros w s.
  - replace (w,s) with (w+0,s+0) by (f_equal; lia).
    rewrite parallel_time_count, parent_rounds_work, repeat_length.
    unfold ITree.map; eapply Leaf_bind; [exact H|apply Leaf_Ret].
  - rewrite fork_rounds_work, fork_rounds_length.
    rewrite interp_state_trigger.
    replace (w + (fork_cost prices + wl + wr + join_cost prices))
      with (w + fork_cost prices + wl + wr + join_cost prices) by lia.
    replace (s + (fork_cost prices + Nat.max wl wr + join_cost prices))
      with (s + fork_cost prices + Nat.max wl wr + join_cost prices) by lia.
    apply parallel_branch_accounting; assumption.
  - rewrite interp_state_trigger; cbn.
    replace (w+1) with (S w) by lia; replace (s+1) with (S s) by lia.
    apply Leaf_Ret.
  - rewrite interp_state_bind, schedule_work_app, length_app.
    eapply Leaf_bind; [apply IHpool_execution1|].
    cbn; replace (w + (schedule_work first + schedule_work second))
      with ((w+schedule_work first)+schedule_work second) by lia.
    replace (s + (length first + length second))
      with ((s+length first)+length second) by lia.
    apply IHpool_execution2.
  - rewrite interp_state_tau; apply Leaf_Tau; apply IHpool_execution.
  - rewrite H; apply IHpool_execution.
Qed.

Definition scheduled prices {A R} (program : itree (ParallelE A) R) array trace outcome : Prop :=
  pool_execution prices (run_parent_from program array) trace outcome.

Theorem scheduled_attains prices A R (program : itree (ParallelE A) R)
    array trace outcome : scheduled prices program array trace outcome ->
  ((schedule_work trace,length trace),outcome) ∈
    run_parallel_from prices program array (0,0).
Proof. intro H; exact (pool_execution_accounting prices _ _ _ _ H 0 0). Qed.
Theorem scheduled_pool_budget prices A R (program : itree (ParallelE A) R)
    array trace outcome : scheduled prices program array trace outcome ->
  Forall (fun round => occupied_slots round <= 2 /\ queued_children round <= 1 /\
    saved_continuations round <= 1 /\ open_fork_frames round <= 1) trace.
Proof. intro H; apply Forall_forall; intros round Hin; apply pool_round_bounds. Qed.

Theorem scheduled_worker_bookkeeping prices A R (program : itree (ParallelE A) R)
    array trace outcome : scheduled prices program array trace outcome ->
  Forall (fun round => forall lane, worker_bookkeeping round lane <= 1) trace.
Proof.
  intro H; apply Forall_forall; intros round Hin lane; apply worker_bookkeeping_bound.
Qed.

Lemma scheduled_lift_serial prices A R (program : itree (ArrayE A +' TimeE) R)
    array cost outcome :
  (cost,outcome) ∈ run_count_from program array 0 ->
  scheduled prices (lift_serial program) array (repeat ParentRound cost) outcome.
Proof.
  intro H; unfold scheduled; eapply PoolEq; [apply run_parent_lift_serial|].
  apply PoolSerial; exact H.
Qed.

Lemma pool_ret prices R (value : R) : pool_execution prices (Ret value) [] value.
Proof.
  eapply PoolEq with (source := translate (@inr1 ForkEvent TimeE) (Ret value)).
  - symmetry; apply translate_ret.
  - apply PoolSerial with (cost := 0); unfold count; apply LeafRet; rewrite observe_count; reflexivity.
Qed.
Lemma scheduled_ret prices A R (value : R) (array : array_state A) :
  scheduled prices (Ret value) array [] (Some (array,value)).
Proof.
  unfold scheduled, run_parent_from; eapply PoolEq.
  - apply unfold_state_option.
  - cbn; apply pool_ret.
Qed.
Lemma scheduled_bind prices A X R (program : itree (ParallelE A) X)
    (next : X -> itree (ParallelE A) R) array array' first second value outcome :
  scheduled prices program array first (Some (array',value)) ->
  scheduled prices (next value) array' second outcome ->
  scheduled prices (program >>= next) array (first ++ second) outcome.
Proof.
  intros Hp Hn; unfold scheduled in *; eapply PoolEq.
  - apply state_option_bind.
  - eapply PoolBind; [exact Hp|exact Hn].
Qed.
Lemma scheduled_fork prices Element A B (left : itree TimeE A) (right : itree TimeE B)
    (array : array_state Element) wl wr x y :
  (wl,x) ∈ count left -> (wr,y) ∈ count right ->
  scheduled prices (fork left right) array (fork_rounds prices wl wr) (Some (array,(x,y))).
Proof.
  intros Hl Hr; unfold scheduled, run_parent_from, fork.
  eapply PoolEq; [apply unfold_state_option|].
  cbn -[interp_state]; rewrite bind_trigger.
  rewrite bind_vis; setoid_rewrite bind_ret_l.
  eapply PoolEq with (source := trigger (Fork left right) >>=
    fun pair => Tau (run_parent_from (Ret pair) array)).
  - rewrite bind_trigger; reflexivity.
  -
  replace (fork_rounds prices wl wr) with (fork_rounds prices wl wr ++ [])
    by apply app_nil_r.
  eapply PoolBind; [apply PoolFork; eassumption|].
  apply PoolTau; eapply PoolEq; [apply unfold_state_option|].
  cbn; apply pool_ret.
Qed.

(** Parent-array reachability uses the same canonical interpreted residuals as
    Array.v. Children and coordination handlers do not change this array. *)
Lemma h_parent_monotone A X (event : ParallelE A X) array array' value :
  Some (array',value) ∈ unOptionT (h_parent X event array) ->
  length array <= length array'.
Proof.
  destruct event as [ae|other]; cbn.
  - rewrite translate_to_interp; intro H; apply interp_leaf_source in H.
    exact (h_effects_monotone A X (ae |) array array' value H).
  - rewrite bind_trigger; intro H; apply Leaf_Vis_inv in H as [reply H].
    apply Leaf_Ret_inv in H; inversion H; subst; lia.
Qed.
Lemma run_parent_from_monotone A R (program : itree (ParallelE A) R) array array' value :
  Some (array',value) ∈ run_parent_from program array -> length array <= length array'.
Proof.
  intro Hleaf.
  assert (Hpost : run_parent_from program array ⤳ (fun outcome =>
    match outcome with Some (a,_) => length array <= length a | None => True end)).
  { apply state_option_invariant.
    - intros X event a a' x Hlen Hstep.
      pose proof (h_parent_monotone A X event a a' x Hstep); lia.
    - lia. }
  destruct (Leaf_eutt_l _ _ _ Hpost Hleaf) as [outcome [_ Hbound]]; exact Hbound.
Qed.
Lemma run_parallel_from_monotone prices A R (program : itree (ParallelE A) R)
    array ws final array' value :
  (final,Some (array',value)) ∈ run_parallel_from prices program array ws ->
  length array <= length array'.
Proof.
  intro H; apply run_parent_from_monotone with (program := program) (value := value).
  exact (interp_state_leaf_source (h_parallel prices) _ _ _ H).
Qed.

Definition parallel_array_bound prices {A R} (program : itree (ParallelE A) R)
    initial_array initial_ws bound : Prop :=
  forall tail array ws,
  Subtree.subtree (run_parallel_from prices tail array ws)
    (run_parallel_from prices program initial_array initial_ws) -> length array <= bound.

Theorem parallel_final_bound_subtree_leaf prices A R (program : itree (ParallelE A) R)
    initial_array initial_ws bound final final_array value :
  (final,Some (final_array,value)) ∈ run_parallel_from prices program initial_array initial_ws ->
  length final_array <= bound ->
  parallel_array_bound prices program initial_array initial_ws bound.
Proof.
  intros Hleaf Hbound tail array ws Hsub.
  pose proof (subtree_finite _ _ Hsub (closed_leaf_finite _ _ Hleaf)) as Hfin.
  apply finite_leaf_non_interactive in Hfin as [[last outcome] Hlast].
  pose proof (Subtree.subtree_image _ _ _ Hsub Hlast) as Hwhole.
  rewrite (closed_leaf_eutt _ _ Hleaf) in Hwhole.
  apply Leaf_Ret_inv in Hwhole; inversion Hwhole; subst.
  pose proof (run_parallel_from_monotone prices A R tail array ws final final_array value Hlast).
  lia.
Qed.

Lemma state_option_eutt {E F S R}
    (handler : E ~> Monads.stateT S (optionT (itree F)))
    (program source : itree E R) array :
  program ≈ source ->
  unOptionT (interp_state handler program array) ≈
    unOptionT (interp_state handler source array).
Proof.
  revert program source array; einit; ecofix CIH; intros program source array Heq.
  rewrite !unfold_state_option; punfold Heq; red in Heq.
  induction Heq; intros; subst; cbn -[interp_state unOptionT]; pclearbot.
  - eret.
  - etau; ebase; right; apply CIHL; exact REL.
  - ebind; econstructor; [reflexivity|].
    intros [[a x]|] ? []; cbn -[interp_state unOptionT].
    + etau; ebase; right; apply CIHL; apply REL.
    + eret.
  - rewrite tau_euttge, unfold_state_option; eauto.
  - rewrite tau_euttge, unfold_state_option; eauto.
Qed.

Lemma run_count_eutt A R (program source : itree (ArrayE A +' TimeE) R) array cost :
  program ≈ source -> run_count_from program array cost ≈ run_count_from source array cost.
Proof.
  intro H; unfold run_count_from, array_to_time_from, count_from.
  apply eutt_interp_state_eq; [apply state_option_eutt; exact H|reflexivity].
Qed.
Lemma run_count_serialization_lift_leaf A R (program : itree (ArrayE A +' TimeE) R)
    array initial cost outcome :
  (cost,outcome) ∈ run_count_from program array initial ->
  (cost,outcome) ∈ run_count_from (serialization (lift_serial program)) array initial.
Proof.
  intro H; rewrite (run_count_eutt A R _ _ array initial (serialization_lift_serial A R program)).
  exact H.
Qed.

Lemma array_to_time_translate_time A R (program : itree TimeE R) (array : array_state A) :
  array_to_time_from (translate (@inr1 (ArrayE A) TimeE) program) array ≈
    (value <- program ;; Ret (Some (array,value))).
Proof.
  revert program; ginit; gcofix CIH; intro program.
  rewrite unfold_translate, (unfold_bind program (fun value => Ret (Some (array,value)))).
  destruct (observe program) as [value|tail|X event next]; cbn -[array_to_time_from].
  - unfold array_to_time_from; rewrite unfold_state_option; cbn.
    gstep; constructor; reflexivity.
  - unfold array_to_time_from at 1; rewrite unfold_state_option; cbn -[interp_state unOptionT].
    gstep; constructor; gbase; apply CIH.
  - destruct event; unfold array_to_time_from at 1; rewrite unfold_state_option.
    cbn -[interp_state]; rewrite bind_trigger, !bind_vis.
    setoid_rewrite bind_ret_l.
    gstep; constructor; intro u; destruct u.
    guclo eqit_clo_trans; econstructor 1 with (RR1 := eq) (RR2 := eq).
    + apply eqit_Tau_l; reflexivity.
    + reflexivity.
    + gbase; apply CIH.
    + intros; subst; reflexivity.
    + intros; subst; reflexivity.
Qed.

Lemma run_count_time_leaf A R (program : itree TimeE R) (array : array_state A)
    initial cost value :
  (cost,value) ∈ count_from program initial ->
  (cost,Some (array,value)) ∈
    run_count_from (translate (@inr1 (ArrayE A) TimeE) program) array initial.
Proof.
  intro H; unfold run_count_from.
  assert (Heq : count_from
    (array_to_time_from (translate (@inr1 (ArrayE A) TimeE) program) array) initial ≈
    count_from (value <- program ;; Ret (Some (array,value))) initial).
  { unfold count_from; apply eutt_interp_state_eq; [apply array_to_time_translate_time|reflexivity]. }
  rewrite Heq; eapply count_bind_leaf; [exact H|].
  apply LeafRet; rewrite observe_count; reflexivity.
Qed.

Lemma serialization_fork A B Element (left : itree TimeE A) (right : itree TimeE B) :
  serialization (fork left right : itree (ParallelE Element) (A*B)) ≈
    translate (@inr1 (ArrayE Element) TimeE) (serial_fork _ (Fork left right)).
Proof. unfold serialization, fork; rewrite interp_trigger; reflexivity. Qed.

Lemma run_count_serialization_fork_leaf Element A B (left : itree TimeE A)
    (right : itree TimeE B) wl wr x y (array : array_state Element) cost :
  (wl,x) ∈ count left -> (wr,y) ∈ count right ->
  (cost+wl+wr,Some (array,(x,y))) ∈
    run_count_from (serialization (fork left right)) array cost.
Proof.
  intros Hl Hr.
  rewrite (run_count_eutt _ _ _ _ array cost (serialization_fork A B Element left right)).
  apply run_count_time_leaf.
  replace (cost+wl+wr) with (cost+(wl+wr)) by lia.
  apply count_shift_leaf; apply serial_branch_accounting; assumption.
Qed.

Lemma run_count_serialization_bind_leaf A X R (program : itree (ParallelE A) X)
    (next : X -> itree (ParallelE A) R) array cost array' cost' value final outcome :
  (cost',Some (array',value)) ∈ run_count_from (serialization program) array cost ->
  (final,outcome) ∈ run_count_from (serialization (next value)) array' cost' ->
  (final,outcome) ∈ run_count_from (serialization (program >>= next)) array cost.
Proof.
  intros Hp Hn; rewrite serialization_bind; eapply run_count_bind_leaf; eassumption.
Qed.
Lemma run_count_serialization_bind_failure A X R (program : itree (ParallelE A) X)
    (next : X -> itree (ParallelE A) R) array cost final :
  (final,None) ∈ run_count_from (serialization program) array cost ->
  (final,None) ∈ run_count_from (serialization (program >>= next)) array cost.
Proof.
  intro H; rewrite serialization_bind; apply run_count_bind_failure; exact H.
Qed.

Lemma run_count_serialization_ret A R (value : R) (array : array_state A) cost :
  (cost,Some (array,value)) ∈ run_count_from (serialization (Ret value)) array cost.
Proof. rewrite serialization_ret; apply run_count_from_ret; reflexivity. Qed.

Lemma serialization_serial_event A X (event : (ArrayE A +' TimeE) X) :
  serialization (trigger (serial_injection X event)) ≈ trigger event.
Proof.
  unfold serialization; rewrite interp_trigger; destruct event as [ae|te]; reflexivity.
Qed.
Lemma run_count_serialization_array_leaf A X (event : ArrayE A X)
    array initial final outcome :
  (final,outcome) ∈ run_count_from (trigger event) array initial ->
  (final,outcome) ∈ run_count_from (serialization (trigger event : itree (ParallelE A) X)) array initial.
Proof.
  intro H.
  rewrite (run_count_eutt A X _ _ array initial (serialization_serial_event A X (event |))).
  exact H.
Qed.
Lemma run_count_serialization_tick_bind A R (next : unit -> itree (ParallelE A) R)
    array cost final outcome :
  (final,outcome) ∈ run_count_from (serialization (next tt)) array (S cost) ->
  (final,outcome) ∈ run_count_from (serialization (trigger Tick >>= next)) array cost.
Proof.
  intro H; rewrite serialization_bind.
  assert (Heq : (serialization (trigger Tick : itree (ParallelE A) unit) >>=
      fun x => serialization (next x)) ≈ (trigger Tick >>= fun x => serialization (next x))).
  { apply eqit_bind; [exact (serialization_serial_event A unit (| Tick))|].
    intro x; reflexivity. }
  rewrite (run_count_eutt A R _ _ array cost Heq).
  apply run_count_tick_bind; exact H.
Qed.

Theorem scheduled_matches_leaf prices A R (program : itree (ParallelE A) R)
    array trace outcome work span :
  scheduled prices program array trace outcome ->
  ((work,span),outcome) ∈ run_parallel_from prices program array (0,0) ->
  schedule_work trace = work /\ length trace = span.
Proof.
  intros Hsched Hleaf; pose proof (scheduled_attains prices A R program array trace outcome Hsched) as H.
  rewrite (closed_leaf_eutt _ _ H) in Hleaf.
  apply Leaf_Ret_inv in Hleaf; inversion Hleaf; auto.
Qed.

(** Pending parent handlers retain their incoming array. The bound includes
    every ordinary allocation/read/set charge before the array-step commits. *)
Theorem parallel_final_bound_handler_subtree_leaf prices A R
    (program : itree (ParallelE A) R) initial_array initial_ws bound final final_array value :
  (final,Some (final_array,value)) ∈ run_parallel_from prices program initial_array initial_ws ->
  length final_array <= bound ->
  forall X (event : ParallelE A X) (next : X -> itree (ParallelE A) R) array
    (pending : itree (ForkEvent +' TimeE) (option (array_state A * X))) ws,
  Subtree.subtree pending (unOptionT (h_parent X event array)) ->
  Subtree.subtree
    (interp_state (h_parallel prices) (outcome <- pending ;; match outcome with
      | None => Ret None
      | Some (array',x) => Tau (run_parent_from (next x) array')
      end) ws)
    (run_parallel_from prices program initial_array initial_ws) ->
  length array <= bound.
Proof.
  intros Hleaf Hbound X event next array pending ws Hpending Hsub.
  pose proof (subtree_finite _ _ Hsub (closed_leaf_finite _ _ Hleaf)) as Hfin.
  apply finite_leaf_non_interactive in Hfin as [[last outcome] Hlast].
  pose proof (Subtree.subtree_image _ _ _ Hsub Hlast) as Hwhole.
  rewrite (closed_leaf_eutt _ _ Hleaf) in Hwhole.
  apply Leaf_Ret_inv in Hwhole; inversion Hwhole; subst.
  apply interp_state_leaf_source in Hlast; cbn in Hlast.
  apply Leaf_bind_inv in Hlast as [middle [Hmiddle Htail]].
  destruct middle as [[array' x]|].
  - apply Leaf_Tau_inv in Htail.
    pose proof (run_parent_from_monotone A R (next x) array' final_array value Htail).
    pose proof (h_parent_monotone A X event array array' x
      (Subtree.subtree_image _ _ _ Hpending Hmiddle)); lia.
  - apply Leaf_Ret_inv in Htail; discriminate.
Qed.

(** During a running fork, both children and all fork/join ticks are array-free.
    Thus the current canonical array is retained unchanged throughout every
    pending closed handler subtree, including while a child finishes first. *)
Theorem parallel_waiting_array_bound prices A R (program : itree (ParallelE A) R)
    initial_array initial_ws bound final final_array value
    (tail : itree (ParallelE A) R) array ws B C (left : itree TimeE B) (right : itree TimeE C)
    (next : B*C -> itree (ParallelE A) R)
    fork_ws (pending : itree void1 ((nat*nat)*(B*C))) :
  (final,Some (final_array,value)) ∈ run_parallel_from prices program initial_array initial_ws ->
  length final_array <= bound ->
  Subtree.subtree (run_parallel_from prices tail array ws)
    (run_parallel_from prices program initial_array initial_ws) ->
  observe tail = VisF (| (Fork left right |)) next ->
  Subtree.subtree pending (parallel_fork prices _ (Fork left right) fork_ws) ->
  length array <= bound.
Proof.
  intros Hleaf Hbound Hsub Hfork Hpending.
  exact (parallel_final_bound_subtree_leaf prices A R program initial_array initial_ws
    bound final final_array value Hleaf Hbound tail array ws Hsub).
Qed.

Lemma run_count_shift_leaf A R (program : itree (ArrayE A +' TimeE) R)
    array cost outcome extra :
  (cost,outcome) ∈ run_count_from program array 0 ->
  (extra+cost,outcome) ∈ run_count_from program array extra.
Proof. apply count_shift_leaf. Qed.

(** The canonical certificate for a serial prefix, one fork, and a serial suffix. *)
Definition serial_fork_serial_trace prices prefix wl wr suffix :=
  repeat ParentRound prefix ++
    (fork_rounds prices wl wr ++ repeat ParentRound suffix).

(** A common shallow composition rule, not an algorithm or a target DSL.
    Both serial fragments may contain arbitrary canonical array operations and
    charged loops. All three executions use the exact same source fragments.
    This rule supplies whole-program outcome preservation as well as exact
    accounting and an operational two-worker certificate. *)
Theorem serial_fork_serial_execution_exact prices Element Input A B R
    (before : itree (ArrayE Element +' TimeE) Input)
    (left : Input -> itree TimeE A) (right : Input -> itree TimeE B)
    (after : Input -> A*B -> itree (ArrayE Element +' TimeE) R)
    initial_array middle_array final_array input x y result prefix wl wr suffix :
  (prefix,Some (middle_array,input)) ∈ run_count_from before initial_array 0 ->
  (wl,x) ∈ count (left input) -> (wr,y) ∈ count (right input) ->
  (suffix,Some (final_array,result)) ∈ run_count_from (after input (x,y)) middle_array 0 ->
  let program := (input <- lift_serial before ;;
    pair <- fork (left input) (right input) ;; lift_serial (after input pair)) in
  scheduled prices program initial_array
    (serial_fork_serial_trace prices prefix wl wr suffix) (Some (final_array,result)) /\
  ((prefix + fork_cost prices + wl + wr + join_cost prices + suffix,
    prefix + fork_cost prices + Nat.max wl wr + join_cost prices + suffix),
    Some (final_array,result)) ∈ run_parallel_from prices program initial_array (0,0) /\
  (prefix+wl+wr+suffix,Some (final_array,result)) ∈
    run_count_from (serialization program) initial_array 0.
Proof.
  intros Hbefore Hl Hr Hafter program.
  assert (Hsched : scheduled prices program initial_array
      (serial_fork_serial_trace prices prefix wl wr suffix) (Some (final_array,result))).
  { unfold program, serial_fork_serial_trace; eapply scheduled_bind.
    - apply scheduled_lift_serial; exact Hbefore.
    - eapply scheduled_bind.
      + apply scheduled_fork; eassumption.
      + apply scheduled_lift_serial; exact Hafter. }
  split; [exact Hsched|]; split.
  - pose proof (scheduled_attains prices Element R program initial_array _
      (Some (final_array,result)) Hsched) as H.
    unfold serial_fork_serial_trace in H.
    rewrite !schedule_work_app, !parent_rounds_work, fork_rounds_work,
      !length_app, !repeat_length, fork_rounds_length in H.
    replace (prefix + fork_cost prices + wl + wr + join_cost prices + suffix)
      with (prefix + (fork_cost prices + wl + wr + join_cost prices + suffix)) by lia.
    replace (prefix + fork_cost prices + Nat.max wl wr + join_cost prices + suffix)
      with (prefix + (fork_cost prices + Nat.max wl wr + join_cost prices + suffix)) by lia.
    exact H.
  - unfold program; eapply run_count_serialization_bind_leaf.
    + apply run_count_serialization_lift_leaf; exact Hbefore.
    + eapply run_count_serialization_bind_leaf.
      * apply run_count_serialization_fork_leaf; eassumption.
      * apply run_count_serialization_lift_leaf.
        apply run_count_shift_leaf; exact Hafter.
Qed.

(** Compatibility interface for callers that do not need the canonical trace. *)
Theorem serial_fork_serial_execution prices Element Input A B R
    (before : itree (ArrayE Element +' TimeE) Input)
    (left : Input -> itree TimeE A) (right : Input -> itree TimeE B)
    (after : Input -> A*B -> itree (ArrayE Element +' TimeE) R)
    initial_array middle_array final_array input x y result prefix wl wr suffix :
  (prefix,Some (middle_array,input)) ∈ run_count_from before initial_array 0 ->
  (wl,x) ∈ count (left input) -> (wr,y) ∈ count (right input) ->
  (suffix,Some (final_array,result)) ∈ run_count_from (after input (x,y)) middle_array 0 ->
  let program := (input <- lift_serial before ;;
    pair <- fork (left input) (right input) ;; lift_serial (after input pair)) in
  exists trace,
    scheduled prices program initial_array trace (Some (final_array,result)) /\
    ((prefix + fork_cost prices + wl + wr + join_cost prices + suffix,
      prefix + fork_cost prices + Nat.max wl wr + join_cost prices + suffix),
      Some (final_array,result)) ∈ run_parallel_from prices program initial_array (0,0) /\
    (prefix+wl+wr+suffix,Some (final_array,result)) ∈
      run_count_from (serialization program) initial_array 0.
Proof.
  intros Hbefore Hl Hr Hafter program.
  exists (serial_fork_serial_trace prices prefix wl wr suffix).
  exact (serial_fork_serial_execution_exact prices Element Input A B R
    before left right after initial_array middle_array final_array input x y result
    prefix wl wr suffix Hbefore Hl Hr Hafter).
Qed.

Corollary serial_fork_serial_outcome prices Element Input A B R
    (before : itree (ArrayE Element +' TimeE) Input)
    (left : Input -> itree TimeE A) (right : Input -> itree TimeE B)
    (after : Input -> A*B -> itree (ArrayE Element +' TimeE) R)
    initial_array middle_array final_array input x y result prefix wl wr suffix :
  (prefix,Some (middle_array,input)) ∈ run_count_from before initial_array 0 ->
  (wl,x) ∈ count (left input) -> (wr,y) ∈ count (right input) ->
  (suffix,Some (final_array,result)) ∈ run_count_from (after input (x,y)) middle_array 0 ->
  let program := (input <- lift_serial before ;;
    pair <- fork (left input) (right input) ;; lift_serial (after input pair)) in
  eutt (fun parallel serial => snd parallel = snd serial)
    (run_parallel_from prices program initial_array (0,0))
    (run_count_from (serialization program) initial_array 0).
Proof.
  intros Hp Hl Hr Hs program.
  destruct (serial_fork_serial_execution_exact prices Element Input A B R before left right after
    initial_array middle_array final_array input x y result prefix wl wr suffix Hp Hl Hr Hs)
    as [_ [Hparallel Hserial]].
  unfold program.
  rewrite (closed_leaf_eutt _ _ Hparallel), (closed_leaf_eutt _ _ Hserial).
  apply eutt_Ret; reflexivity.
Qed.

Lemma run_parallel_from_ret prices A R (program : itree (ParallelE A) R) array ws value :
  observe program = RetF value ->
  (ws,Some (array,value)) ∈ run_parallel_from prices program array ws.
Proof.
  intro H; eapply run_parallel_from_observe with (program' := Ret value);
    [exact H|apply run_parallel_ret].
Qed.
Lemma run_parallel_from_tau prices A R (program tail : itree (ParallelE A) R)
    array ws final outcome :
  observe program = TauF tail ->
  (final,outcome) ∈ run_parallel_from prices tail array ws ->
  (final,outcome) ∈ run_parallel_from prices program array ws.
Proof.
  intros Hobs Htail; unfold run_parallel_from, run_parent_from in *.
  rewrite (unfold_state_option h_parent program array), Hobs; cbn.
  rewrite interp_state_tau; apply Leaf_Tau; exact Htail.
Qed.
Lemma run_parallel_fork_leaf prices Element A B (left : itree TimeE A) (right : itree TimeE B)
    wl wr x y (array : array_state Element) w s :
  (wl,x) ∈ count left -> (wr,y) ∈ count right ->
  ((w+fork_cost prices+wl+wr+join_cost prices,
    s+fork_cost prices+Nat.max wl wr+join_cost prices),Some (array,(x,y))) ∈
    run_parallel_from prices (fork left right) array (w,s).
Proof.
  intros Hl Hr.
  rewrite <- (bind_ret_r (fork left right)).
  eapply run_parallel_fork_bind; [exact Hl|exact Hr|apply run_parallel_ret].
Qed.
Lemma run_parallel_init_pair_bind prices A R (first second : A)
    (next : itree (ParallelE A) R) w s final outcome :
  (final,outcome) ∈ run_parallel_from prices next [Some first;Some second] (w+5,s+5) ->
  (final,outcome) ∈ run_parallel_from prices
    (array_alloc 2 ;; array_set 0 first ;; array_set 1 second ;; next) [] (w,s).
Proof.
  intro H; apply run_parallel_alloc_bind; cbn.
  apply run_parallel_set_bind; [cbn; lia|].
  apply run_parallel_set_bind; [cbn; lia|].
  cbn; replace (S (S (w+3))) with (w+5) by lia.
  replace (S (S (s+3))) with (s+5) by lia; exact H.
Qed.

Lemma run_parallel_cost_iter_step prices A State R
    (body : State -> itree (ParallelE A) (State+R)) state array w s
    array' ws' step final outcome :
  (ws',Some (array',step)) ∈ run_parallel_from prices (body state) array (S w,S s) ->
  (match step with
   | inl state' => (final,outcome) ∈ run_parallel_from prices (cost_iter body state') array' ws'
   | inr result => (final,outcome) = (ws',Some (array',result))
   end) ->
  (final,outcome) ∈ run_parallel_from prices (cost_iter body state) array (w,s).
Proof.
  intros Hb Hnext; unfold cost_iter in *; rewrite unfold_iter.
  eapply run_parallel_bind_leaf.
  - unfold iter_body_entry; eapply run_parallel_tick_bind; exact Hb.
  - destruct step as [state'|result]; cbn in *.
    + eapply run_parallel_from_tau; [reflexivity|exact Hnext].
    + inversion Hnext; subst; apply run_parallel_ret.
Qed.

#[global] Instance eq_itree_scheduled prices A R :
  Proper (eq_itree eq ==> eq ==> eq ==> eq ==> iff) (@scheduled prices A R).
Proof.
  intros p q Heq a a' <- tr tr' <- v v' <-; unfold scheduled.
  apply eq_itree_pool_execution; [apply eq_itree_run_parent_from; [exact Heq|reflexivity]|reflexivity|reflexivity].
Qed.
Lemma scheduled_array_leaf prices A X (event : ArrayE A X) array cost outcome :
  (cost,outcome) ∈ run_count_from (trigger event) array 0 ->
  scheduled prices (trigger event) array (repeat ParentRound cost) outcome.
Proof.
  intro H; pose proof (scheduled_lift_serial prices A X (trigger event) array cost outcome H) as Hs.
  change (scheduled prices (lift_serial (trigger (event |))) array
    (repeat ParentRound cost) outcome) in Hs.
  rewrite lift_serial_trigger in Hs; exact Hs.
Qed.
Lemma scheduled_tick prices A (array : array_state A) :
  scheduled prices (trigger Tick) array [ParentRound] (Some (array,tt)).
Proof.
  pose proof (scheduled_lift_serial prices A unit (trigger Tick) array 1 (Some (array,tt))) as H.
  assert (Htick : (1,Some (array,tt)) ∈ run_count_from (trigger Tick) array 0).
  { rewrite <- (bind_ret_r (trigger Tick : itree (ArrayE A +' TimeE) unit)).
    eapply run_count_tick_bind with (continuation := fun x => Ret x).
    apply run_count_from_ret; reflexivity. }
  specialize (H Htick).
  change (scheduled prices (lift_serial (trigger (| Tick))) array [ParentRound]
    (Some (array,tt))) in H.
  rewrite lift_serial_trigger in H; exact H.
Qed.

Lemma positive_price_domain_nonempty : exists prices, positive_prices prices.
Proof. exists {| fork_cost := 1; join_cost := 1 |}; split; cbn; lia. Qed.
Lemma branch_speedup_condition prices wl wr :
  fork_cost prices + Nat.max wl wr + join_cost prices < wl + wr <->
  fork_cost prices + join_cost prices < Nat.min wl wr.
Proof.
  destruct (Nat.le_ge_cases wl wr) as [H|H].
  - rewrite Nat.max_r, Nat.min_l by assumption; lia.
  - rewrite Nat.max_l, Nat.min_r by assumption; lia.
Qed.

(** Executable checks are small regressions, not scheduling or fidelity proofs. *)
Module Regression.
Definition prices := {| fork_cost := 2; join_cost := 3 |}.
Definition program : itree (ParallelE nat) nat :=
  trigger Tick ;; array_alloc 1 ;;
  pair <- fork (cost_add 2 3) (cost_mul 4 5) ;;
  value <- cost_add (fst pair) (snd pair) ;;
  array_set 0 value ;; array_read 0.
Example parallel : observe_closed 500 (run_parallel prices program) =
  Some ((13,12),Some ([Some 25],25)).
Proof. vm_compute; reflexivity. Qed.
Example serial : observe_closed 500 (run_count (serialization program)) =
  Some (8,Some ([Some 25],25)).
Proof. vm_compute; reflexivity. Qed.
Example failure_parallel : observe_closed 100
  (run_parallel prices (array_read (A := nat) 0)) = Some ((1,1),None).
Proof. vm_compute; reflexivity. Qed.
Example failure_serial : observe_closed 100
  (run_count (serialization (array_read (A := nat) 0 : itree (ParallelE nat) nat))) =
    Some (1,None).
Proof. vm_compute; reflexivity. Qed.
End Regression.
