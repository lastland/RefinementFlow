From Stdlib Require Import List.
From RefineToITree Require Import FibonacciL4.
Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.

(** Observation fuel bounds the evaluator, not the abstract time cost.
    The general theorems establish termination independently of these runs. *)
Example Fib_L1_samples :
  List.map (fun input => observe_closed 1000 (count (Fib_L1 input))) [0; 1; 2; 5; 10] =
  [Some (1, 0); Some (1, 1); Some (4, 1); Some (22, 5); Some (265, 55)].
Proof. vm_compute; reflexivity. Qed.

Example Fib_L2_samples :
  List.map (fun input => observe_closed 1000 (run_count (Fib_L2 input))) [0; 1; 2; 5; 10] =
  [Some (8, Some ([Some 0; Some 1], 0));
   Some (14, Some ([Some 1; Some 1], 1));
   Some (20, Some ([Some 1; Some 2], 1));
   Some (38, Some ([Some 5; Some 8], 5));
   Some (68, Some ([Some 55; Some 89], 55))].
Proof. vm_compute; reflexivity. Qed.

(** Inputs around powers of two exercise mask changes and both bit branches. *)
Example Fib_L3_samples :
  List.map (fun input => observe_closed 1000 (run_count (Fib_L3 input)))
    [0; 1; 2; 3; 4; 5; 7; 8; 10; 15; 16] =
  [Some (9, Some ([Some 0; Some 1], 0));
   Some (21, Some ([Some 1; Some 1], 1));
   Some (34, Some ([Some 1; Some 2], 1));
   Some (34, Some ([Some 2; Some 3], 2));
   Some (47, Some ([Some 3; Some 5], 3));
   Some (47, Some ([Some 5; Some 8], 5));
   Some (47, Some ([Some 13; Some 21], 13));
   Some (60, Some ([Some 21; Some 34], 21));
   Some (60, Some ([Some 55; Some 89], 55));
   Some (60, Some ([Some 610; Some 987], 610));
   Some (73, Some ([Some 987; Some 1597], 987))].
Proof. vm_compute; reflexivity. Qed.

(** Sequential L4 uses the same two-cell outcomes with one fewer arithmetic
    operation per processed bit. Include input 20 alongside mask boundaries. *)
Example Fib_L4_samples :
  List.map (fun input => observe_closed 1000 (run_count (Fib_L4 input)))
    [0; 1; 2; 3; 4; 5; 7; 8; 10; 15; 16; 20] =
  [Some (9, Some ([Some 0; Some 1], 0));
   Some (20, Some ([Some 1; Some 1], 1));
   Some (32, Some ([Some 1; Some 2], 1));
   Some (32, Some ([Some 2; Some 3], 2));
   Some (44, Some ([Some 3; Some 5], 3));
   Some (44, Some ([Some 5; Some 8], 5));
   Some (44, Some ([Some 13; Some 21], 13));
   Some (56, Some ([Some 21; Some 34], 21));
   Some (56, Some ([Some 55; Some 89], 55));
   Some (56, Some ([Some 610; Some 987], 610));
   Some (68, Some ([Some 987; Some 1597], 987));
   Some (68, Some ([Some 6765; Some 10946], 6765))].
Proof. vm_compute; reflexivity. Qed.

(** Report (L3 cost, L4 cost, saved ticks) only when both observed executions
    terminate successfully, including their array operations. *)
Definition fib_l4_observed_cost_saving input : option (nat * nat * nat) :=
  match observe_closed 1000 (run_count (Fib_L3 input)),
        observe_closed 1000 (run_count (Fib_L4 input)) with
  | Some (cost_l3, Some _), Some (cost_l4, Some _) =>
      Some (cost_l3, cost_l4, cost_l3 - cost_l4)
  | _, _ => None
  end.

Example Fib_L4_cost_saving_samples :
  List.map fib_l4_observed_cost_saving [0; 1; 2; 5; 10; 20] =
  [Some (9, 9, 0); Some (21, 20, 1); Some (34, 32, 2);
   Some (47, 44, 3); Some (60, 56, 4); Some (73, 68, 5)].
Proof. vm_compute; reflexivity. Qed.

Example Fib_L1_ignored :
  observe_closed 1000 (ignore_time (Fib_L1 5)) = Some 5.
Proof. vm_compute; reflexivity. Qed.

Example Fib_L2_ignored :
  observe_closed 1000 (run_ignore (Fib_L2 5)) =
  Some (Some ([Some 5; Some 8], 5)).
Proof. vm_compute; reflexivity. Qed.

Example Fib_L3_ignored :
  observe_closed 1000 (run_ignore (Fib_L3 10)) =
  Some (Some ([Some 55; Some 89], 55)).
Proof. vm_compute; reflexivity. Qed.

Example Fib_L4_ignored :
  observe_closed 1000 (run_ignore (Fib_L4 10)) =
  Some (Some ([Some 55; Some 89], 55)).
Proof. vm_compute; reflexivity. Qed.

(** Two allocations exercise fresh base indices, preservation of old cells,
    and reuse of the same canonical interpreter at a non-nat element type. *)
Definition bool_array_example :
    itree (ArrayE bool +' TimeE) (nat * (bool * bool)) :=
  function_entry (fun _ : unit =>
    first_index <- array_alloc 1 ;;
    array_set first_index true ;;
    second_index <- array_alloc 1 ;;
    first_value <- array_read first_index ;;
    array_set second_index false ;;
    second_value <- array_read second_index ;;
      Ret (second_index, (first_value, second_value))) tt.

Example bool_array_counted :
  observe_closed 1000 (run_count bool_array_example) =
  Some (9, Some ([Some true; Some false], (1, (true, false)))).
Proof. vm_compute; reflexivity. Qed.

Example bool_array_ignored :
  observe_closed 1000 (run_ignore bool_array_example) =
  Some (Some ([Some true; Some false], (1, (true, false)))).
Proof. vm_compute; reflexivity. Qed.

(** Primitive interpreter checks isolate automatic charges from function
    entry charges. Both uninitialized and invalid reads abort with None. *)
Example empty_allocation :
  observe_closed 100 (run_count (array_alloc (A := bool) 0)) =
  Some (1, Some ([], 0)).
Proof. vm_compute; reflexivity. Qed.

Example uninitialized_read :
  observe_closed 100
    (run_count (index <- array_alloc (A := nat) 1 ;;
      array_read index)) = Some (3, None).
Proof. vm_compute; reflexivity. Qed.

Example out_of_bounds_read :
  observe_closed 100 (run_count (array_read (A := nat) 0)) = Some (1, None).
Proof. vm_compute; reflexivity. Qed.

Example failed_set_skips_continuation :
  observe_closed 100
    (run_count (array_set (A := bool) 0 true ;;
      trigger Tick ;; Ret false)) =
  Some (1, None).
Proof. vm_compute; reflexivity. Qed.

(** The final loop-body invocation is charged too. *)
Example terminal_iteration_cost :
  observe_closed 100
    (count (cost_iter (fun _ : unit => Ret (inr 7)) tt)) = Some (1, 7).
Proof. vm_compute; reflexivity. Qed.

Example continuing_and_terminal_iteration_cost :
  observe_closed 100
    (count (cost_iter (fun remaining : nat =>
      match remaining with
      | 0 => Ret (inr 7)
      | S remaining => Ret (inl remaining)
      end) 1)) = Some (2, 7).
Proof. vm_compute; reflexivity. Qed.

(** Tau prefixes carry no charge; only the visible Tick contributes. *)
Example finite_tau_cost :
  observe_closed 100
    (count (Tau tick ;; Tau (Ret 3))) = Some (1, 3).
Proof. vm_compute; reflexivity. Qed.

Eval vm_compute in
  List.map (fun input => (input, observe_closed 1000 (count (Fib_L1 input)))) [0; 1; 2; 5; 10].
Eval vm_compute in
  List.map (fun input => (input, observe_closed 1000 (run_count (Fib_L2 input)))) [0; 1; 2; 5; 10].
Eval vm_compute in
  List.map (fun input => (input, observe_closed 1000 (run_count (Fib_L3 input)))) [0; 1; 2; 5; 10].
Eval vm_compute in
  List.map (fun input =>
    (input, observe_closed 1000 (run_count (Fib_L4 input))))
    [0; 1; 2; 3; 4; 5; 7; 8; 10; 15; 16; 20].
Eval vm_compute in
  List.map (fun input => (input, fib_l4_observed_cost_saving input))
    [0; 1; 2; 5; 10; 20].

(** Inspect the constructed terms. The separate assumption gate audits the
    theorems listed in checks/assumptions.txt. *)
Print Fib_L1.
Print Fib_L2.
Print Fib_L3.
Print Fib_L4.
Check Spec_L1.
Check Spec_L2.
Check Spec_L3.
Check Spec_L4.
Check fib_l4_cost_saving.
Check Fib_L4_count.
Check Fib_L4_erases.
Check Fib_L4_improves_L3.
