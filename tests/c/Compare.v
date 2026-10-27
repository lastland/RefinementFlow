(* Actual Rocq execution of the derived programs, independently of extraction
   and the Python generator.  check_c.py checks these same small known values
   against its independent exact-integer linear reference and native output. *)
From Stdlib Require Import List.
From RefineToITree Require Import FibonacciL4.
Import ListNotations.

Definition c_check_inputs : list nat := [0; 1; 2; 3; 4; 5; 7; 8; 10; 15; 16; 20].
Definition c_check_values : list nat := [0; 1; 1; 2; 3; 5; 13; 21; 55; 610; 987; 6765].

(* L1's exponential execution is intentionally limited to this known subset.
   Keep its literals independent so the runner checks both lists for drift. *)
Definition c_check_l1_inputs : list nat := [0; 1; 2; 3; 4; 5; 7; 8; 10].
Definition c_check_l1_values : list nat := [0; 1; 1; 2; 3; 5; 13; 21; 55].

(* Print the independently maintained literals so the runner detects drift.
   Separate markers let it accept ordinary pretty-printer line wrapping. *)
Goal True.
  idtac "C-CHECK INPUTS BEGIN".
  let inputs := eval vm_compute in c_check_inputs in idtac inputs.
  idtac "C-CHECK INPUTS END".
  idtac "C-CHECK VALUES BEGIN".
  let values := eval vm_compute in c_check_values in idtac values.
  idtac "C-CHECK VALUES END".
  idtac "C-CHECK L1 INPUTS BEGIN".
  let inputs := eval vm_compute in c_check_l1_inputs in idtac inputs.
  idtac "C-CHECK L1 INPUTS END".
  idtac "C-CHECK L1 VALUES BEGIN".
  let values := eval vm_compute in c_check_l1_values in idtac values.
  idtac "C-CHECK L1 VALUES END".
  exact I.
Qed.

Definition c_check_observed
    (program : nat -> itree (ArrayE nat +' TimeE) nat) input : option nat :=
  match observe_closed 1000 (run_count (program input)) with
  | Some (_, Some (_, result)) => Some result
  | _ => None
  end.

Definition c_check_l1_observed input : option nat :=
  match observe_closed 1000 (count (Fib_L1 input)) with
  | Some (_, result) => Some result
  | None => None
  end.

Example actual_l1_c_check :
  List.map c_check_l1_observed c_check_l1_inputs =
  List.map (@Some nat) c_check_l1_values.
Proof. vm_compute; reflexivity. Qed.
Goal True. idtac "C-CHECK ROCQ L1 OK". exact I. Qed.

Example actual_l2_c_check :
  List.map (c_check_observed Fib_L2) c_check_inputs =
  List.map (@Some nat) c_check_values.
Proof. vm_compute; reflexivity. Qed.
Goal True. idtac "C-CHECK ROCQ L2 OK". exact I. Qed.

Example actual_l3_c_check :
  List.map (c_check_observed Fib_L3) c_check_inputs =
  List.map (@Some nat) c_check_values.
Proof. vm_compute; reflexivity. Qed.
Goal True. idtac "C-CHECK ROCQ L3 OK". exact I. Qed.

Example actual_l4_c_check :
  List.map (c_check_observed Fib_L4) c_check_inputs =
  List.map (@Some nat) c_check_values.
Proof. vm_compute; reflexivity. Qed.
Goal True. idtac "C-CHECK ROCQ L4 OK". exact I. Qed.

(* Record the source side of the intentional unsigned-underflow mismatch. *)
Example natural_zero_minus_one : 0 - 1 = 0.
Proof. vm_compute; reflexivity. Qed.
Example charged_natural_zero_minus_one :
  c_check_observed (fun input => cost_sub 0 input) 1 = Some 0.
Proof. vm_compute; reflexivity. Qed.
