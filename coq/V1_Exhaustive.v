(** * Pruned Threshold Logic Network *)
(** Formally verified 8-bit parity network, pruned from 32->16->1 to 11->3->1. *)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(** ** Definitions *)

Definition bit := bool.
Definition weight := Z.
Definition bias := Z.

(** Heaviside activation: 1 if x >= 0, else 0. *)
Definition heaviside (x : Z) : bit :=
  if Z.geb x 0 then true else false.

(** Dot product of weights and inputs. *)
Fixpoint dot (ws : list weight) (xs : list bit) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' =>
      (if x then w else 0) + dot ws' xs'
  end.

(** Single neuron: dot product + bias, then heaviside. *)
Definition neuron (ws : list weight) (b : bias) (xs : list bit) : bit :=
  heaviside (dot ws xs + b).

(** Layer: apply list of neurons to same input. *)
Definition layer (neurons : list (list weight * bias)) (xs : list bit) : list bit :=
  map (fun wb => neuron (fst wb) (snd wb) xs) neurons.

(** Parity function: XOR of all input bits. *)
Fixpoint parity (xs : list bit) : bit :=
  match xs with
  | [] => false
  | x :: xs' => xorb x (parity xs')
  end.

(** ** Pruned Network Weights *)
(** Architecture: 8 -> 11 -> 3 -> 1 *)
(** Original: 833 parameters, Pruned: 139 parameters (83.3% reduction) *)

Definition layer1_weights : list (list weight * bias) :=
  [    ([1; -1; 1; -1; 1; 1; 1; 1], 0);
    ([-1; 1; -1; 1; 1; -1; -1; -1], 1);
    ([-1; -1; -1; -1; -1; -1; -1; 1], 2);
    ([0; 1; -1; -1; -1; 0; 1; 0], 5);
    ([1; -1; -1; 0; -1; 1; -1; 0], 7);
    ([-1; 1; -1; 1; -1; -1; -1; -1], 0);
    ([-1; 1; -1; 1; 1; -1; -1; -1], 3);
    ([1; -1; 1; -1; 1; 1; 1; 1], -2);
    ([1; 1; -1; 1; 1; 1; 1; -1], -2);
    ([-1; 1; -1; 1; 1; -1; -1; -1], 0);
    ([-1; 1; -1; 1; 1; -1; -1; -1], 2)
  ].

Definition layer2_weights : list (list weight * bias) :=
  [    ([0; 0; -1; -1; 0; 0; -1; 1; -1; 1; -1], 30);
    ([1; -1; 1; 1; -1; 1; -1; 1; 1; 1; 1], -3);
    ([1; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1], 20)
  ].

Definition output_weights : list weight * bias :=
  ([1; -1; 1], -2).

(** ** Network Definition *)

Definition network (xs : list bit) : bit :=
  let h1 := layer layer1_weights xs in
  let h2 := layer layer2_weights h1 in
  neuron (fst output_weights) (snd output_weights) h2.

(** ** Exhaustive Verification *)

Fixpoint all_inputs (n : nat) : list (list bit) :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')
  end.

Definition check_all_8bit : bool :=
  forallb (fun xs => Bool.eqb (network xs) (parity xs)) (all_inputs 8).

(** Main correctness theorem. *)
Theorem pruned_network_correct :
  check_all_8bit = true.
Proof. vm_compute. reflexivity. Qed.

(** Alternative statement: for all 8-bit inputs, network equals parity. *)
Theorem network_verified :
  forall xs, In xs (all_inputs 8) -> network xs = parity xs.
Proof.
  intros xs Hin.
  assert (H: check_all_8bit = true) by (vm_compute; reflexivity).
  unfold check_all_8bit in H.
  rewrite forallb_forall in H.
  specialize (H xs Hin).
  apply Bool.eqb_prop in H.
  exact H.
Qed.

(** ** Additional Properties *)

(** Bit-flip invariance: parity(NOT x) = parity(x) for 8-bit inputs. *)
Definition check_negb_invariance : bool :=
  forallb (fun xs => Bool.eqb (network (map negb xs)) (network xs)) (all_inputs 8).

Theorem negb_invariance :
  check_negb_invariance = true.
Proof. vm_compute. reflexivity. Qed.
