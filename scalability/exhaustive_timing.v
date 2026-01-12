(** Exhaustive timing test - see how vm_compute scales with 2^n *)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition bit := bool.
Definition heaviside (x : Z) : bit := Z.geb x 0.

Fixpoint dot (ws : list Z) (xs : list bit) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' => (if x then w else 0) + dot ws' xs'
  end.

Definition neuron (ws : list Z) (b : Z) (xs : list bit) : bit :=
  heaviside (dot ws xs + b).

Fixpoint ones (n : nat) : list Z :=
  match n with O => [] | S n' => 1 :: ones n' end.

Fixpoint alt_weights (n : nat) (sign : bool) : list Z :=
  match n with
  | O => []
  | S n' => (if sign then 1 else -1) :: alt_weights n' (negb sign)
  end.

Definition L1_output (n : nat) (xs : list bit) : list bit :=
  map (fun k => neuron (ones n) (- Z.of_nat k) xs) (seq 0 (S n)).

Definition parity_network (n : nat) (xs : list bit) : bit :=
  neuron [-1] 0 [neuron (alt_weights (S n) true) (-1) (L1_output n xs)].

Fixpoint parity (xs : list bit) : bit :=
  match xs with [] => false | x :: xs' => xorb x (parity xs') end.

Fixpoint all_inputs (n : nat) : list (list bit) :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')
  end.

Definition check (n : nat) : bool :=
  forallb (fun xs => Bool.eqb (parity_network n xs) (parity xs)) (all_inputs n).

(** n=8: 256 inputs *)
Lemma ex8 : check 8 = true. Proof. vm_compute. reflexivity. Qed.

(** n=10: 1024 inputs *)
Lemma ex10 : check 10 = true. Proof. vm_compute. reflexivity. Qed.

(** n=12: 4096 inputs - expect ~4x slower than n=10 *)
Lemma ex12 : check 12 = true. Proof. vm_compute. reflexivity. Qed.

(** n=14: 16384 inputs *)
Lemma ex14 : check 14 = true. Proof. vm_compute. reflexivity. Qed.

(** n=16: 65536 inputs *)
Lemma ex16 : check 16 = true. Proof. vm_compute. reflexivity. Qed.

(** n=18: 262144 inputs *)
Lemma ex18 : check 18 = true. Proof. vm_compute. reflexivity. Qed.

(** n=20: 1048576 inputs - ~1 million *)
Lemma ex20 : check 20 = true. Proof. vm_compute. reflexivity. Qed.

(** n=22: 4194304 inputs - ~4 million *)
Lemma ex22 : check 22 = true. Proof. vm_compute. reflexivity. Qed.

(** n=24: 16777216 inputs - ~16 million *)
Lemma ex24 : check 24 = true. Proof. vm_compute. reflexivity. Qed.
