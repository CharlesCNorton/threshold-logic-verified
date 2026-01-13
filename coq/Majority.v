(** * Majority Function: Depth-1 Sufficiency *)

(**
   This file proves that the majority function can be computed by a
   single threshold gate (depth-1), in contrast to parity which requires
   depth-2.

   MAIN RESULTS:
   1. majority_depth1: A single gate computes n-bit majority
   2. majority_parity_contrast: Majority is depth-1, parity needs depth-2

   This demonstrates that parity's depth requirement is not shared by
   all symmetric Boolean functions.
*)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

(** * Definitions *)

Definition bit := bool.
Definition input := list bit.

Fixpoint hamming_weight (xs : input) : nat :=
  match xs with
  | [] => 0
  | true :: xs' => S (hamming_weight xs')
  | false :: xs' => hamming_weight xs'
  end.

Fixpoint parity (xs : input) : bit :=
  match xs with
  | [] => false
  | x :: xs' => xorb x (parity xs')
  end.

(** Majority: output 1 if more than half the inputs are 1 *)
Definition majority (xs : input) : bit :=
  (length xs / 2 <? hamming_weight xs)%nat.

(** Strict majority: output 1 if at least half the inputs are 1 *)
Definition majority_geq (xs : input) : bit :=
  (length xs / 2 <=? hamming_weight xs)%nat.

Fixpoint dot (ws : list Z) (xs : input) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' => (if x then w else 0) + dot ws' xs'
  end.

Definition gate (ws : list Z) (b : Z) (xs : input) : bit :=
  Z.geb (dot ws xs + b) 0.

(** * All-Ones Weights *)

Fixpoint ones (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => 1 :: ones n'
  end.

Lemma ones_length : forall n, length (ones n) = n.
Proof. induction n; simpl; auto. Qed.

Lemma dot_ones_eq_hw : forall xs,
  dot (ones (length xs)) xs = Z.of_nat (hamming_weight xs).
Proof.
  induction xs as [| x xs' IH]; simpl.
  - reflexivity.
  - destruct x; simpl; rewrite IH.
    + change (1 + Z.of_nat (hamming_weight xs') = Z.of_nat (S (hamming_weight xs'))).
      lia.
    + reflexivity.
Qed.

(** * Gate Lemmas *)

Lemma gate_fires_iff : forall ws b xs,
  gate ws b xs = true <-> dot ws xs + b >= 0.
Proof.
  intros. unfold gate. rewrite Z.geb_leb.
  split; intro H.
  - apply Z.leb_le in H. lia.
  - apply Z.leb_le. lia.
Qed.

Lemma gate_silent_iff : forall ws b xs,
  gate ws b xs = false <-> dot ws xs + b < 0.
Proof.
  intros. unfold gate. rewrite Z.geb_leb.
  split; intro H.
  - apply Z.leb_gt in H. lia.
  - apply Z.leb_gt. lia.
Qed.

(** * Majority Gate *)

(**
   The majority gate uses:
   - Weights: all ones [1, 1, ..., 1]
   - Bias: -(n/2 + 1) for strict majority (> half)
   - Bias: -(n/2) for weak majority (>= half when n even)

   Pre-activation = HW(x) - (n/2 + 1)
   Fires iff HW(x) >= n/2 + 1, i.e., HW(x) > n/2
*)

Definition majority_bias (n : nat) : Z := - Z.of_nat (n / 2 + 1).

Definition majority_gate (xs : input) : bit :=
  gate (ones (length xs)) (majority_bias (length xs)) xs.

(** The gate fires iff HW > n/2 *)
Lemma majority_gate_fires_iff : forall xs,
  majority_gate xs = true <-> (length xs / 2 < hamming_weight xs)%nat.
Proof.
  intros xs.
  unfold majority_gate, majority_bias.
  rewrite gate_fires_iff.
  rewrite dot_ones_eq_hw.
  split; intro H.
  - lia.
  - lia.
Qed.

Lemma majority_gate_silent_iff : forall xs,
  majority_gate xs = false <-> (hamming_weight xs <= length xs / 2)%nat.
Proof.
  intros xs.
  unfold majority_gate, majority_bias.
  rewrite gate_silent_iff.
  rewrite dot_ones_eq_hw.
  split; intro H.
  - lia.
  - lia.
Qed.

(** *** MAIN THEOREM: Majority is computable by depth-1 *)
Theorem majority_depth1 : forall xs,
  majority_gate xs = majority xs.
Proof.
  intros xs.
  unfold majority.
  destruct (length xs / 2 <? hamming_weight xs)%nat eqn:Hcmp.
  - apply Nat.ltb_lt in Hcmp.
    apply majority_gate_fires_iff. exact Hcmp.
  - apply Nat.ltb_ge in Hcmp.
    apply majority_gate_silent_iff. exact Hcmp.
Qed.

(** * Weak Majority (>= half) *)

Definition weak_majority_bias (n : nat) : Z := - Z.of_nat ((n + 1) / 2).

Definition weak_majority_gate (xs : input) : bit :=
  gate (ones (length xs)) (weak_majority_bias (length xs)) xs.

Lemma weak_majority_gate_fires_iff : forall xs,
  weak_majority_gate xs = true <-> ((length xs + 1) / 2 <= hamming_weight xs)%nat.
Proof.
  intros xs.
  unfold weak_majority_gate, weak_majority_bias.
  rewrite gate_fires_iff.
  rewrite dot_ones_eq_hw.
  split; intro H; lia.
Qed.

(** * Contrast with Parity *)

(** Import the depth-1 impossibility for parity *)
Lemma parity_needs_depth2 : forall n, (n >= 2)%nat ->
  forall ws b,
  length ws = n ->
  ~ (forall xs, length xs = n -> gate ws b xs = parity xs).
Proof.
  intros n Hn ws b Hlen Hgate.
  destruct ws as [| w0 ws']; [simpl in Hlen; lia |].
  destruct ws' as [| w1 ws'']; [simpl in Hlen; lia |].
  set (x00 := [false; false] ++ repeat false (n - 2)).
  set (x01 := [false; true] ++ repeat false (n - 2)).
  set (x10 := [true; false] ++ repeat false (n - 2)).
  set (x11 := [true; true] ++ repeat false (n - 2)).
  assert (Hlen00 : length x00 = n).
  { unfold x00. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hlen01 : length x01 = n).
  { unfold x01. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hlen10 : length x10 = n).
  { unfold x10. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hlen11 : length x11 = n).
  { unfold x11. rewrite app_length, repeat_length. simpl. lia. }
  pose proof (Hgate x00 Hlen00) as H00.
  pose proof (Hgate x01 Hlen01) as H01.
  pose proof (Hgate x10 Hlen10) as H10.
  pose proof (Hgate x11 Hlen11) as H11.
  assert (Hpar_repeat : forall k, parity (repeat false k) = false).
  { clear. induction k; simpl; auto. }
  assert (Hpar_app : forall xs ys, parity (xs ++ ys) = xorb (parity xs) (parity ys)).
  { clear. induction xs; intros ys; simpl.
    - reflexivity.
    - rewrite IHxs. destruct a, (parity xs), (parity ys); reflexivity. }
  assert (Hpar00 : parity x00 = false).
  { unfold x00. rewrite Hpar_app, Hpar_repeat. reflexivity. }
  assert (Hpar01 : parity x01 = true).
  { unfold x01. rewrite Hpar_app, Hpar_repeat. reflexivity. }
  assert (Hpar10 : parity x10 = true).
  { unfold x10. rewrite Hpar_app, Hpar_repeat. reflexivity. }
  assert (Hpar11 : parity x11 = false).
  { unfold x11. rewrite Hpar_app, Hpar_repeat. reflexivity. }
  rewrite Hpar00 in H00.
  rewrite Hpar01 in H01.
  rewrite Hpar10 in H10.
  rewrite Hpar11 in H11.
  rewrite gate_silent_iff in H00.
  rewrite gate_fires_iff in H01.
  rewrite gate_fires_iff in H10.
  rewrite gate_silent_iff in H11.
  assert (Hdot_repeat : forall ws k, dot ws (repeat false k) = 0).
  { clear. intros ws k. revert ws.
    induction k as [| k' IH]; intros ws.
    - destruct ws; reflexivity.
    - destruct ws as [| w ws']; [reflexivity |].
      simpl. rewrite IH. lia. }
  assert (Hdot00 : dot (w0 :: w1 :: ws'') x00 = 0).
  { unfold x00. simpl. rewrite Hdot_repeat. lia. }
  assert (Hdot01 : dot (w0 :: w1 :: ws'') x01 = w1).
  { unfold x01. simpl. rewrite Hdot_repeat. lia. }
  assert (Hdot10 : dot (w0 :: w1 :: ws'') x10 = w0).
  { unfold x10. simpl. rewrite Hdot_repeat. lia. }
  assert (Hdot11 : dot (w0 :: w1 :: ws'') x11 = w0 + w1).
  { unfold x11. simpl. rewrite Hdot_repeat. lia. }
  rewrite Hdot00 in H00.
  rewrite Hdot01 in H01.
  rewrite Hdot10 in H10.
  rewrite Hdot11 in H11.
  lia.
Qed.

(** *** CONTRAST THEOREM: Majority vs Parity *)
Theorem majority_parity_contrast : forall n, (n >= 2)%nat ->
  (exists ws b, length ws = n /\ forall xs, length xs = n -> gate ws b xs = majority xs)
  /\
  (forall ws b, length ws = n -> ~ (forall xs, length xs = n -> gate ws b xs = parity xs)).
Proof.
  intros n Hn.
  split.
  - exists (ones n), (majority_bias n).
    split.
    + apply ones_length.
    + intros xs Hxs.
      rewrite <- Hxs.
      apply majority_depth1.
  - exact (parity_needs_depth2 n Hn).
Qed.

(** * Exhaustive Verification for Small n *)

Fixpoint all_inputs (n : nat) : list input :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')
  end.

Definition check_majority (n : nat) : bool :=
  forallb (fun xs => Bool.eqb (majority_gate xs) (majority xs)) (all_inputs n).

Lemma majority_exhaustive_4 : check_majority 4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma majority_exhaustive_8 : check_majority 8 = true.
Proof. vm_compute. reflexivity. Qed.

(** * Concrete Examples *)

Example majority_0000 : majority [false; false; false; false] = false.
Proof. reflexivity. Qed.

Example majority_0001 : majority [false; false; false; true] = false.
Proof. reflexivity. Qed.

Example majority_0011 : majority [false; false; true; true] = false.
Proof. reflexivity. Qed.

Example majority_0111 : majority [false; true; true; true] = true.
Proof. reflexivity. Qed.

Example majority_1111 : majority [true; true; true; true] = true.
Proof. reflexivity. Qed.

Example majority_gate_0000 : majority_gate [false; false; false; false] = false.
Proof. reflexivity. Qed.

Example majority_gate_0111 : majority_gate [false; true; true; true] = true.
Proof. reflexivity. Qed.

(** * Summary *)

(**
   WHAT WE PROVED:
   - majority_depth1: Majority is computable by a single threshold gate
   - majority_parity_contrast: Majority needs depth-1, parity needs depth-2

   WHY MAJORITY IS EASY:
   - Majority is a LINEAR threshold function
   - The decision boundary is a hyperplane: HW(x) = n/2
   - A single gate can implement any hyperplane separator

   WHY PARITY IS HARD:
   - Parity is a NONLINEAR function (XOR of all bits)
   - No hyperplane separates odd-parity from even-parity inputs
   - The parity classes are "interleaved" in Hamming space

   GEOMETRIC INTUITION:
   - Majority separates inputs by Hamming weight (above/below n/2)
   - Parity separates inputs by Hamming weight PARITY (odd/even)
   - Odd/even classes alternate: 0,2,4,... vs 1,3,5,...
   - No single cut can separate alternating classes
*)

Close Scope Z_scope.
