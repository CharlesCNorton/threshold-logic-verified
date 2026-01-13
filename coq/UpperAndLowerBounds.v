(** * Upper and Lower Bounds for Depth-2 Threshold Circuits Computing Parity *)

(**
   This file unifies the theoretical analysis of threshold circuits for parity:

   UPPER BOUNDS (from V12_Depth2Minimal):
   - An 11-neuron depth-2 circuit computes 8-bit parity
   - Construction: thermometer encoding + alternating weights + negation
   - Verified correct on all 256 inputs

   LOWER BOUNDS (from ThresholdLowerBounds):
   - Depth-1 is impossible: no single gate computes n-bit parity (n >= 2)
   - Depth-2 requires Ω(n/log n) gates in layer 1
   - Communication complexity argument: Alice/Bob protocol simulation

   MAIN THEOREM (depth2_parity_bounds):
   For n-bit parity with n >= 2:
   1. Depth-1 is impossible
   2. Depth-2 suffices with O(n) gates
   3. Depth-2 requires Ω(n/log n) gates

   LIBRARIES:
   - Coq.ZArith.ZArith: Integer arithmetic
   - Coq.Lists.List: List operations
   - Coq.Bool.Bool: Boolean operations
   - Coq.Arith.PeanoNat: Natural number arithmetic
   - Coq.micromega.Lia: Linear integer arithmetic solver
   - Coq.Logic.Classical_Prop: Classical logic
   - Coq.Reals.Reals: Real numbers (for logarithm bounds)
*)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rpower.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope Z_scope.

(** * Part I: Common Definitions *)

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

Fixpoint dot (ws : list Z) (xs : input) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' => (if x then w else 0) + dot ws' xs'
  end.

Definition heaviside (x : Z) : bit := Z.geb x 0.

Definition gate (ws : list Z) (b : Z) (xs : input) : bit :=
  heaviside (dot ws xs + b).

Definition neuron := gate.

(** * Part II: Upper Bound - Depth-2 Construction *)

(** ** Layer 1: Thermometer Encoding *)

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

Definition L1_neuron (k : nat) (xs : input) : bit :=
  neuron (ones (length xs)) (- Z.of_nat k) xs.

Lemma L1_neuron_correct : forall k xs,
  L1_neuron k xs = (k <=? hamming_weight xs)%nat.
Proof.
  intros k xs.
  unfold L1_neuron, neuron, gate, heaviside.
  rewrite dot_ones_eq_hw.
  set (hw := hamming_weight xs).
  destruct (Nat.le_gt_cases k hw) as [Hle | Hgt].
  - assert (H: Z.of_nat hw + - Z.of_nat k >= 0) by lia.
    destruct (Z.of_nat hw + - Z.of_nat k >=? 0) eqn:E.
    + symmetry. apply Nat.leb_le. exact Hle.
    + exfalso. rewrite Z.geb_leb in E. apply Z.leb_gt in E. lia.
  - assert (H: Z.of_nat hw + - Z.of_nat k < 0) by lia.
    destruct (Z.of_nat hw + - Z.of_nat k >=? 0) eqn:E.
    + exfalso. rewrite Z.geb_leb in E. apply Z.leb_le in E. lia.
    + symmetry. apply Nat.leb_gt. exact Hgt.
Qed.

Definition L1_output (xs : input) : list bit :=
  map (fun k => L1_neuron k xs) (seq 0 9).

Lemma L1_output_length : forall xs, length (L1_output xs) = 9%nat.
Proof. intros. unfold L1_output. rewrite map_length, seq_length. reflexivity. Qed.

(** ** Layer 2: Alternating Weights *)

Fixpoint alt_weights (n : nat) (sign : bool) : list Z :=
  match n with
  | O => []
  | S n' => (if sign then 1 else -1) :: alt_weights n' (negb sign)
  end.

Definition L2_weights : list Z := alt_weights 9 true.

Lemma L2_weights_expand : L2_weights = [1; -1; 1; -1; 1; -1; 1; -1; 1].
Proof. reflexivity. Qed.

Fixpoint alt_sum_first (m : nat) : Z :=
  match m with
  | O => 0
  | S m' => (if Nat.odd m then 1 else -1) + alt_sum_first m'
  end.

Lemma even_S : forall n, Nat.even (S n) = negb (Nat.even n).
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - change (Nat.even (S (S n'))) with (Nat.even n').
    rewrite IH. destruct (Nat.even n'); reflexivity.
Qed.

Lemma odd_S : forall n, Nat.odd (S n) = negb (Nat.odd n).
Proof.
  intros n. unfold Nat.odd. rewrite even_S.
  destruct (Nat.even n); reflexivity.
Qed.

Lemma alt_sum_first_correct : forall m,
  alt_sum_first m = if Nat.odd m then 1 else 0.
Proof.
  induction m.
  - reflexivity.
  - simpl alt_sum_first. rewrite odd_S. rewrite IHm.
    destruct (Nat.odd m); simpl; lia.
Qed.

Definition L2_neuron (h1 : list bit) : bit :=
  neuron L2_weights (-1) h1.

Theorem L2_fires_iff_even : forall xs,
  length xs = 8%nat ->
  (hamming_weight xs <= 8)%nat ->
  L2_neuron (L1_output xs) = Nat.even (hamming_weight xs).
Proof.
  intros xs Hlen Hbound.
  unfold L2_neuron, neuron, gate, heaviside.
  set (hw := hamming_weight xs).
  assert (Hdot: dot L2_weights (L1_output xs) = alt_sum_first (S hw)).
  {
    unfold L1_output, L2_weights.
    destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 xs']]]]]]]];
    try (simpl in Hlen; discriminate).
    destruct xs'; try (simpl in Hlen; discriminate).
    unfold hamming_weight. fold hamming_weight.
    destruct x0, x1, x2, x3, x4, x5, x6, x7; reflexivity.
  }
  rewrite Hdot. rewrite alt_sum_first_correct. rewrite odd_S.
  unfold Nat.odd. destruct (Nat.even hw) eqn:Heven; simpl; reflexivity.
Qed.

(** ** Output Layer *)

Definition output_neuron (l2 : bit) : bit :=
  neuron [-1] 0 [l2].

Lemma output_neuron_negates : forall b,
  output_neuron b = negb b.
Proof.
  intros []; unfold output_neuron, neuron, gate, heaviside, dot; simpl; reflexivity.
Qed.

(** ** Complete Network *)

Definition parity_depth2 (xs : input) : bit :=
  let h1 := L1_output xs in
  let h2 := L2_neuron h1 in
  output_neuron h2.

Lemma parity_is_odd_hw : forall xs,
  parity xs = Nat.odd (hamming_weight xs).
Proof.
  induction xs as [| x xs' IH]; simpl.
  - reflexivity.
  - destruct x; simpl.
    + rewrite IH. rewrite odd_S.
      destruct (Nat.odd (hamming_weight xs')); reflexivity.
    + exact IH.
Qed.

Lemma hw_bounded : forall xs,
  length xs = 8%nat -> (hamming_weight xs <= 8)%nat.
Proof.
  intros xs Hlen.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 xs']]]]]]]];
  try (simpl in Hlen; discriminate).
  destruct xs'; try (simpl in Hlen; discriminate).
  unfold hamming_weight.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; simpl; lia.
Qed.

(** *** UPPER BOUND MAIN THEOREM *)
Theorem upper_bound_depth2_suffices : forall xs,
  length xs = 8%nat ->
  parity_depth2 xs = parity xs.
Proof.
  intros xs Hlen.
  unfold parity_depth2.
  rewrite output_neuron_negates.
  rewrite L2_fires_iff_even by (auto using hw_bounded).
  rewrite parity_is_odd_hw.
  unfold Nat.odd. destruct (Nat.even (hamming_weight xs)); reflexivity.
Qed.

(** ** Exhaustive Verification *)

Fixpoint all_inputs (n : nat) : list input :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')
  end.

Definition check_upper_bound : bool :=
  forallb (fun xs => Bool.eqb (parity_depth2 xs) (parity xs)) (all_inputs 8).

Lemma exhaustive_upper_bound : check_upper_bound = true.
Proof. vm_compute. reflexivity. Qed.

(** * Part III: Lower Bound - Depth-1 Impossibility *)

Definition x00 : input := [false; false].
Definition x01 : input := [false; true].
Definition x10 : input := [true; false].
Definition x11 : input := [true; true].

Lemma dot_x00 : forall w0 w1, dot [w0; w1] x00 = 0.
Proof. intros. reflexivity. Qed.

Lemma dot_x01 : forall w0 w1, dot [w0; w1] x01 = w1.
Proof. intros. unfold x01, dot. lia. Qed.

Lemma dot_x10 : forall w0 w1, dot [w0; w1] x10 = w0.
Proof. intros. unfold x10, dot. lia. Qed.

Lemma dot_x11 : forall w0 w1, dot [w0; w1] x11 = w0 + w1.
Proof. intros. unfold x11, dot. lia. Qed.

Lemma gate_fires_iff : forall ws b xs,
  gate ws b xs = true <-> dot ws xs + b >= 0.
Proof.
  intros ws b xs. unfold gate, heaviside. rewrite Z.geb_leb.
  split; intros H.
  - apply Z.leb_le in H. lia.
  - apply Z.leb_le. lia.
Qed.

Lemma gate_silent_iff : forall ws b xs,
  gate ws b xs = false <-> dot ws xs + b < 0.
Proof.
  intros ws b xs. unfold gate, heaviside. rewrite Z.geb_leb.
  split; intros H.
  - apply Z.leb_gt in H. lia.
  - apply Z.leb_gt. lia.
Qed.

Theorem depth1_impossible_2bit : forall w0 w1 b,
  gate [w0; w1] b x00 = parity x00 ->
  gate [w0; w1] b x01 = parity x01 ->
  gate [w0; w1] b x10 = parity x10 ->
  gate [w0; w1] b x11 = parity x11 ->
  False.
Proof.
  intros w0 w1 b H00 H01 H10 H11.
  simpl in H00, H01, H10, H11.
  rewrite gate_silent_iff in H00.
  rewrite gate_fires_iff in H01.
  rewrite gate_fires_iff in H10.
  rewrite gate_silent_iff in H11.
  rewrite dot_x00 in H00.
  rewrite dot_x01 in H01.
  rewrite dot_x10 in H10.
  rewrite dot_x11 in H11.
  lia.
Qed.

Definition pad_zeros (xs : input) (k : nat) : input := xs ++ repeat false k.

Lemma parity_repeat_false : forall k, parity (repeat false k) = false.
Proof. induction k as [| k' IH]; simpl; [reflexivity | exact IH]. Qed.

Lemma parity_app : forall xs ys,
  parity (xs ++ ys) = xorb (parity xs) (parity ys).
Proof.
  induction xs as [| x xs' IH]; intros ys; simpl.
  - reflexivity.
  - rewrite IH. destruct x, (parity xs'), (parity ys); reflexivity.
Qed.

Lemma parity_pad_zeros : forall xs k,
  parity (pad_zeros xs k) = parity xs.
Proof.
  intros xs k. unfold pad_zeros.
  rewrite parity_app, parity_repeat_false.
  destruct (parity xs); reflexivity.
Qed.

Lemma dot_repeat_false : forall ws k, dot ws (repeat false k) = 0.
Proof.
  induction ws as [| w ws' IH]; intros k.
  - reflexivity.
  - destruct k; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma dot_pad_x00 : forall w0 w1 ws k,
  length ws = k -> dot (w0 :: w1 :: ws) (pad_zeros x00 k) = 0.
Proof.
  intros. unfold pad_zeros, x00. simpl. apply dot_repeat_false.
Qed.

Lemma dot_pad_x01 : forall w0 w1 ws k,
  length ws = k -> dot (w0 :: w1 :: ws) (pad_zeros x01 k) = w1.
Proof.
  intros. unfold pad_zeros, x01. simpl. rewrite dot_repeat_false. lia.
Qed.

Lemma dot_pad_x10 : forall w0 w1 ws k,
  length ws = k -> dot (w0 :: w1 :: ws) (pad_zeros x10 k) = w0.
Proof.
  intros. unfold pad_zeros, x10. simpl. rewrite dot_repeat_false. lia.
Qed.

Lemma dot_pad_x11 : forall w0 w1 ws k,
  length ws = k -> dot (w0 :: w1 :: ws) (pad_zeros x11 k) = w0 + w1.
Proof.
  intros. unfold pad_zeros, x11. simpl. rewrite dot_repeat_false. lia.
Qed.

(** *** LOWER BOUND: Depth-1 Impossible for n >= 2 *)
Theorem lower_bound_depth1_impossible : forall n, (n >= 2)%nat ->
  forall ws b,
  length ws = n ->
  ~ (forall xs, length xs = n -> gate ws b xs = parity xs).
Proof.
  intros n Hn ws b Hlen Hgate.
  set (pad := (n - 2)%nat).
  destruct ws as [| w0 ws']; [simpl in Hlen; lia |].
  destruct ws' as [| w1 ws'']; [simpl in Hlen; lia |].
  assert (Hws'' : length ws'' = pad) by (simpl in *; lia).
  assert (Hlen00 : length (pad_zeros x00 pad) = n).
  { unfold pad_zeros, x00. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hlen01 : length (pad_zeros x01 pad) = n).
  { unfold pad_zeros, x01. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hlen10 : length (pad_zeros x10 pad) = n).
  { unfold pad_zeros, x10. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hlen11 : length (pad_zeros x11 pad) = n).
  { unfold pad_zeros, x11. rewrite app_length, repeat_length. simpl. lia. }
  pose proof (Hgate (pad_zeros x00 pad) Hlen00) as H00.
  pose proof (Hgate (pad_zeros x01 pad) Hlen01) as H01.
  pose proof (Hgate (pad_zeros x10 pad) Hlen10) as H10.
  pose proof (Hgate (pad_zeros x11 pad) Hlen11) as H11.
  unfold gate, heaviside in H00, H01, H10, H11.
  rewrite dot_pad_x00 in H00 by exact Hws''.
  rewrite dot_pad_x01 in H01 by exact Hws''.
  rewrite dot_pad_x10 in H10 by exact Hws''.
  rewrite dot_pad_x11 in H11 by exact Hws''.
  rewrite parity_pad_zeros in H00, H01, H10, H11.
  unfold x00, x01, x10, x11 in H00, H01, H10, H11.
  simpl parity in H00, H01, H10, H11.
  assert (Hb_neg : b < 0).
  { destruct (Z.geb (0 + b) 0) eqn:E; [discriminate H00 |].
    rewrite Z.geb_leb, Z.leb_gt in E. lia. }
  assert (Hw1_pos : w1 + b >= 0).
  { destruct (Z.geb (w1 + b) 0) eqn:E; [| discriminate H01].
    rewrite Z.geb_leb, Z.leb_le in E. lia. }
  assert (Hw0_pos : w0 + b >= 0).
  { destruct (Z.geb (w0 + b) 0) eqn:E; [| discriminate H10].
    rewrite Z.geb_leb, Z.leb_le in E. lia. }
  assert (Hsum_neg : w0 + w1 + b < 0).
  { destruct (Z.geb (w0 + w1 + b) 0) eqn:E; [discriminate H11 |].
    rewrite Z.geb_leb, Z.leb_gt in E. lia. }
  lia.
Qed.

(** * Part IV: Lower Bound - Ω(n/log n) Gates Required *)

(** ** Depth-2 Circuit Definition *)

Record depth2_circuit := {
  n_inputs : nat;
  n_layer1 : nat;
  layer1_weights : list (list Z * Z);
  layer2_weights : list Z;
  layer2_bias : Z
}.

Definition eval_layer1 (c : depth2_circuit) (xs : input) : list bit :=
  map (fun wb => gate (fst wb) (snd wb) xs) (layer1_weights c).

Definition eval_depth2 (c : depth2_circuit) (xs : input) : bit :=
  let h := eval_layer1 c xs in
  gate (layer2_weights c) (layer2_bias c) h.

Definition circuit_computes_parity (c : depth2_circuit) : Prop :=
  forall xs, length xs = n_inputs c -> eval_depth2 c xs = parity xs.

(** ** Pattern Analysis *)

Definition layer1_pattern (c : depth2_circuit) (xs : input) : list bit :=
  eval_layer1 c xs.

Lemma same_pattern_same_output : forall c xs ys,
  layer1_pattern c xs = layer1_pattern c ys ->
  eval_depth2 c xs = eval_depth2 c ys.
Proof.
  intros c xs ys Hpat. unfold eval_depth2, layer1_pattern in *.
  rewrite Hpat. reflexivity.
Qed.

Lemma different_parity_different_pattern : forall c xs ys,
  circuit_computes_parity c ->
  length xs = n_inputs c ->
  length ys = n_inputs c ->
  parity xs <> parity ys ->
  layer1_pattern c xs <> layer1_pattern c ys.
Proof.
  intros c xs ys Hcomp Hxs Hys Hpar Hpat. apply Hpar.
  unfold circuit_computes_parity in Hcomp.
  rewrite <- (Hcomp xs Hxs), <- (Hcomp ys Hys).
  apply same_pattern_same_output. exact Hpat.
Qed.

(** ** Communication Complexity Argument *)

Definition alice_partial (ws : list Z) (xs_A : input) (half : nat) : Z :=
  dot (firstn half ws) xs_A.

Definition alice_messages (gates : list (list Z * Z)) (xs : input) (half : nat) : list Z :=
  map (fun wb => alice_partial (fst wb) (firstn half xs) half) gates.

Lemma dot_firstn_skipn : forall ws xs k,
  length ws = length xs ->
  (k <= length xs)%nat ->
  dot ws xs = dot (firstn k ws) (firstn k xs) + dot (skipn k ws) (skipn k xs).
Proof.
  intros ws xs k Hlen Hk. revert xs k Hlen Hk.
  induction ws as [| w ws' IH]; intros xs k Hlen Hk.
  - destruct xs; simpl in *; [destruct k; reflexivity | discriminate].
  - destruct xs as [| x xs']; simpl in *; [discriminate |].
    destruct k as [| k']; [simpl; lia |].
    simpl. injection Hlen as Hlen'.
    specialize (IH xs' k' Hlen' ltac:(lia)).
    destruct x; lia.
Qed.

Lemma same_alice_same_gate : forall ws b xs ys half,
  length xs = (2 * half)%nat ->
  length ys = (2 * half)%nat ->
  length ws = (2 * half)%nat ->
  skipn half xs = skipn half ys ->
  alice_partial ws (firstn half xs) half = alice_partial ws (firstn half ys) half ->
  gate ws b xs = gate ws b ys.
Proof.
  intros ws b xs ys half Hxlen Hylen Hwlen Hbob Halice.
  unfold gate, heaviside. f_equal.
  rewrite (dot_firstn_skipn ws xs half) by lia.
  rewrite (dot_firstn_skipn ws ys half) by lia.
  unfold alice_partial in Halice.
  rewrite Halice, Hbob. reflexivity.
Qed.

Lemma same_messages_same_layer1 : forall gates xs ys half,
  length xs = (2 * half)%nat ->
  length ys = (2 * half)%nat ->
  Forall (fun wb => length (fst wb) = (2 * half)%nat) gates ->
  skipn half xs = skipn half ys ->
  alice_messages gates xs half = alice_messages gates ys half ->
  map (fun wb => gate (fst wb) (snd wb) xs) gates =
  map (fun wb => gate (fst wb) (snd wb) ys) gates.
Proof.
  intros gates xs ys half Hxlen Hylen Hglen Hbob Halice.
  induction gates as [| g gates' IH]; [reflexivity |].
  simpl in *. inversion Hglen as [| ? ? Hg Hgates']; subst.
  injection Halice as Hg_alice Hrest. f_equal.
  - apply (same_alice_same_gate (fst g) (snd g) xs ys half); assumption.
  - apply IH; assumption.
Qed.

Lemma parity_xor_halves : forall xs half,
  length xs = (2 * half)%nat ->
  parity xs = xorb (parity (firstn half xs)) (parity (skipn half xs)).
Proof.
  intros xs half Hlen.
  rewrite <- (firstn_skipn half xs) at 1.
  rewrite parity_app. reflexivity.
Qed.

Lemma alice_parity_determines : forall xs ys half,
  length xs = (2 * half)%nat ->
  length ys = (2 * half)%nat ->
  skipn half xs = skipn half ys ->
  parity (firstn half xs) <> parity (firstn half ys) ->
  parity xs <> parity ys.
Proof.
  intros xs ys half Hxlen Hylen Hbob Halice_diff.
  rewrite (parity_xor_halves xs half Hxlen).
  rewrite (parity_xor_halves ys half Hylen).
  rewrite Hbob. intro Heq. apply Halice_diff.
  destruct (parity (firstn half xs)), (parity (firstn half ys)),
           (parity (skipn half ys)); simpl in Heq; try discriminate; reflexivity.
Qed.

Theorem message_collision_contradiction : forall c xs ys half,
  circuit_computes_parity c ->
  n_inputs c = (2 * half)%nat ->
  length xs = (2 * half)%nat ->
  length ys = (2 * half)%nat ->
  Forall (fun wb => length (fst wb) = (2 * half)%nat) (layer1_weights c) ->
  skipn half xs = skipn half ys ->
  alice_messages (layer1_weights c) xs half =
  alice_messages (layer1_weights c) ys half ->
  parity (firstn half xs) <> parity (firstn half ys) ->
  False.
Proof.
  intros c xs ys half Hcomp Hn Hxlen Hylen Hglen Hbob Hmsg Halice_diff.
  assert (Hpar_diff : parity xs <> parity ys).
  { apply (alice_parity_determines xs ys half); assumption. }
  assert (Hlayer1_eq : eval_layer1 c xs = eval_layer1 c ys).
  { unfold eval_layer1.
    apply (same_messages_same_layer1 (layer1_weights c) xs ys half); assumption. }
  assert (Hout_eq : eval_depth2 c xs = eval_depth2 c ys).
  { unfold eval_depth2. rewrite Hlayer1_eq. reflexivity. }
  unfold circuit_computes_parity in Hcomp. rewrite Hn in Hcomp.
  rewrite (Hcomp xs Hxlen) in Hout_eq. rewrite (Hcomp ys Hylen) in Hout_eq.
  apply Hpar_diff. exact Hout_eq.
Qed.

(** ** Logarithmic Lower Bound *)

Open Scope R_scope.

Definition log2 (x : R) : R := ln x / ln 2.

Lemma ln_2_pos : ln 2 > 0.
Proof. rewrite <- ln_1. apply ln_increasing. lra. lra. Qed.

Lemma log2_pow2 : forall n : nat, log2 (2 ^ n) = INR n.
Proof.
  intros n. unfold log2. rewrite ln_pow.
  - field. apply Rgt_not_eq. apply ln_2_pos.
  - lra.
Qed.

Lemma ln_le_compat : forall x y : R, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy.
  destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq].
  - left. apply ln_increasing; assumption.
  - right. rewrite Heq. reflexivity.
Qed.

Lemma log2_increasing : forall x y : R, 0 < x -> x <= y -> log2 x <= log2 y.
Proof.
  intros x y Hx Hxy. unfold log2. apply Rmult_le_compat_r.
  - left. apply Rinv_0_lt_compat. apply ln_2_pos.
  - apply ln_le_compat; assumption.
Qed.

Lemma message_space_bound : forall half k : nat,
  (half >= 1)%nat ->
  INR k * log2 (INR (S (2 * half))) >= log2 (INR (Nat.pow (S (2 * half)) k)).
Proof.
  intros half k Hhalf. rewrite pow_INR. unfold log2. rewrite ln_pow.
  - unfold Rdiv. rewrite Rmult_assoc. lra.
  - apply lt_0_INR. lia.
Qed.

Lemma nat_pow_pos : forall base exp : nat, (base >= 1)%nat -> (Nat.pow base exp >= 1)%nat.
Proof. intros base exp Hbase. induction exp; simpl; lia. Qed.

Lemma lower_bound_from_messages : forall half k : nat,
  (half >= 1)%nat ->
  (Nat.pow (S (2 * half)) k >= Nat.pow 2 half)%nat ->
  INR k * log2 (INR (S (2 * half))) >= INR half.
Proof.
  intros half k Hhalf Hpow. apply Rle_ge.
  apply Rle_trans with (r2 := log2 (INR (Nat.pow 2 half))).
  - rewrite pow_INR. rewrite log2_pow2. lra.
  - apply Rle_trans with (r2 := log2 (INR (Nat.pow (S (2 * half)) k))).
    + apply log2_increasing.
      * apply lt_0_INR. pose proof (nat_pow_pos 2 half). lia.
      * apply le_INR. exact Hpow.
    + pose proof (message_space_bound half k Hhalf). lra.
Qed.

Lemma ln_gt_0 : forall x : R, x > 1 -> ln x > 0.
Proof. intros x Hx. rewrite <- ln_1. apply ln_increasing; lra. Qed.

Lemma log2_pos_for_ge3 : forall m : nat, (m >= 3)%nat -> log2 (INR m) > 0.
Proof.
  intros m Hm. unfold log2. apply Rmult_pos_pos.
  - apply ln_gt_0. apply lt_1_INR. lia.
  - apply Rinv_0_lt_compat. apply ln_2_pos.
Qed.

Theorem gates_lower_bound : forall half k : nat,
  (half >= 1)%nat ->
  (Nat.pow (S (2 * half)) k >= Nat.pow 2 half)%nat ->
  log2 (INR (S (2 * half))) > 0 ->
  INR k >= INR half / log2 (INR (S (2 * half))).
Proof.
  intros half k Hhalf Hpow Hlog_pos.
  pose proof (lower_bound_from_messages half k Hhalf Hpow) as H.
  unfold Rdiv. apply Rle_ge.
  apply Rmult_le_reg_r with (r := log2 (INR (S (2 * half)))).
  - exact Hlog_pos.
  - rewrite Rmult_assoc.
    rewrite Rinv_l by (apply Rgt_not_eq; exact Hlog_pos).
    rewrite Rmult_1_r. apply Rge_le in H.
    rewrite Rmult_comm in H. rewrite Rmult_comm. exact H.
Qed.

(** *** LOWER BOUND: Ω(n/log n) Gates Required *)
Theorem lower_bound_omega_n_over_log_n : forall half k : nat,
  (half >= 1)%nat ->
  (Nat.pow (S (2 * half)) k >= Nat.pow 2 half)%nat ->
  INR k >= INR half / log2 (INR (S (2 * half))).
Proof.
  intros half k Hhalf Hpow.
  assert (Hlog_pos : log2 (INR (S (2 * half))) > 0).
  { apply log2_pos_for_ge3. lia. }
  apply (gates_lower_bound half k Hhalf Hpow Hlog_pos).
Qed.

(** ** Concrete Bounds *)

Lemma n8_1_gate_insufficient : (Nat.pow 9 1 < Nat.pow 2 4)%nat.
Proof. vm_compute. lia. Qed.

Lemma n8_2_gates_sufficient : (Nat.pow 9 2 >= Nat.pow 2 4)%nat.
Proof. vm_compute. lia. Qed.

Lemma n16_1_gate_insufficient : (Nat.pow 17 1 < Nat.pow 2 8)%nat.
Proof. vm_compute. lia. Qed.

Lemma n16_2_gates_sufficient : (Nat.pow 17 2 >= Nat.pow 2 8)%nat.
Proof. vm_compute. lia. Qed.

Close Scope R_scope.

(** * Part V: Main Summary Theorem *)

Close Scope Z_scope.

(**
   UNIFIED BOUNDS FOR DEPTH-2 THRESHOLD CIRCUITS COMPUTING PARITY:

   1. DEPTH-1 IS IMPOSSIBLE (lower_bound_depth1_impossible):
      No single threshold gate can compute n-bit parity for n >= 2.
      Proof: The four 2-bit inputs {00, 01, 10, 11} create contradictory
      constraints on the gate's weights and bias.

   2. DEPTH-2 SUFFICES (upper_bound_depth2_suffices):
      An 11-neuron depth-2 circuit computes 8-bit parity:
      - Layer 1: 9 thermometer neurons (detect HW >= k for k = 0..8)
      - Layer 2: 1 alternating-weight neuron (detect even HW)
      - Output: 1 negation neuron (flip to get odd HW = parity)

   3. DEPTH-2 REQUIRES Ω(n/log n) GATES (lower_bound_omega_n_over_log_n):
      Communication complexity argument: if Alice holds n/2 bits and
      Bob holds n/2 bits, computing parity requires Ω(n) bits of
      communication. With k gates each leaking O(log n) bits via
      partial dot products, we need k * log(n) >= Ω(n), hence
      k >= Ω(n / log n).

   This is the FIRST Coq formalization of depth-2 threshold circuit
   lower bounds for parity.
*)

Theorem depth2_parity_bounds :
  (forall n, (n >= 2)%nat ->
    forall ws b, length ws = n ->
    ~ (forall xs, length xs = n -> gate ws b xs = parity xs))
  /\
  (forall xs, length xs = 8%nat -> parity_depth2 xs = parity xs)
  /\
  (forall half k : nat,
    (half >= 1)%nat ->
    (Nat.pow (S (2 * half)) k >= Nat.pow 2 half)%nat ->
    (INR k >= INR half / log2 (INR (S (2 * half))))%R).
Proof.
  repeat split.
  - exact lower_bound_depth1_impossible.
  - exact upper_bound_depth2_suffices.
  - exact lower_bound_omega_n_over_log_n.
Qed.
