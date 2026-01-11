(** * Final Constructive Proof of Parity Network Correctness *)

(**
   This is the most structured proof of the pruned threshold network.

   Architecture: 8 -> 11 -> 3 -> 1

   Proof structure:
   1. L2-N0 always fires (CONSTRUCTIVE via dot product bounds)
   2. L2-N2 always fires (CONSTRUCTIVE via dot product bounds)
   3. L1-N3 always fires (CONSTRUCTIVE via dot product bounds)
   4. L1-N4 always fires (CONSTRUCTIVE via dot product bounds)
   5. L2-N1 = even(HW) (via HW-class decomposition: 9 small vm_computes)
   6. Output = NOT(L2-N1) = parity (ALGEBRAIC derivation)

   Key insight: The network implements parity by:
   - Using two "always on" neurons (L2-N0, L2-N2)
   - A parity discriminator (L2-N1) that fires iff HW is even
   - Output wiring that negates the discriminator
*)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(** ** Core Definitions *)

Definition bit := bool.
Definition weight := Z.
Definition bias := Z.

Definition heaviside (x : Z) : bit := if Z.geb x 0 then true else false.

Fixpoint dot (ws : list weight) (xs : list bit) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' => (if x then w else 0) + dot ws' xs'
  end.

Fixpoint sum_negative (ws : list weight) : Z :=
  match ws with
  | [] => 0
  | w :: ws' => (if Z.ltb w 0 then w else 0) + sum_negative ws'
  end.

(** ** Dot Product Lower Bound *)

Lemma dot_lower_bound : forall ws xs,
  length ws = length xs -> sum_negative ws <= dot ws xs.
Proof.
  induction ws as [| w ws' IH]; intros xs Hlen.
  - simpl. lia.
  - destruct xs as [| x xs']; simpl in Hlen; try lia.
    injection Hlen as Hlen'. simpl. specialize (IH xs' Hlen').
    destruct x; destruct (Z.ltb w 0) eqn:Hneg.
    + apply Z.ltb_lt in Hneg. lia.
    + apply Z.ltb_ge in Hneg. lia.
    + apply Z.ltb_lt in Hneg. lia.
    + apply Z.ltb_ge in Hneg. lia.
Qed.

(** ** Neuron Definition and Always-Fire Lemma *)

Definition neuron (ws : list weight) (b : bias) (xs : list bit) : bit :=
  heaviside (dot ws xs + b).

Lemma geb_false_lt : forall a b, Z.geb a b = false -> a < b.
Proof. intros. rewrite Z.geb_leb in H. apply Z.leb_gt. exact H. Qed.

Lemma neuron_always_fires : forall ws b xs,
  length ws = length xs -> sum_negative ws + b >= 0 -> neuron ws b xs = true.
Proof.
  intros. unfold neuron, heaviside.
  assert (Hlower := dot_lower_bound ws xs H).
  destruct (Z.geb (dot ws xs + b) 0) eqn:E; auto.
  apply geb_false_lt in E. lia.
Qed.

Definition layer (neurons : list (list weight * bias)) (xs : list bit) : list bit :=
  map (fun wb => neuron (fst wb) (snd wb) xs) neurons.

(** ** Network Weights *)

Definition l1n3_weights : list weight := [0; 1; -1; -1; -1; 0; 1; 0].
Definition l1n3_bias : bias := 5.
Definition l1n4_weights : list weight := [1; -1; -1; 0; -1; 1; -1; 0].
Definition l1n4_bias : bias := 7.

Definition layer1_weights : list (list weight * bias) :=
  [ ([1; -1; 1; -1; 1; 1; 1; 1], 0);
    ([-1; 1; -1; 1; 1; -1; -1; -1], 1);
    ([-1; -1; -1; -1; -1; -1; -1; 1], 2);
    (l1n3_weights, l1n3_bias);
    (l1n4_weights, l1n4_bias);
    ([-1; 1; -1; 1; -1; -1; -1; -1], 0);
    ([-1; 1; -1; 1; 1; -1; -1; -1], 3);
    ([1; -1; 1; -1; 1; 1; 1; 1], -2);
    ([1; 1; -1; 1; 1; 1; 1; -1], -2);
    ([-1; 1; -1; 1; 1; -1; -1; -1], 0);
    ([-1; 1; -1; 1; 1; -1; -1; -1], 2) ].

Definition l2n0_weights : list weight := [0; 0; -1; -1; 0; 0; -1; 1; -1; 1; -1].
Definition l2n0_bias : bias := 30.
Definition l2n1_weights : list weight := [1; -1; 1; 1; -1; 1; -1; 1; 1; 1; 1].
Definition l2n1_bias : bias := -3.
Definition l2n2_weights : list weight := [1; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1].
Definition l2n2_bias : bias := 20.

Definition layer2_weights : list (list weight * bias) :=
  [(l2n0_weights, l2n0_bias); (l2n1_weights, l2n1_bias); (l2n2_weights, l2n2_bias)].

Definition output_weights : list weight * bias := ([1; -1; 1], -2).

Definition l1_output (xs : list bit) : list bit := layer layer1_weights xs.

Definition network (xs : list bit) : bit :=
  let h1 := l1_output xs in
  let h2 := layer layer2_weights h1 in
  neuron (fst output_weights) (snd output_weights) h2.

(** ** Length Lemmas *)

Lemma l1_output_length : forall xs,
  length xs = 8%nat -> length (l1_output xs) = 11%nat.
Proof. intros. unfold l1_output, layer. rewrite map_length. reflexivity. Qed.

(** ** CONSTRUCTIVE: L1-N3 Always Fires *)

Lemma l1n3_sum_neg : sum_negative l1n3_weights = -3.
Proof. reflexivity. Qed.

Theorem L1N3_always_fires : forall xs,
  length xs = 8%nat -> neuron l1n3_weights l1n3_bias xs = true.
Proof.
  intros xs Hlen. apply neuron_always_fires.
  - unfold l1n3_weights. simpl. rewrite Hlen. reflexivity.
  - rewrite l1n3_sum_neg. unfold l1n3_bias. lia.
Qed.

(** ** CONSTRUCTIVE: L1-N4 Always Fires *)

Lemma l1n4_sum_neg : sum_negative l1n4_weights = -4.
Proof. reflexivity. Qed.

Theorem L1N4_always_fires : forall xs,
  length xs = 8%nat -> neuron l1n4_weights l1n4_bias xs = true.
Proof.
  intros xs Hlen. apply neuron_always_fires.
  - unfold l1n4_weights. simpl. rewrite Hlen. reflexivity.
  - rewrite l1n4_sum_neg. unfold l1n4_bias. lia.
Qed.

(** ** CONSTRUCTIVE: L2-N0 Always Fires *)

Lemma l2n0_sum_neg : sum_negative l2n0_weights = -5.
Proof. reflexivity. Qed.

Theorem L2N0_always_fires : forall xs,
  length xs = 8%nat -> neuron l2n0_weights l2n0_bias (l1_output xs) = true.
Proof.
  intros. apply neuron_always_fires.
  - rewrite l1_output_length by auto. reflexivity.
  - rewrite l2n0_sum_neg. unfold l2n0_bias. lia.
Qed.

(** ** CONSTRUCTIVE: L2-N2 Always Fires *)

Lemma l2n2_sum_neg : sum_negative l2n2_weights = 0.
Proof. reflexivity. Qed.

Theorem L2N2_always_fires : forall xs,
  length xs = 8%nat -> neuron l2n2_weights l2n2_bias (l1_output xs) = true.
Proof.
  intros. apply neuron_always_fires.
  - rewrite l1_output_length by auto. reflexivity.
  - rewrite l2n2_sum_neg. unfold l2n2_bias. lia.
Qed.

(** ** Hamming Weight and Parity *)

Fixpoint hamming_weight (xs : list bit) : nat :=
  match xs with
  | [] => O
  | true :: xs' => S (hamming_weight xs')
  | false :: xs' => hamming_weight xs'
  end.

Fixpoint parity (xs : list bit) : bit :=
  match xs with
  | [] => false
  | x :: xs' => xorb x (parity xs')
  end.

Lemma odd_succ : forall n, Nat.odd (S n) = negb (Nat.odd n).
Proof. induction n; simpl; auto. rewrite IHn. rewrite Bool.negb_involutive. reflexivity. Qed.

Lemma parity_is_odd : forall xs, parity xs = Nat.odd (hamming_weight xs).
Proof.
  induction xs as [| x xs' IH]; simpl.
  - reflexivity.
  - destruct x; simpl.
    + rewrite IH. rewrite odd_succ. reflexivity.
    + exact IH.
Qed.

Lemma odd_negb_even : forall n, Nat.odd n = negb (Nat.even n).
Proof. intro n. unfold Nat.odd. reflexivity. Qed.

(** ** Input Generation *)

Fixpoint all_inputs (n : nat) : list (list bit) :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')
  end.

Lemma all_inputs_length : forall n xs, In xs (all_inputs n) -> length xs = n.
Proof.
  induction n; intros xs Hin; simpl in *.
  - destruct Hin as [<- | []]. reflexivity.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin];
    apply in_map_iff in Hin; destruct Hin as [ys [<- Hys]];
    simpl; f_equal; apply IHn; exact Hys.
Qed.

(** ** L2-N1: Hamming-Weight Class Analysis *)

Definition l2n1_neuron (xs : list bit) : bit :=
  neuron l2n1_weights l2n1_bias (l1_output xs).

(** Filter inputs by Hamming weight *)
Definition inputs_with_hw (n hw : nat) : list (list bit) :=
  filter (fun xs => Nat.eqb (hamming_weight xs) hw) (all_inputs n).

(** Check that L2-N1 fires for all inputs with given HW *)
Definition check_fires_hw (hw : nat) : bool :=
  forallb (fun xs => l2n1_neuron xs) (inputs_with_hw 8 hw).

(** Check that L2-N1 doesn't fire for all inputs with given HW *)
Definition check_silent_hw (hw : nat) : bool :=
  forallb (fun xs => negb (l2n1_neuron xs)) (inputs_with_hw 8 hw).

(** Even HW classes: L2-N1 fires *)
Lemma l2n1_hw0 : check_fires_hw 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma l2n1_hw2 : check_fires_hw 2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma l2n1_hw4 : check_fires_hw 4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma l2n1_hw6 : check_fires_hw 6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma l2n1_hw8 : check_fires_hw 8 = true. Proof. vm_compute. reflexivity. Qed.

(** Odd HW classes: L2-N1 doesn't fire *)
Lemma l2n1_hw1 : check_silent_hw 1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma l2n1_hw3 : check_silent_hw 3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma l2n1_hw5 : check_silent_hw 5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma l2n1_hw7 : check_silent_hw 7 = true. Proof. vm_compute. reflexivity. Qed.

(** Helper: filter membership *)
Lemma filter_In : forall A (f : A -> bool) l x,
  In x (filter f l) <-> In x l /\ f x = true.
Proof.
  intros. induction l.
  - simpl. split; intros []; auto.
  - simpl. destruct (f a) eqn:Hf.
    + simpl. split.
      * intros [Heq | Hin]. subst. auto. apply IHl in Hin. destruct Hin. auto.
      * intros [[Heq | Hin] Hfx]. left. exact Heq. right. apply IHl. auto.
    + split.
      * intros Hin. apply IHl in Hin. destruct Hin. auto.
      * intros [[Heq | Hin] Hfx]. subst. rewrite Hfx in Hf. discriminate. apply IHl. auto.
Qed.

Lemma inputs_with_hw_correct : forall n hw xs,
  In xs (inputs_with_hw n hw) <-> In xs (all_inputs n) /\ hamming_weight xs = hw.
Proof.
  intros. unfold inputs_with_hw. rewrite filter_In.
  split; intros [H1 H2]; split; auto.
  - apply Nat.eqb_eq. exact H2.
  - apply Nat.eqb_eq in H2. exact H2.
Qed.

(** HW bound *)
Lemma hw_le_length : forall xs, (hamming_weight xs <= length xs)%nat.
Proof. induction xs as [| x xs' IH]; simpl. lia. destruct x; lia. Qed.

Lemma hw_cases : forall xs,
  In xs (all_inputs 8) ->
  hamming_weight xs = 0%nat \/ hamming_weight xs = 1%nat \/
  hamming_weight xs = 2%nat \/ hamming_weight xs = 3%nat \/
  hamming_weight xs = 4%nat \/ hamming_weight xs = 5%nat \/
  hamming_weight xs = 6%nat \/ hamming_weight xs = 7%nat \/
  hamming_weight xs = 8%nat.
Proof.
  intros xs Hin.
  assert (Hlen: length xs = 8%nat) by (apply all_inputs_length; exact Hin).
  assert (Hle := hw_le_length xs). lia.
Qed.

(** ** L2-N1 = even(HW) via HW-class decomposition *)

Theorem L2N1_equals_even : forall xs,
  In xs (all_inputs 8) ->
  l2n1_neuron xs = Nat.even (hamming_weight xs).
Proof.
  intros xs Hin.
  destruct (hw_cases xs Hin) as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; rewrite H.
  - (* HW=0 *) assert (Hv := l2n1_hw0). unfold check_fires_hw in Hv.
    rewrite forallb_forall in Hv.
    assert (Hin': In xs (inputs_with_hw 8 0)) by (apply inputs_with_hw_correct; auto).
    specialize (Hv xs Hin'). simpl. rewrite Hv. reflexivity.
  - (* HW=1 *) assert (Hv := l2n1_hw1). unfold check_silent_hw in Hv.
    rewrite forallb_forall in Hv.
    assert (Hin': In xs (inputs_with_hw 8 1)) by (apply inputs_with_hw_correct; auto).
    specialize (Hv xs Hin'). simpl. rewrite Bool.negb_true_iff in Hv. rewrite Hv. reflexivity.
  - (* HW=2 *) assert (Hv := l2n1_hw2). unfold check_fires_hw in Hv.
    rewrite forallb_forall in Hv.
    assert (Hin': In xs (inputs_with_hw 8 2)) by (apply inputs_with_hw_correct; auto).
    specialize (Hv xs Hin'). simpl. rewrite Hv. reflexivity.
  - (* HW=3 *) assert (Hv := l2n1_hw3). unfold check_silent_hw in Hv.
    rewrite forallb_forall in Hv.
    assert (Hin': In xs (inputs_with_hw 8 3)) by (apply inputs_with_hw_correct; auto).
    specialize (Hv xs Hin'). simpl. rewrite Bool.negb_true_iff in Hv. rewrite Hv. reflexivity.
  - (* HW=4 *) assert (Hv := l2n1_hw4). unfold check_fires_hw in Hv.
    rewrite forallb_forall in Hv.
    assert (Hin': In xs (inputs_with_hw 8 4)) by (apply inputs_with_hw_correct; auto).
    specialize (Hv xs Hin'). simpl. rewrite Hv. reflexivity.
  - (* HW=5 *) assert (Hv := l2n1_hw5). unfold check_silent_hw in Hv.
    rewrite forallb_forall in Hv.
    assert (Hin': In xs (inputs_with_hw 8 5)) by (apply inputs_with_hw_correct; auto).
    specialize (Hv xs Hin'). simpl. rewrite Bool.negb_true_iff in Hv. rewrite Hv. reflexivity.
  - (* HW=6 *) assert (Hv := l2n1_hw6). unfold check_fires_hw in Hv.
    rewrite forallb_forall in Hv.
    assert (Hin': In xs (inputs_with_hw 8 6)) by (apply inputs_with_hw_correct; auto).
    specialize (Hv xs Hin'). simpl. rewrite Hv. reflexivity.
  - (* HW=7 *) assert (Hv := l2n1_hw7). unfold check_silent_hw in Hv.
    rewrite forallb_forall in Hv.
    assert (Hin': In xs (inputs_with_hw 8 7)) by (apply inputs_with_hw_correct; auto).
    specialize (Hv xs Hin'). simpl. rewrite Bool.negb_true_iff in Hv. rewrite Hv. reflexivity.
  - (* HW=8 *) assert (Hv := l2n1_hw8). unfold check_fires_hw in Hv.
    rewrite forallb_forall in Hv.
    assert (Hin': In xs (inputs_with_hw 8 8)) by (apply inputs_with_hw_correct; auto).
    specialize (Hv xs Hin'). simpl. rewrite Hv. reflexivity.
Qed.

(** ** Layer 2 Structure *)

Lemma l2_structure : forall xs,
  layer layer2_weights (l1_output xs) =
  [neuron l2n0_weights l2n0_bias (l1_output xs);
   neuron l2n1_weights l2n1_bias (l1_output xs);
   neuron l2n2_weights l2n2_bias (l1_output xs)].
Proof. reflexivity. Qed.

(** ** MAIN THEOREM *)

Theorem network_computes_parity : forall xs,
  In xs (all_inputs 8) ->
  network xs = parity xs.
Proof.
  intros xs Hin.
  assert (Hlen: length xs = 8%nat) by (apply all_inputs_length; exact Hin).

  (* CONSTRUCTIVE: L2-N0 always fires *)
  assert (H0: neuron l2n0_weights l2n0_bias (l1_output xs) = true)
    by (apply L2N0_always_fires; exact Hlen).

  (* CONSTRUCTIVE: L2-N2 always fires *)
  assert (H2: neuron l2n2_weights l2n2_bias (l1_output xs) = true)
    by (apply L2N2_always_fires; exact Hlen).

  (* HW-CLASS DECOMPOSITION: L2-N1 = even(HW) *)
  assert (H1: neuron l2n1_weights l2n1_bias (l1_output xs) = Nat.even (hamming_weight xs)).
  { apply L2N1_equals_even. exact Hin. }

  (* ALGEBRAIC: derive final result *)
  unfold network. fold l1_output. rewrite l2_structure.
  rewrite H0, H1, H2.
  unfold neuron, output_weights, dot, heaviside. simpl.
  rewrite parity_is_odd, odd_negb_even.
  destruct (Nat.even (hamming_weight xs)); simpl; reflexivity.
Qed.

(** ** Summary *)

(**
   PROOF SUMMARY
   =============

   This proof decomposes the network correctness into structured components:

   1. CONSTRUCTIVE BOUNDS (no vm_compute):
      - L2-N0 always fires: sum_negative(weights) + bias = -5 + 30 = 25 >= 0
      - L2-N2 always fires: sum_negative(weights) + bias = 0 + 20 = 20 >= 0
      - L1-N3 always fires: sum_negative(weights) + bias = -3 + 5 = 2 >= 0
      - L1-N4 always fires: sum_negative(weights) + bias = -4 + 7 = 3 >= 0

   2. HW-CLASS DECOMPOSITION (9 small vm_computes):
      - HW=0: 1 input, L2-N1 fires
      - HW=1: 8 inputs, L2-N1 silent
      - HW=2: 28 inputs, L2-N1 fires
      - HW=3: 56 inputs, L2-N1 silent
      - HW=4: 70 inputs, L2-N1 fires
      - HW=5: 56 inputs, L2-N1 silent
      - HW=6: 28 inputs, L2-N1 fires
      - HW=7: 8 inputs, L2-N1 silent
      - HW=8: 1 input, L2-N1 fires

   3. ALGEBRAIC DERIVATION:
      - Output = h2[0] - h2[1] + h2[2] - 2 >= 0
      - Since h2[0] = h2[2] = 1 always:
        = 1 - h2[1] + 1 - 2 >= 0
        = -h2[1] >= 0
        = h2[1] = 0
        = L2-N1 doesn't fire
        = HW is odd
        = parity(input)

   INSIGHT: The network implements parity by:
   1. Using two "always on" neurons to set up the output threshold
   2. Using L2-N1 as a parity discriminator (fires iff HW even)
   3. Negating the discriminator via the output weights

   This explains WHY the network computes parity, not just THAT it does.
*)
