Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

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

Lemma dot_lower_bound : forall ws xs,
  length ws = length xs -> sum_negative ws <= dot ws xs.
Proof.
  induction ws as [| w ws' IH]; intros xs Hlen.
  - simpl. lia.
  - destruct xs as [| x xs']; simpl in Hlen; try lia.
    injection Hlen as Hlen'. simpl. specialize (IH xs' Hlen').
    destruct x; destruct (Z.ltb w 0) eqn:Hneg;
    try (apply Z.ltb_lt in Hneg); try (apply Z.ltb_nlt in Hneg); lia.
Qed.

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

Definition layer1_weights : list (list weight * bias) :=
  [ ([1; -1; 1; -1; 1; 1; 1; 1], 0);
    ([-1; 1; -1; 1; 1; -1; -1; -1], 1);
    ([-1; -1; -1; -1; -1; -1; -1; 1], 2);
    ([0; 1; -1; -1; -1; 0; 1; 0], 5);
    ([1; -1; -1; 0; -1; 1; -1; 0], 7);
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

Lemma l1_output_length : forall xs,
  length xs = 8%nat -> length (l1_output xs) = 11%nat.
Proof. intros. unfold l1_output, layer. rewrite map_length. reflexivity. Qed.

Theorem L2N0_always_fires : forall xs,
  length xs = 8%nat -> neuron l2n0_weights l2n0_bias (l1_output xs) = true.
Proof.
  intros. apply neuron_always_fires.
  - rewrite l1_output_length by auto. reflexivity.
  - reflexivity.
Qed.

Theorem L2N2_always_fires : forall xs,
  length xs = 8%nat -> neuron l2n2_weights l2n2_bias (l1_output xs) = true.
Proof.
  intros. apply neuron_always_fires.
  - rewrite l1_output_length by auto. reflexivity.
  - reflexivity.
Qed.

Fixpoint hamming_weight (xs : list bit) : nat :=
  match xs with
  | [] => O
  | true :: xs' => S (hamming_weight xs')
  | false :: xs' => hamming_weight xs'
  end.

Fixpoint all_inputs (n : nat) : list (list bit) :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')
  end.

Definition check_l2n1 : bool :=
  forallb (fun xs => Bool.eqb (neuron l2n1_weights l2n1_bias (l1_output xs))
                              (Nat.even (hamming_weight xs)))
          (all_inputs 8).

Lemma L2N1_is_even : check_l2n1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma all_inputs_length : forall n xs, In xs (all_inputs n) -> length xs = n.
Proof.
  induction n; intros xs Hin; simpl in *.
  - destruct Hin as [<- | []]. reflexivity.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin];
    apply in_map_iff in Hin; destruct Hin as [ys [<- Hys]];
    simpl; f_equal; apply IHn; exact Hys.
Qed.

Lemma L2N1_equals_even : forall xs,
  In xs (all_inputs 8) ->
  neuron l2n1_weights l2n1_bias (l1_output xs) = Nat.even (hamming_weight xs).
Proof.
  intros xs Hin.
  assert (Hv := L2N1_is_even). unfold check_l2n1 in Hv.
  rewrite forallb_forall in Hv. specialize (Hv xs Hin).
  apply Bool.eqb_prop in Hv. exact Hv.
Qed.

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

Lemma l2_structure : forall xs,
  layer layer2_weights (l1_output xs) =
  [neuron l2n0_weights l2n0_bias (l1_output xs);
   neuron l2n1_weights l2n1_bias (l1_output xs);
   neuron l2n2_weights l2n2_bias (l1_output xs)].
Proof. reflexivity. Qed.

Theorem network_computes_parity : forall xs,
  In xs (all_inputs 8) ->
  network xs = parity xs.
Proof.
  intros xs Hin.
  assert (Hlen: length xs = 8%nat) by (apply all_inputs_length; exact Hin).
  assert (H0: neuron l2n0_weights l2n0_bias (l1_output xs) = true)
    by (apply L2N0_always_fires; exact Hlen).
  assert (H2: neuron l2n2_weights l2n2_bias (l1_output xs) = true)
    by (apply L2N2_always_fires; exact Hlen).
  assert (H1: neuron l2n1_weights l2n1_bias (l1_output xs) = Nat.even (hamming_weight xs))
    by (apply L2N1_equals_even; exact Hin).
  unfold network. fold l1_output. rewrite l2_structure.
  rewrite H0, H1, H2.
  unfold neuron, output_weights, dot, heaviside. simpl.
  rewrite parity_is_odd, odd_negb_even.
  destruct (Nat.even (hamming_weight xs)); simpl; reflexivity.
Qed.
