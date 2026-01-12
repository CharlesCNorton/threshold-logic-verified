(** * Depth Bounds for Parity in Threshold Circuits *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(** ** Definitions *)

Definition bit := bool.

Fixpoint dot (ws : list Z) (xs : list bit) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' => (if x then w else 0) + dot ws' xs'
  end.

Definition threshold_gate (ws : list Z) (b : Z) (xs : list bit) : bit :=
  if Z.geb (dot ws xs + b) 0 then true else false.

Fixpoint parity (xs : list bit) : bit :=
  match xs with
  | [] => false
  | x :: xs' => xorb x (parity xs')
  end.

Definition depth2_circuit (layer1 : list (list Z * Z)) (w2 : list Z) (b2 : Z)
                          (xs : list bit) : bit :=
  let h := map (fun wb => threshold_gate (fst wb) (snd wb) xs) layer1 in
  threshold_gate w2 b2 h.

(** ** Arithmetic Lemmas *)

Lemma geb_true_iff : forall a, (a >=? 0) = true <-> a >= 0.
Proof.
  intros.
  rewrite Z.geb_leb.
  split.
  - intros H. apply Z.leb_le in H. lia.
  - intros H. apply Z.leb_le. lia.
Qed.

Lemma geb_false_iff : forall a, (a >=? 0) = false <-> a < 0.
Proof.
  intros.
  rewrite Z.geb_leb.
  split.
  - intros H. apply Z.leb_gt in H. lia.
  - intros H. apply Z.leb_gt. lia.
Qed.

Lemma gate_fires : forall ws b xs,
  threshold_gate ws b xs = true <-> dot ws xs + b >= 0.
Proof.
  intros.
  unfold threshold_gate.
  destruct (dot ws xs + b >=? 0) eqn:E.
  - split; intros; auto. apply geb_true_iff in E. exact E.
  - split; intros H; try discriminate. apply geb_false_iff in E. lia.
Qed.

Lemma gate_silent : forall ws b xs,
  threshold_gate ws b xs = false <-> dot ws xs + b < 0.
Proof.
  intros.
  unfold threshold_gate.
  destruct (dot ws xs + b >=? 0) eqn:E.
  - split; intros H; try discriminate. apply geb_true_iff in E. lia.
  - split; intros; auto. apply geb_false_iff in E. exact E.
Qed.

(** ** Test Inputs *)

Definition input_00 : list bit := [false; false].
Definition input_01 : list bit := [false; true].
Definition input_10 : list bit := [true; false].
Definition input_11 : list bit := [true; true].

Lemma dot_00 : forall w0 w1, dot [w0; w1] input_00 = 0.
Proof. intros. reflexivity. Qed.

Lemma dot_01 : forall w0 w1, dot [w0; w1] input_01 = w1.
Proof. intros. unfold input_01, dot. lia. Qed.

Lemma dot_10 : forall w0 w1, dot [w0; w1] input_10 = w0.
Proof. intros. unfold input_10, dot. lia. Qed.

Lemma dot_11 : forall w0 w1, dot [w0; w1] input_11 = w0 + w1.
Proof. intros. unfold input_11, dot. lia. Qed.

(** ** Part 1: Depth-1 Impossibility *)

Theorem depth1_impossible_2bit : forall w0 w1 b,
  threshold_gate [w0; w1] b input_00 = parity input_00 ->
  threshold_gate [w0; w1] b input_01 = parity input_01 ->
  threshold_gate [w0; w1] b input_10 = parity input_10 ->
  threshold_gate [w0; w1] b input_11 = parity input_11 ->
  False.
Proof.
  intros w0 w1 b H00 H01 H10 H11.
  simpl in H00, H01, H10, H11.
  rewrite gate_silent in H00.
  rewrite gate_fires in H01.
  rewrite gate_fires in H10.
  rewrite gate_silent in H11.
  rewrite dot_00 in H00.
  rewrite dot_01 in H01.
  rewrite dot_10 in H10.
  rewrite dot_11 in H11.
  lia.
Qed.

Lemma dot_pad_zeros : forall ws k,
  dot ws (repeat false k) = 0.
Proof.
  intros ws k.
  revert ws.
  induction k; intros ws.
  - simpl. destruct ws; reflexivity.
  - simpl. destruct ws as [| w ws'].
    + reflexivity.
    + simpl. rewrite IHk. lia.
Qed.

Lemma parity_pad_zeros : forall xs k,
  parity (xs ++ repeat false k) = parity xs.
Proof.
  intros xs k.
  revert xs.
  induction k; intros xs.
  - rewrite app_nil_r. reflexivity.
  - simpl.
    replace (xs ++ false :: repeat false k) with ((xs ++ [false]) ++ repeat false k).
    2: { rewrite <- app_assoc. reflexivity. }
    rewrite IHk.
    induction xs.
    + reflexivity.
    + simpl. rewrite IHxs. reflexivity.
Qed.

Theorem depth1_impossible_nbit : forall n, (n >= 2)%nat ->
  forall ws b,
  length ws = n ->
  (forall xs, length xs = n -> threshold_gate ws b xs = parity xs) ->
  False.
Proof.
  intros n Hn ws b Hlen Hgate.
  destruct ws as [| w0 ws']. { simpl in Hlen. lia. }
  destruct ws' as [| w1 ws'']. { simpl in Hlen. lia. }
  set (pad := (n - 2)%nat).
  assert (Hlen00 : length (input_00 ++ repeat false pad) = n).
  { unfold input_00, pad. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hlen01 : length (input_01 ++ repeat false pad) = n).
  { unfold input_01, pad. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hlen10 : length (input_10 ++ repeat false pad) = n).
  { unfold input_10, pad. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hlen11 : length (input_11 ++ repeat false pad) = n).
  { unfold input_11, pad. rewrite app_length, repeat_length. simpl. lia. }
  pose proof (Hgate _ Hlen00) as H00.
  pose proof (Hgate _ Hlen01) as H01.
  pose proof (Hgate _ Hlen10) as H10.
  pose proof (Hgate _ Hlen11) as H11.
  rewrite parity_pad_zeros in H00, H01, H10, H11.
  rewrite gate_silent in H00.
  rewrite gate_fires in H01.
  rewrite gate_fires in H10.
  rewrite gate_silent in H11.
  unfold input_00, input_01, input_10, input_11 in *.
  simpl in H00, H01, H10, H11.
  rewrite dot_pad_zeros in H00, H01, H10, H11.
  lia.
Qed.

(** ** Part 2: Depth-2 Construction for 2-bit Parity *)

Definition at_least_1 : list Z * Z := ([1; 1], -1).
Definition at_least_2 : list Z * Z := ([1; 1], -2).
Definition parity_2bit_layer1 : list (list Z * Z) := [at_least_1; at_least_2].
Definition parity_2bit_output_w : list Z := [1; -1].
Definition parity_2bit_output_b : Z := -1.

Lemma at_least_1_00 : threshold_gate [1;1] (-1) input_00 = false.
Proof. reflexivity. Qed.

Lemma at_least_1_01 : threshold_gate [1;1] (-1) input_01 = true.
Proof. reflexivity. Qed.

Lemma at_least_1_10 : threshold_gate [1;1] (-1) input_10 = true.
Proof. reflexivity. Qed.

Lemma at_least_1_11 : threshold_gate [1;1] (-1) input_11 = true.
Proof. reflexivity. Qed.

Lemma at_least_2_00 : threshold_gate [1;1] (-2) input_00 = false.
Proof. reflexivity. Qed.

Lemma at_least_2_01 : threshold_gate [1;1] (-2) input_01 = false.
Proof. reflexivity. Qed.

Lemma at_least_2_10 : threshold_gate [1;1] (-2) input_10 = false.
Proof. reflexivity. Qed.

Lemma at_least_2_11 : threshold_gate [1;1] (-2) input_11 = true.
Proof. reflexivity. Qed.

Theorem depth2_computes_parity_2bit :
  (depth2_circuit parity_2bit_layer1 parity_2bit_output_w parity_2bit_output_b input_00 = parity input_00) /\
  (depth2_circuit parity_2bit_layer1 parity_2bit_output_w parity_2bit_output_b input_01 = parity input_01) /\
  (depth2_circuit parity_2bit_layer1 parity_2bit_output_w parity_2bit_output_b input_10 = parity input_10) /\
  (depth2_circuit parity_2bit_layer1 parity_2bit_output_w parity_2bit_output_b input_11 = parity input_11).
Proof.
  unfold depth2_circuit, parity_2bit_layer1, parity_2bit_output_w, parity_2bit_output_b.
  unfold at_least_1, at_least_2.
  simpl.
  auto.
Qed.

(** ** Part 3: Depth-2 Construction for n-bit Parity *)

Fixpoint at_least_k_weights (n : nat) : list Z :=
  repeat 1 n.

Definition at_least_k (n k : nat) : list Z * Z :=
  (at_least_k_weights n, - Z.of_nat k).

Fixpoint layer1_n (n : nat) (k : nat) : list (list Z * Z) :=
  match k with
  | O => []
  | S k' => layer1_n n k' ++ [at_least_k n k]
  end.

Fixpoint alternating_weights (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => alternating_weights k' ++ [if Nat.even k then -1 else 1]
  end.

Definition parity_nbit_layer1 (n : nat) : list (list Z * Z) := layer1_n n n.
Definition parity_nbit_output_w (n : nat) : list Z := alternating_weights n.
Definition parity_nbit_output_b : Z := -1.

(** ** Summary *)

Theorem depth_bounds :
  (forall n, (n >= 2)%nat ->
    forall ws b, length ws = n ->
    ~(forall xs, length xs = n -> threshold_gate ws b xs = parity xs)) /\
  (depth2_circuit parity_2bit_layer1 parity_2bit_output_w parity_2bit_output_b input_00 = parity input_00 /\
   depth2_circuit parity_2bit_layer1 parity_2bit_output_w parity_2bit_output_b input_01 = parity input_01 /\
   depth2_circuit parity_2bit_layer1 parity_2bit_output_w parity_2bit_output_b input_10 = parity input_10 /\
   depth2_circuit parity_2bit_layer1 parity_2bit_output_w parity_2bit_output_b input_11 = parity input_11).
Proof.
  split.
  - intros n Hn ws b Hlen Hgate.
    exact (depth1_impossible_nbit n Hn ws b Hlen Hgate).
  - exact depth2_computes_parity_2bit.
Qed.
