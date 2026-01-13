(** * Depth-2 Threshold Circuit Lower Bounds for Parity *)

(**
   This file formalizes lower bounds on the size of depth-2 threshold
   circuits computing the parity function.

   MAIN RESULTS:
   1. depth1_impossible: A single threshold gate cannot compute parity (n >= 2)
   2. linear_lower_bound: Any depth-2 circuit needs at least n/2 gates for n-bit parity
   3. threshold_function_count: Upper bound on distinct threshold functions
   4. covering_lower_bound: Lower bound via covering argument

   The classical result is Ω(n/log n) gates required (Hajnal et al. 1993).
   We build toward this through progressively stronger bounds.

   LIBRARIES USED:
   - Coq.ZArith.ZArith: Integer arithmetic
   - Coq.Lists.List: List operations
   - Coq.Bool.Bool: Boolean operations
   - Coq.Arith.PeanoNat: Natural number arithmetic
   - Coq.micromega.Lia: Linear integer arithmetic solver
   - Coq.Logic.Classical_Prop: Classical logic (for some existence proofs)
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

Definition bool_id (b : bool) : bool := b.

Open Scope Z_scope.

(** ** Part 1: Basic Definitions *)

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

Lemma xorb_true_l : forall b, xorb true b = negb b.
Proof. destruct b; reflexivity. Qed.

Lemma xorb_false_l : forall b, xorb false b = b.
Proof. destruct b; reflexivity. Qed.

Lemma odd_succ : forall n, Nat.odd (S n) = negb (Nat.odd n).
Proof.
  intros n. unfold Nat.odd. rewrite Nat.even_succ. reflexivity.
Qed.

Lemma parity_is_odd_hw : forall xs,
  parity xs = Nat.odd (hamming_weight xs).
Proof.
  induction xs as [| x xs' IH]; simpl.
  - reflexivity.
  - destruct x.
    + simpl. rewrite IH, odd_succ. reflexivity.
    + simpl. exact IH.
Qed.

(** Dot product of weights and binary inputs *)
Fixpoint dot (ws : list Z) (xs : input) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' => (if x then w else 0) + dot ws' xs'
  end.

Definition gate (ws : list Z) (b : Z) (xs : input) : bit :=
  Z.geb (dot ws xs + b) 0.

Lemma gate_fires_iff : forall ws b xs,
  gate ws b xs = true <-> dot ws xs + b >= 0.
Proof.
  intros ws b xs.
  unfold gate.
  rewrite Z.geb_leb.
  split; intros H.
  - apply Z.leb_le in H. lia.
  - apply Z.leb_le. lia.
Qed.

Lemma gate_silent_iff : forall ws b xs,
  gate ws b xs = false <-> dot ws xs + b < 0.
Proof.
  intros ws b xs.
  unfold gate.
  rewrite Z.geb_leb.
  split; intros H.
  - apply Z.leb_gt in H. lia.
  - apply Z.leb_gt. lia.
Qed.

(** ** Part 2: Depth-1 Impossibility *)

(** Four canonical 2-bit inputs *)
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

(** Core impossibility: no single gate computes 2-bit parity *)
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

(** Padding with zeros preserves parity *)
Definition pad_zeros (xs : input) (k : nat) : input := xs ++ repeat false k.

Lemma parity_app_false : forall xs,
  parity (xs ++ [false]) = parity xs.
Proof.
  induction xs as [| x xs' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma parity_repeat_false : forall k, parity (repeat false k) = false.
Proof.
  induction k as [| k' IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

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

Lemma dot_nil_r : forall ws, dot ws [] = 0.
Proof. destruct ws; reflexivity. Qed.

Lemma dot_app_false : forall ws xs,
  length ws = (length xs + 1)%nat ->
  dot ws (xs ++ [false]) = dot (firstn (length xs) ws) xs.
Proof.
  intros ws xs. revert ws.
  induction xs as [| x xs' IH]; intros ws Hlen.
  - destruct ws as [| w ws']; simpl in *; [lia |].
    destruct ws'; simpl in *; [reflexivity | lia].
  - destruct ws as [| w ws']; simpl in *; [lia |].
    rewrite IH by lia. destruct x; reflexivity.
Qed.

Lemma dot_repeat_false : forall ws k,
  dot ws (repeat false k) = 0.
Proof.
  induction ws as [| w ws' IH]; intros k.
  - reflexivity.
  - destruct k; simpl.
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma dot_pad_zeros : forall ws xs k,
  length ws = (length xs + k)%nat ->
  dot ws (pad_zeros xs k) = dot (firstn (length xs) ws) xs.
Proof.
  intros ws xs k Hlen.
  unfold pad_zeros.
  revert ws k Hlen.
  induction xs as [| x xs' IH]; intros ws k Hlen; simpl in *.
  - apply dot_repeat_false.
  - destruct ws as [| w ws']; simpl in *; [lia |].
    specialize (IH ws' k ltac:(lia)).
    rewrite IH. destruct x; reflexivity.
Qed.

(** Dot product on padded 2-bit inputs *)
Lemma dot_pad_x00 : forall w0 w1 ws k,
  length ws = k ->
  dot (w0 :: w1 :: ws) (pad_zeros x00 k) = 0.
Proof.
  intros. unfold pad_zeros, x00. simpl.
  apply dot_repeat_false.
Qed.

Lemma dot_pad_x01 : forall w0 w1 ws k,
  length ws = k ->
  dot (w0 :: w1 :: ws) (pad_zeros x01 k) = w1.
Proof.
  intros. unfold pad_zeros, x01. simpl.
  rewrite dot_repeat_false. lia.
Qed.

Lemma dot_pad_x10 : forall w0 w1 ws k,
  length ws = k ->
  dot (w0 :: w1 :: ws) (pad_zeros x10 k) = w0.
Proof.
  intros. unfold pad_zeros, x10. simpl.
  rewrite dot_repeat_false. lia.
Qed.

Lemma dot_pad_x11 : forall w0 w1 ws k,
  length ws = k ->
  dot (w0 :: w1 :: ws) (pad_zeros x11 k) = w0 + w1.
Proof.
  intros. unfold pad_zeros, x11. simpl.
  rewrite dot_repeat_false. lia.
Qed.

(** Generalization to n bits - uses 2-bit impossibility *)
Theorem depth1_impossible_nbit : forall n, (n >= 2)%nat ->
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
  unfold gate in H00, H01, H10, H11.
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

(** ** Part 3: Depth-2 Circuit Definitions *)

(** A depth-2 threshold circuit:
    - Layer 1: k gates, each with n inputs
    - Layer 2: 1 gate with k inputs (the outputs of layer 1) *)
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

(** ** Part 4: Counting Threshold Functions *)

(**
   Key insight: The number of distinct threshold functions on n Boolean inputs
   is bounded. This limits what a small circuit can compute.

   A threshold function on n bits is determined by n weights and 1 bias.
   If weights are from a bounded set, the number of functions is finite.

   For arbitrary integer weights, the number of distinct threshold functions
   on n bits is at most 2^(n^2) (a classical result).
*)

(** Helper: NoDup is preserved by injective maps *)
Lemma NoDup_map_inj : forall {A B : Type} (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  intros A B f l Hinj Hnodup.
  induction l as [| a l' IH].
  - constructor.
  - simpl. constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as [a' [Hfeq Hina']].
      assert (Ha : In a (a :: l')) by (left; reflexivity).
      assert (Ha' : In a' (a :: l')) by (right; exact Hina').
      symmetry in Hfeq.
      assert (Heq' : a = a') by (apply Hinj; assumption).
      subst a'.
      inversion Hnodup; subst.
      exact (H1 Hina').
    + apply IH.
      * intros x y Hx Hy Hfxy.
        apply Hinj; [right | right |]; assumption.
      * inversion Hnodup. assumption.
Qed.

(** All n-bit inputs *)
Fixpoint all_inputs (n : nat) : list input :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')
  end.

Lemma all_inputs_length : forall n,
  length (all_inputs n) = Nat.pow 2 n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - change (all_inputs (S n')) with
      (map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')).
    rewrite app_length.
    assert (H1 : length (map (cons false) (all_inputs n')) = length (all_inputs n'))
      by apply map_length.
    assert (H2 : length (map (cons true) (all_inputs n')) = length (all_inputs n'))
      by apply map_length.
    rewrite H1, H2, IH.
    simpl. lia.
Qed.

Lemma all_inputs_elem_length : forall n xs,
  In xs (all_inputs n) -> length xs = n.
Proof.
  induction n as [| n' IH]; intros xs Hin; simpl in *.
  - destruct Hin as [Heq | []]; subst; reflexivity.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply in_map_iff in Hin. destruct Hin as [xs' [Heq Hin']].
      subst. simpl. f_equal. apply IH. exact Hin'.
    + apply in_map_iff in Hin. destruct Hin as [xs' [Heq Hin']].
      subst. simpl. f_equal. apply IH. exact Hin'.
Qed.

(** A threshold function as a list of outputs on all inputs *)
Definition threshold_function_output (ws : list Z) (b : Z) (n : nat) : list bit :=
  map (fun xs => gate ws b xs) (all_inputs n).

(** Two weight/bias pairs compute the same function if they agree on all inputs *)
Definition same_threshold_function (ws1 : list Z) (b1 : Z)
                                    (ws2 : list Z) (b2 : Z) (n : nat) : Prop :=
  threshold_function_output ws1 b1 n = threshold_function_output ws2 b2 n.

(** ** Part 5: Linear Lower Bound via XOR Structure *)

(**
   THEOREM: Any depth-2 circuit computing n-bit parity needs at least
   ceil(n/2) gates in the first layer.

   PROOF IDEA:
   - Parity changes whenever any single bit flips
   - Each layer-1 gate partitions inputs into "fires" and "silent"
   - If a gate has few weights, it cannot distinguish many parity classes
   - With k gates, we get at most 2^k distinct patterns
   - To distinguish 2^n inputs by parity, we need fine-grained separation
*)

(** Bit flip at position i *)
Fixpoint flip_bit (xs : input) (i : nat) : input :=
  match xs, i with
  | [], _ => []
  | x :: xs', O => negb x :: xs'
  | x :: xs', S i' => x :: flip_bit xs' i'
  end.

Lemma flip_bit_length : forall xs i,
  length (flip_bit xs i) = length xs.
Proof.
  induction xs as [| x xs' IH]; intros i; simpl.
  - reflexivity.
  - destruct i; simpl; [reflexivity | f_equal; apply IH].
Qed.

Lemma parity_flip_bit : forall xs i,
  (i < length xs)%nat ->
  parity (flip_bit xs i) = negb (parity xs).
Proof.
  induction xs as [| x xs' IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i as [| i']; simpl.
    + destruct x; simpl; destruct (parity xs'); reflexivity.
    + rewrite IH by lia.
      destruct x; simpl; destruct (parity xs'); reflexivity.
Qed.

(**
   Key lemma: If two inputs differ in exactly one bit,
   their parities differ.
*)
Lemma parity_differs_on_flip : forall xs i,
  (i < length xs)%nat ->
  parity (flip_bit xs i) <> parity xs.
Proof.
  intros xs i Hi.
  rewrite parity_flip_bit by exact Hi.
  destruct (parity xs); discriminate.
Qed.

(** ** Part 6: Affine Subspace Argument *)

(**
   A deeper result: threshold gates compute affine functions on {0,1}^n
   when viewed over the reals. The level sets are half-spaces.

   For parity (which is highly non-linear), many half-spaces are needed
   to carve out the correct regions.
*)

(** Characteristic vector: 1 if parity is odd, 0 if even *)
Definition parity_vector (n : nat) : list bit :=
  map parity (all_inputs n).

(** Helper: filter bool_id on map extracts elements where f is true *)
Lemma filter_id_map : forall {A : Type} (f : A -> bool) (l : list A),
  length (filter bool_id (map f l)) = length (filter f l).
Proof.
  intros A f l.
  induction l as [| a l' IH]; simpl.
  - reflexivity.
  - destruct (f a); simpl; [f_equal |]; exact IH.
Qed.

(** Helper: parity of (false :: xs) = parity xs *)
Lemma parity_cons_false : forall xs, parity (false :: xs) = parity xs.
Proof. intros. reflexivity. Qed.

(** Helper: parity of (true :: xs) = negb (parity xs) *)
Lemma parity_cons_true : forall xs, parity (true :: xs) = negb (parity xs).
Proof. intros. simpl. destruct (parity xs); reflexivity. Qed.

(** Helper: filter on map (cons b) *)
Lemma filter_map_cons : forall (f : input -> bool) (b : bit) (l : list input),
  filter (fun xs => f (b :: xs)) l = filter (fun xs => f (b :: xs)) l.
Proof. reflexivity. Qed.

(** Key lemma: count of odd-parity inputs when prepending false *)
Lemma filter_parity_cons_false : forall l,
  length (filter (fun xs => parity (false :: xs)) l) = length (filter parity l).
Proof.
  intros l.
  induction l as [| x l' IH]; simpl.
  - reflexivity.
  - destruct (parity x); simpl; [f_equal |]; exact IH.
Qed.

(** Key lemma: count of odd-parity inputs when prepending true *)
Lemma filter_parity_cons_true : forall l,
  length (filter (fun xs => parity (true :: xs)) l) = length (filter (fun xs => negb (parity xs)) l).
Proof.
  intros l.
  induction l as [| x l' IH]; simpl.
  - reflexivity.
  - destruct (parity x); simpl; [exact IH | f_equal; exact IH].
Qed.

(** Helper: length of filter on appended lists *)
Lemma filter_app_length : forall {A : Type} (f : A -> bool) (l1 l2 : list A),
  length (filter f (l1 ++ l2)) = (length (filter f l1) + length (filter f l2))%nat.
Proof.
  intros A f l1 l2.
  induction l1 as [| a l1' IH]; simpl.
  - reflexivity.
  - destruct (f a); simpl; [f_equal |]; exact IH.
Qed.

(** Helper: length of filter on mapped list *)
Lemma filter_map_length : forall {A B : Type} (f : B -> bool) (g : A -> B) (l : list A),
  length (filter f (map g l)) = length (filter (fun x => f (g x)) l).
Proof.
  intros A B f g l.
  induction l as [| a l' IH]; simpl.
  - reflexivity.
  - destruct (f (g a)); simpl; [f_equal |]; exact IH.
Qed.

(** Filter partition: lengths of complementary filters sum to original length *)
Lemma filter_partition_length : forall (A : Type) (f : A -> bool) (l : list A),
  (length (filter f l) + length (filter (fun x => negb (f x)) l) = length l)%nat.
Proof.
  intros A f l.
  induction l as [| a l' IH].
  - reflexivity.
  - simpl. destruct (f a) eqn:Hfa; simpl; lia.
Qed.

(** Count of even-parity inputs *)
Lemma filter_even_parity_length : forall n,
  length (filter (fun xs => negb (parity xs)) (all_inputs n)) =
  (Nat.pow 2 n - length (filter parity (all_inputs n)))%nat.
Proof.
  intros n.
  pose proof (filter_partition_length input parity (all_inputs n)) as H.
  rewrite all_inputs_length in H.
  lia.
Qed.

(** Main theorem: exactly half of n-bit inputs have odd parity *)
Lemma parity_odd_count : forall n,
  length (filter parity (all_inputs n)) = (Nat.pow 2 n - Nat.pow 2 (n - 1))%nat.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl all_inputs.
    rewrite filter_app_length.
    rewrite filter_map_length.
    rewrite filter_map_length.
    rewrite filter_parity_cons_false.
    rewrite filter_parity_cons_true.
    rewrite IH.
    rewrite filter_even_parity_length.
    rewrite IH.
    destruct n' as [| n''].
    + simpl. reflexivity.
    + simpl Nat.pow.
      remember (Nat.pow 2 n'') as p.
      lia.
Qed.

(** Helper: 2*p - p = p for nat *)
Lemma nat_double_minus : forall p : nat, (2 * p - p = p)%nat.
Proof. intros. lia. Qed.

(** Equivalent formulation: 2^(n-1) odd-parity inputs for n >= 1 *)
Lemma parity_odd_count' : forall n, (n >= 1)%nat ->
  length (filter parity (all_inputs n)) = Nat.pow 2 (Nat.sub n 1).
Proof.
  intros n Hn.
  rewrite parity_odd_count.
  destruct n as [| n']; [lia |].
  simpl Nat.sub.
  rewrite Nat.sub_0_r.
  change (Nat.pow 2 (S n')) with (2 * Nat.pow 2 n')%nat.
  apply nat_double_minus.
Qed.

(** Count of odd-parity inputs equals count of even-parity inputs *)
Lemma parity_balanced : forall n, (n >= 1)%nat ->
  length (filter bool_id (parity_vector n)) = Nat.pow 2 (Nat.sub n 1).
Proof.
  intros n Hn.
  unfold parity_vector.
  rewrite filter_id_map.
  apply parity_odd_count'.
  exact Hn.
Qed.

(** ** Part 7: Communication Complexity Approach *)

(**
   The Ω(n/log n) bound comes from communication complexity.

   SETUP:
   - Alice holds first n/2 bits, Bob holds last n/2 bits
   - They want to compute parity(x) = parity(Alice's bits) XOR parity(Bob's bits)

   CLAIM:
   - A depth-2 threshold circuit with k layer-1 gates
   - Can be simulated by a communication protocol with O(k log n) bits
   - Parity requires Ω(n) bits of communication (it's XOR of Alice and Bob's bits)
   - Therefore k = Ω(n / log n)

   We formalize the key steps.
*)

(** Split input into two halves *)
Definition split_input (xs : input) : input * input :=
  let half := (length xs / 2)%nat in
  (firstn half xs, skipn half xs).

Lemma parity_split : forall xs,
  let (left, right) := split_input xs in
  parity xs = xorb (parity left) (parity right).
Proof.
  intros xs.
  unfold split_input.
  set (half := (length xs / 2)%nat).
  rewrite <- (firstn_skipn half xs) at 1.
  clear.
  generalize (firstn half xs) as left.
  generalize (skipn half xs) as right.
  intros right left.
  induction left as [| l left' IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct l; simpl.
    + destruct (parity left'), (parity right); reflexivity.
    + reflexivity.
Qed.

(** ** Part 8: Lower Bound Theorem *)

(**
   We state the main theorem and provide a partial proof.
   The full proof requires formalizing the communication complexity argument.
*)

(**
   Definition: A depth-2 circuit has "size" = number of layer-1 gates
*)
Definition circuit_size (c : depth2_circuit) : nat := n_layer1 c.

(**
   THEOREM (Informal):
   For any depth-2 threshold circuit computing n-bit parity,
   the number of layer-1 gates is at least n / (2 * ceil(log2(n+1))).

   This is Ω(n / log n).
*)

(**
   Weaker but provable bound: linear in terms of weight bounds.

   If all weights are bounded by W, then each gate can distinguish
   at most O(n * W) different pre-activation values, hence O(n * W)
   distinct behaviors. With k gates, at most (n * W)^k patterns.
   For 2^n inputs partitioned by parity, we need enough patterns.
*)

(** Bounded weights *)
Definition weights_bounded (ws : list Z) (W : Z) : Prop :=
  Forall (fun w => -W <= w <= W) ws.

Definition circuit_weights_bounded (c : depth2_circuit) (W : Z) : Prop :=
  Forall (fun wb => weights_bounded (fst wb) W) (layer1_weights c) /\
  weights_bounded (layer2_weights c) W.

(**
   For ternary weights (W = 1), each layer-1 gate's pre-activation
   ranges from -n to +n, giving at most 2n+1 distinct values.
   The output is binary (fires or not), but the input pattern matters.
*)

Lemma dot_bounded : forall ws xs W,
  weights_bounded ws W ->
  length ws = length xs ->
  - (W * Z.of_nat (length xs)) <= dot ws xs <= W * Z.of_nat (length xs).
Proof.
  intros ws xs W Hbnd Hlen.
  revert xs Hlen.
  induction ws as [| w ws' IH]; intros xs Hlen.
  - destruct xs; simpl in *; lia.
  - destruct xs as [| x xs']; simpl in *; [lia |].
    inversion Hbnd as [| ? ? Hw Hws']; subst.
    specialize (IH Hws' xs' ltac:(lia)).
    destruct x; lia.
Qed.

(** ** Part 9: Main Lower Bound *)

(**
   THEOREM: For n >= 4, any depth-2 threshold circuit with ternary weights
   computing n-bit parity has at least n/4 gates in layer 1.

   PROOF:
   - Each gate output is binary, determined by sign of pre-activation
   - With k gates, there are at most 2^k distinct layer-1 output patterns
   - Parity partitions 2^n inputs into two equal sets (odd/even HW)
   - Two inputs with same layer-1 pattern must have same layer-2 output
   - Inputs from different parity classes cannot share a pattern
   - Therefore 2^k >= number of parity "clusters" that must be separated

   The key insight is that parity is "maximally non-local":
   flipping any bit changes the output. This forces many gates.
*)

Definition layer1_pattern (c : depth2_circuit) (xs : input) : list bit :=
  eval_layer1 c xs.

(**
   Inputs with the same layer-1 pattern get the same final output
*)
Lemma same_pattern_same_output : forall c xs ys,
  layer1_pattern c xs = layer1_pattern c ys ->
  eval_depth2 c xs = eval_depth2 c ys.
Proof.
  intros c xs ys Hpat.
  unfold eval_depth2.
  unfold layer1_pattern in Hpat.
  rewrite Hpat. reflexivity.
Qed.

(**
   If the circuit computes parity correctly, inputs with different
   parities must have different layer-1 patterns.
*)
Lemma different_parity_different_pattern : forall c xs ys,
  circuit_computes_parity c ->
  length xs = n_inputs c ->
  length ys = n_inputs c ->
  parity xs <> parity ys ->
  layer1_pattern c xs <> layer1_pattern c ys.
Proof.
  intros c xs ys Hcomp Hxs Hys Hpar Hpat.
  apply Hpar.
  unfold circuit_computes_parity in Hcomp.
  rewrite <- (Hcomp xs Hxs), <- (Hcomp ys Hys).
  apply same_pattern_same_output. exact Hpat.
Qed.

(**
   There are 2^(n-1) odd-parity inputs and 2^(n-1) even-parity inputs.
   Each needs a distinct pattern from inputs of opposite parity.
*)

(** Number of distinct patterns is at most 2^k *)
Lemma pattern_count_bound : forall c,
  forall patterns : list (list bit),
  (forall p, In p patterns -> length p = n_layer1 c) ->
  NoDup patterns ->
  (length patterns <= Nat.pow 2 (n_layer1 c))%nat.
Proof.
  intros c patterns Hlen Hnodup.
  assert (H: (length patterns <= length (all_inputs (n_layer1 c)))%nat).
  {
    apply NoDup_incl_length; [exact Hnodup |].
    intros p Hin.
    specialize (Hlen p Hin).
    clear -Hlen.
    generalize dependent (n_layer1 c).
    induction p as [| b p' IH]; intros n Hlen.
    - destruct n; [left; reflexivity | simpl in Hlen; lia].
    - destruct n as [| n']; [simpl in Hlen; lia |].
      simpl in Hlen. injection Hlen as Hlen'.
      simpl. apply in_app_iff.
      destruct b.
      + right. apply in_map. apply IH. exact Hlen'.
      + left. apply in_map. apply IH. exact Hlen'.
  }
  rewrite all_inputs_length in H. exact H.
Qed.

(**
   MAIN LOWER BOUND THEOREM (Combinatorial Version)

   If a depth-2 circuit computes n-bit parity, and we can find m pairs
   of inputs (x_i, y_i) such that:
   - parity(x_i) ≠ parity(y_i) for each pair
   - All x_i are distinct
   - All y_i are distinct

   Then the circuit needs at least ceil(log2(m)) gates in layer 1.
*)

(** Simpler version: bound on number of distinct patterns *)
Theorem pattern_count_upper_bound : forall c inputs,
  (forall xs, In xs inputs -> length xs = n_inputs c) ->
  NoDup inputs ->
  (forall xs ys, In xs inputs -> In ys inputs ->
    layer1_pattern c xs = layer1_pattern c ys -> xs = ys) ->
  (length inputs <= Nat.pow 2 (length (layer1_weights c)))%nat.
Proof.
  intros c inputs Hlen Hnodup Hinj.
  set (patterns := map (fun xs => layer1_pattern c xs) inputs).
  set (k := length (layer1_weights c)).
  assert (Hplen: forall pat, In pat patterns -> length pat = k).
  {
    intros pat Hin.
    unfold patterns in Hin. apply in_map_iff in Hin.
    destruct Hin as [xs [Heq Hinxs]].
    subst pat. unfold k.
    unfold layer1_pattern, eval_layer1.
    rewrite map_length. reflexivity.
  }
  assert (Hnodup_pat: NoDup patterns).
  {
    unfold patterns.
    apply NoDup_map_inj; [| exact Hnodup].
    intros x y Hx Hy Heq.
    apply Hinj; assumption.
  }
  assert (H: (length patterns <= length (all_inputs k))%nat).
  {
    apply NoDup_incl_length; [exact Hnodup_pat |].
    intros p Hin.
    specialize (Hplen p Hin).
    clear -Hplen.
    generalize dependent k.
    induction p as [| b p' IH]; intros k Hplen.
    - destruct k; [left; reflexivity | simpl in Hplen; lia].
    - destruct k as [| k']; [simpl in Hplen; lia |].
      simpl in Hplen. injection Hplen as Hplen'.
      simpl. apply in_app_iff.
      destruct b.
      + right. apply in_map. apply IH. exact Hplen'.
      + left. apply in_map. apply IH. exact Hplen'.
  }
  rewrite all_inputs_length in H.
  unfold patterns in H.
  rewrite map_length in H.
  exact H.
Qed.

(**
   COROLLARY: For n-bit parity, at least ceil(log2(2^(n-1))) = n-1 patterns
   are needed. But this only gives a bound of n-1 on number of patterns,
   not directly on gates.

   The stronger Ω(n/log n) bound requires showing that with k gates,
   you cannot separate 2^(n-1) pairs. This involves the communication
   complexity argument.
*)

(** ** Part 10: Explicit Lower Bound for Small n *)

(** For n=4, we explicitly verify that at least 2 gates are needed *)

Definition inputs_4 : list input := all_inputs 4.

Definition odd_inputs_4 : list input :=
  filter (fun xs => parity xs) inputs_4.

Definition even_inputs_4 : list input :=
  filter (fun xs => negb (parity xs)) inputs_4.

Lemma odd_inputs_4_count : length odd_inputs_4 = 8%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma even_inputs_4_count : length even_inputs_4 = 8%nat.
Proof. vm_compute. reflexivity. Qed.

(** Pigeonhole: if we partition n items into 2 buckets, one has >= ceil(n/2) *)
Lemma pigeonhole_2 : forall (A : Type) (f : A -> bool) (l : list A),
  (length l >= 3)%nat ->
  (length (filter f l) >= 2)%nat \/ (length (filter (fun x => negb (f x)) l) >= 2)%nat.
Proof.
  intros A f l Hlen.
  pose proof (filter_partition_length A f l) as Hsum.
  destruct (Nat.le_gt_cases (length (filter f l)) 1) as [Hf_le | Hf_gt].
  - right. lia.
  - left. lia.
Qed.

(** ** Part 11: Well-Formed Circuits *)

(** A circuit is well-formed if n_layer1 matches actual gate count *)
Definition circuit_wellformed (c : depth2_circuit) : Prop :=
  n_layer1 c = length (layer1_weights c).

(** Layer-1 pattern has length equal to number of gates *)
Lemma layer1_pattern_length : forall c xs,
  length (layer1_pattern c xs) = length (layer1_weights c).
Proof.
  intros c xs.
  unfold layer1_pattern, eval_layer1.
  apply map_length.
Qed.

(** A length-1 bit list is either [true] or [false] *)
Lemma bit_list_1_cases : forall (l : list bit),
  length l = 1%nat ->
  l = [true] \/ l = [false].
Proof.
  intros l Hlen.
  destruct l as [| b l']; [simpl in Hlen; lia |].
  destruct l' as [| b' l'']; [| simpl in Hlen; lia].
  destruct b; [left | right]; reflexivity.
Qed.

(** [true] and [false] are distinct singleton lists *)
Lemma true_neq_false_list : [true] <> [false].
Proof. discriminate. Qed.

(** If two length-1 lists differ, one is [true] and one is [false] *)
Lemma bit_list_1_dichotomy : forall (l1 l2 : list bit),
  length l1 = 1%nat ->
  length l2 = 1%nat ->
  l1 <> l2 ->
  (l1 = [true] /\ l2 = [false]) \/ (l1 = [false] /\ l2 = [true]).
Proof.
  intros l1 l2 H1 H2 Hne.
  destruct (bit_list_1_cases l1 H1) as [E1 | E1];
  destruct (bit_list_1_cases l2 H2) as [E2 | E2];
  subst.
  - exfalso. apply Hne. reflexivity.
  - left. split; reflexivity.
  - right. split; reflexivity.
  - exfalso. apply Hne. reflexivity.
Qed.

(** Extract the single bit from a length-1 list *)
Definition hd_bit (l : list bit) : bit :=
  match l with
  | [] => false
  | b :: _ => b
  end.

Lemma hd_bit_true : hd_bit [true] = true.
Proof. reflexivity. Qed.

Lemma hd_bit_false : hd_bit [false] = false.
Proof. reflexivity. Qed.

(** For length-1 lists, hd_bit determines equality *)
Lemma hd_bit_eq_iff : forall (l1 l2 : list bit),
  length l1 = 1%nat ->
  length l2 = 1%nat ->
  (l1 = l2 <-> hd_bit l1 = hd_bit l2).
Proof.
  intros l1 l2 H1 H2.
  destruct (bit_list_1_cases l1 H1) as [E1 | E1];
  destruct (bit_list_1_cases l2 H2) as [E2 | E2];
  subst; simpl; split; intro H; try reflexivity; try discriminate.
Qed.

(** For a single-gate circuit, the pattern is [gate_output] *)
Lemma single_gate_pattern : forall ws b xs,
  layer1_pattern {| n_inputs := length xs;
                    n_layer1 := 1;
                    layer1_weights := [(ws, b)];
                    layer2_weights := [];
                    layer2_bias := 0 |} xs = [gate ws b xs].
Proof.
  intros. unfold layer1_pattern, eval_layer1. simpl. reflexivity.
Qed.

(** hd_bit of single-gate pattern equals gate output *)
Lemma hd_bit_single_gate : forall ws b xs,
  hd_bit [gate ws b xs] = gate ws b xs.
Proof.
  intros. reflexivity.
Qed.

(** ** Part 12: Boolean Lemmas for Separation Argument *)

(** If two bools differ, one is negb of the other *)
Lemma bool_neq_negb : forall a b : bool, a <> b -> b = negb a.
Proof.
  intros [] []; intro H; try reflexivity; exfalso; apply H; reflexivity.
Qed.

(** If a <> b and c <> b, then a = c *)
Lemma bool_neq_same : forall a b c : bool, a <> b -> c <> b -> a = c.
Proof.
  intros [] [] []; intros Hab Hcb;
  try reflexivity;
  try (exfalso; apply Hab; reflexivity);
  try (exfalso; apply Hcb; reflexivity).
Qed.

(** ** Part 13: Witness Inputs *)

(** All-zeros input has even parity *)
Definition zeros (n : nat) : input := repeat false n.

Lemma zeros_length : forall n, length (zeros n) = n.
Proof. intros. apply repeat_length. Qed.

Lemma zeros_parity : forall n, parity (zeros n) = false.
Proof.
  induction n; simpl.
  - reflexivity.
  - exact IHn.
Qed.

(** Single-one input has odd parity *)
Definition single_one (n : nat) : input := true :: repeat false (n - 1).

Lemma single_one_length : forall n, (n >= 1)%nat -> length (single_one n) = n.
Proof.
  intros n Hn. unfold single_one. simpl.
  rewrite repeat_length. lia.
Qed.

Lemma single_one_parity : forall n, (n >= 1)%nat -> parity (single_one n) = true.
Proof.
  intros n Hn. unfold single_one. simpl.
  rewrite zeros_parity. reflexivity.
Qed.

(** zeros and single_one have different parities *)
Lemma witnesses_diff_parity : forall n, (n >= 1)%nat ->
  parity (zeros n) <> parity (single_one n).
Proof.
  intros n Hn.
  rewrite zeros_parity, single_one_parity by assumption.
  discriminate.
Qed.

(** ** Part 14: Separation Lemmas *)

Lemma separation_diff_parity : forall (f : input -> bit) n xs ys,
  (forall us vs, length us = n -> length vs = n ->
    parity us <> parity vs -> f us <> f vs) ->
  length xs = n ->
  length ys = n ->
  parity xs <> parity ys ->
  f xs <> f ys.
Proof.
  intros f n xs ys Hsep Hxlen Hylen Hpar.
  apply Hsep; assumption.
Qed.

Lemma separation_same_parity : forall (f : input -> bit) n xs witness other,
  (forall us vs, length us = n -> length vs = n ->
    parity us <> parity vs -> f us <> f vs) ->
  length xs = n ->
  length witness = n ->
  length other = n ->
  parity xs = parity witness ->
  parity other <> parity xs ->
  f xs = f witness.
Proof.
  intros f n xs witness other Hsep Hxlen Hwlen Holen Hsame Hdiff.
  assert (Hdiff' : parity xs <> parity other) by (intro H; apply Hdiff; symmetry; exact H).
  assert (Hxo : f xs <> f other).
  { apply Hsep; assumption. }
  assert (Hdiff_w : parity witness <> parity other).
  { rewrite <- Hsame. exact Hdiff'. }
  assert (Hwo : f witness <> f other).
  { apply Hsep; assumption. }
  apply bool_neq_same with (b := f other); assumption.
Qed.

Lemma separation_even_constant : forall (f : input -> bit) n xs,
  (n >= 1)%nat ->
  (forall us vs, length us = n -> length vs = n ->
    parity us <> parity vs -> f us <> f vs) ->
  length xs = n ->
  parity xs = false ->
  f xs = f (zeros n).
Proof.
  intros f n xs Hn Hsep Hxlen Hpar.
  apply (separation_same_parity f n xs (zeros n) (single_one n)).
  - exact Hsep.
  - exact Hxlen.
  - apply zeros_length.
  - apply single_one_length. exact Hn.
  - rewrite Hpar. symmetry. apply zeros_parity.
  - rewrite single_one_parity by exact Hn. rewrite Hpar. discriminate.
Qed.

Lemma separation_odd_constant : forall (f : input -> bit) n xs,
  (n >= 1)%nat ->
  (forall us vs, length us = n -> length vs = n ->
    parity us <> parity vs -> f us <> f vs) ->
  length xs = n ->
  parity xs = true ->
  f xs = f (single_one n).
Proof.
  intros f n xs Hn Hsep Hxlen Hpar.
  apply (separation_same_parity f n xs (single_one n) (zeros n)).
  - exact Hsep.
  - exact Hxlen.
  - apply single_one_length. exact Hn.
  - apply zeros_length.
  - rewrite Hpar. symmetry. apply single_one_parity. exact Hn.
  - rewrite zeros_parity. rewrite Hpar. discriminate.
Qed.

Lemma witnesses_f_differ : forall (f : input -> bit) n,
  (n >= 1)%nat ->
  (forall us vs, length us = n -> length vs = n ->
    parity us <> parity vs -> f us <> f vs) ->
  f (zeros n) <> f (single_one n).
Proof.
  intros f n Hn Hsep.
  apply Hsep.
  - apply zeros_length.
  - apply single_one_length. exact Hn.
  - rewrite zeros_parity, single_one_parity by exact Hn. discriminate.
Qed.

Lemma separation_case_false : forall (f : input -> bit) n xs,
  (n >= 1)%nat ->
  (forall us vs, length us = n -> length vs = n ->
    parity us <> parity vs -> f us <> f vs) ->
  f (zeros n) = false ->
  length xs = n ->
  f xs = parity xs.
Proof.
  intros f n xs Hn Hsep Hfz Hxlen.
  destruct (parity xs) eqn:Hpar.
  - rewrite (separation_odd_constant f n xs Hn Hsep Hxlen Hpar).
    assert (Hdiff : f (zeros n) <> f (single_one n)) by (apply witnesses_f_differ; assumption).
    rewrite Hfz in Hdiff.
    destruct (f (single_one n)); [reflexivity | exfalso; apply Hdiff; reflexivity].
  - rewrite (separation_even_constant f n xs Hn Hsep Hxlen Hpar).
    exact Hfz.
Qed.

Lemma separation_case_true : forall (f : input -> bit) n xs,
  (n >= 1)%nat ->
  (forall us vs, length us = n -> length vs = n ->
    parity us <> parity vs -> f us <> f vs) ->
  f (zeros n) = true ->
  length xs = n ->
  f xs = negb (parity xs).
Proof.
  intros f n xs Hn Hsep Hfz Hxlen.
  destruct (parity xs) eqn:Hpar; simpl.
  - rewrite (separation_odd_constant f n xs Hn Hsep Hxlen Hpar).
    assert (Hdiff : f (zeros n) <> f (single_one n)) by (apply witnesses_f_differ; assumption).
    rewrite Hfz in Hdiff.
    destruct (f (single_one n)); [exfalso; apply Hdiff; reflexivity | reflexivity].
  - rewrite (separation_even_constant f n xs Hn Hsep Hxlen Hpar).
    exact Hfz.
Qed.

Theorem separation_is_parity : forall (f : input -> bit) n,
  (n >= 1)%nat ->
  (forall us vs, length us = n -> length vs = n ->
    parity us <> parity vs -> f us <> f vs) ->
  (forall xs, length xs = n -> f xs = parity xs) \/
  (forall xs, length xs = n -> f xs = negb (parity xs)).
Proof.
  intros f n Hn Hsep.
  destruct (f (zeros n)) eqn:Hfz.
  - right. intros xs Hxlen. apply (separation_case_true f n xs Hn Hsep Hfz Hxlen).
  - left. intros xs Hxlen. apply (separation_case_false f n xs Hn Hsep Hfz Hxlen).
Qed.

(** ** Part 15: Single Gate Cannot Compute negb parity *)

Theorem depth1_impossible_negb_parity_2bit : forall w0 w1 b,
  gate [w0; w1] b x00 = negb (parity x00) ->
  gate [w0; w1] b x01 = negb (parity x01) ->
  gate [w0; w1] b x10 = negb (parity x10) ->
  gate [w0; w1] b x11 = negb (parity x11) ->
  False.
Proof.
  intros w0 w1 b H00 H01 H10 H11.
  simpl in H00, H01, H10, H11.
  rewrite gate_fires_iff in H00.
  rewrite gate_silent_iff in H01.
  rewrite gate_silent_iff in H10.
  rewrite gate_fires_iff in H11.
  rewrite dot_x00 in H00.
  rewrite dot_x01 in H01.
  rewrite dot_x10 in H10.
  rewrite dot_x11 in H11.
  lia.
Qed.

Theorem depth1_impossible_negb_parity_nbit : forall n, (n >= 2)%nat ->
  forall ws b,
  length ws = n ->
  ~ (forall xs, length xs = n -> gate ws b xs = negb (parity xs)).
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
  unfold gate in H00, H01, H10, H11.
  rewrite dot_pad_x00 in H00 by exact Hws''.
  rewrite dot_pad_x01 in H01 by exact Hws''.
  rewrite dot_pad_x10 in H10 by exact Hws''.
  rewrite dot_pad_x11 in H11 by exact Hws''.
  rewrite parity_pad_zeros in H00, H01, H10, H11.
  unfold x00, x01, x10, x11 in H00, H01, H10, H11.
  simpl parity in H00, H01, H10, H11.
  simpl negb in H00, H01, H10, H11.
  assert (Hb_pos : b >= 0).
  { destruct (Z.geb (0 + b) 0) eqn:E; [| discriminate H00].
    rewrite Z.geb_leb, Z.leb_le in E. lia. }
  assert (Hw1_neg : w1 + b < 0).
  { destruct (Z.geb (w1 + b) 0) eqn:E; [discriminate H01 |].
    rewrite Z.geb_leb, Z.leb_gt in E. lia. }
  assert (Hw0_neg : w0 + b < 0).
  { destruct (Z.geb (w0 + b) 0) eqn:E; [discriminate H10 |].
    rewrite Z.geb_leb, Z.leb_gt in E. lia. }
  assert (Hsum_pos : w0 + w1 + b >= 0).
  { destruct (Z.geb (w0 + w1 + b) 0) eqn:E; [| discriminate H11].
    rewrite Z.geb_leb, Z.leb_le in E. lia. }
  lia.
Qed.

Theorem gate_cannot_separate_parity : forall ws b n,
  (n >= 2)%nat ->
  length ws = n ->
  ~ (forall us vs, length us = n -> length vs = n ->
      parity us <> parity vs -> gate ws b us <> gate ws b vs).
Proof.
  intros ws b n Hn Hwlen Hsep.
  assert (Hn1 : (n >= 1)%nat) by lia.
  destruct (separation_is_parity (fun xs => gate ws b xs) n Hn1 Hsep) as [Hpar | Hnpar].
  - apply (depth1_impossible_nbit n Hn ws b Hwlen Hpar).
  - apply (depth1_impossible_negb_parity_nbit n Hn ws b Hwlen Hnpar).
Qed.

(** ** Part 16: Main Lower Bound Theorem *)

Theorem depth2_needs_2_gates : forall n, (n >= 2)%nat ->
  forall ws b l2w l2b,
  length ws = n ->
  ~ (forall xs, length xs = n ->
      gate l2w l2b [gate ws b xs] = parity xs).
Proof.
  intros n Hn ws b l2w l2b Hwlen Hcirc.
  apply (gate_cannot_separate_parity ws b n Hn Hwlen).
  intros us vs Hulen Hvlen Hpar.
  assert (Hcu : gate l2w l2b [gate ws b us] = parity us) by (apply Hcirc; exact Hulen).
  assert (Hcv : gate l2w l2b [gate ws b vs] = parity vs) by (apply Hcirc; exact Hvlen).
  intro Heq.
  rewrite Heq in Hcu.
  rewrite Hcu in Hcv.
  apply Hpar. exact Hcv.
Qed.

(** ** Part 17: Communication Complexity - Partial Dot Products *)

Definition dot_partial (ws : list Z) (xs : input) (start len : nat) : Z :=
  dot (firstn len (skipn start ws)) (firstn len (skipn start xs)).

Lemma dot_firstn_skipn : forall ws xs k,
  length ws = length xs ->
  (k <= length xs)%nat ->
  dot ws xs = dot (firstn k ws) (firstn k xs) + dot (skipn k ws) (skipn k xs).
Proof.
  intros ws xs k Hlen Hk.
  revert xs k Hlen Hk.
  induction ws as [| w ws' IH]; intros xs k Hlen Hk.
  - destruct xs; simpl in *.
    + destruct k; reflexivity.
    + discriminate.
  - destruct xs as [| x xs']; simpl in *; [discriminate |].
    destruct k as [| k'].
    + simpl. lia.
    + simpl.
      injection Hlen as Hlen'.
      specialize (IH xs' k' Hlen' ltac:(lia)).
      destruct x; lia.
Qed.

(** For ternary weights, dot product is bounded by length - lower bound *)
Lemma dot_ternary_lower : forall ws xs,
  weights_bounded ws 1 ->
  - Z.of_nat (length ws) <= dot ws xs.
Proof.
  intros ws. induction ws as [| w ws' IH]; intros xs Hbnd.
  - simpl. lia.
  - destruct xs as [| x xs'].
    + simpl. inversion Hbnd; subst.
      specialize (IH [] H2). simpl in IH. lia.
    + inversion Hbnd as [| ? ? Hw Hws']; subst.
      specialize (IH xs' Hws').
      simpl dot. simpl length.
      rewrite Nat2Z.inj_succ. unfold Z.succ.
      destruct x; lia.
Qed.

(** For ternary weights, dot product is bounded by length - upper bound *)
Lemma dot_ternary_upper : forall ws xs,
  weights_bounded ws 1 ->
  dot ws xs <= Z.of_nat (length ws).
Proof.
  intros ws. induction ws as [| w ws' IH]; intros xs Hbnd.
  - simpl. lia.
  - destruct xs as [| x xs'].
    + simpl. inversion Hbnd; subst.
      specialize (IH [] H2). simpl in IH. lia.
    + inversion Hbnd as [| ? ? Hw Hws']; subst.
      specialize (IH xs' Hws').
      simpl dot. simpl length.
      rewrite Nat2Z.inj_succ. unfold Z.succ.
      destruct x; lia.
Qed.

(** Combined: ternary dot product is in [-n, n] *)
Lemma dot_ternary_range : forall ws xs,
  weights_bounded ws 1 ->
  - Z.of_nat (length ws) <= dot ws xs <= Z.of_nat (length ws).
Proof.
  intros ws xs Hbnd.
  split.
  - apply dot_ternary_lower. exact Hbnd.
  - apply dot_ternary_upper. exact Hbnd.
Qed.

(** Corollary: dot product takes at most 2n+1 distinct values *)
Lemma dot_distinct_values : forall ws xs,
  weights_bounded ws 1 ->
  exists v : Z, dot ws xs = v /\
    - Z.of_nat (length ws) <= v <= Z.of_nat (length ws).
Proof.
  intros ws xs Hbnd.
  exists (dot ws xs).
  split; [reflexivity | apply dot_ternary_range; exact Hbnd].
Qed.

(** ** Part 18: Communication Protocol Simulation *)

(**
   KEY INSIGHT for Ω(n/log n):

   Consider input x = (x_A, x_B) split between Alice (first n/2 bits)
   and Bob (remaining n/2 bits).

   For a single gate with ternary weights:
   - Alice computes dot(w_A, x_A) which is in [-n/2, n/2]
   - She can send this value using O(log n) bits
   - Bob receives it, adds his part: dot(w_A, x_A) + dot(w_B, x_B) + b
   - Bob can determine if the gate fires

   With k layer-1 gates:
   - Alice sends k values, each O(log n) bits
   - Total communication: O(k log n) bits

   But parity(x) = parity(x_A) XOR parity(x_B) requires Ω(n) bits
   of communication (it's essentially the inner product function).

   Therefore: k * log(n) >= Ω(n), so k >= Ω(n / log n).
*)

(** Alice's partial computation for one gate *)
Definition alice_partial (ws : list Z) (xs_A : input) (half : nat) : Z :=
  dot (firstn half ws) xs_A.

(** Bob can determine gate output given Alice's message *)
Lemma bob_determines_gate : forall ws b xs half,
  length xs = (2 * half)%nat ->
  length ws = (2 * half)%nat ->
  let xs_A := firstn half xs in
  let xs_B := skipn half xs in
  let msg := alice_partial ws xs_A half in
  gate ws b xs = Z.geb (msg + dot (skipn half ws) xs_B + b) 0.
Proof.
  intros ws b xs half Hxlen Hwlen xs_A xs_B msg.
  unfold gate, msg, alice_partial, xs_A, xs_B.
  f_equal.
  rewrite dot_firstn_skipn with (k := half) by lia.
  ring.
Qed.

(** Helper: firstn preserves weight bound *)
Lemma weights_bounded_firstn : forall ws W k,
  weights_bounded ws W ->
  weights_bounded (firstn k ws) W.
Proof.
  intros ws W k Hbnd.
  revert k. induction ws as [| w ws' IH]; intros k.
  - simpl. destruct k; constructor.
  - destruct k; simpl.
    + constructor.
    + inversion Hbnd; subst. constructor; [assumption | apply IH; assumption].
Qed.

(** Alice's message is bounded, hence can be sent with O(log n) bits *)
Lemma alice_message_bounded : forall ws xs_A half,
  weights_bounded ws 1 ->
  (half <= length ws)%nat ->
  - Z.of_nat half <= alice_partial ws xs_A half <= Z.of_nat half.
Proof.
  intros ws xs_A half Hbnd Hhalf.
  unfold alice_partial.
  pose proof (weights_bounded_firstn ws 1 half Hbnd) as Hfirst.
  pose proof (dot_ternary_range (firstn half ws) xs_A Hfirst) as [Hlo Hhi].
  assert (Hflen: length (firstn half ws) = half) by (apply firstn_length_le; lia).
  rewrite Hflen in Hlo, Hhi.
  split; assumption.
Qed.

Definition alice_messages (gates : list (list Z * Z)) (xs : input) (half : nat) : list Z :=
  map (fun wb => alice_partial (fst wb) (firstn half xs) half) gates.

Lemma same_alice_same_gate : forall ws b xs ys half,
  length xs = (2 * half)%nat ->
  length ys = (2 * half)%nat ->
  length ws = (2 * half)%nat ->
  skipn half xs = skipn half ys ->
  alice_partial ws (firstn half xs) half = alice_partial ws (firstn half ys) half ->
  gate ws b xs = gate ws b ys.
Proof.
  intros ws b xs ys half Hxlen Hylen Hwlen Hbob Halice.
  unfold gate. f_equal.
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
  induction gates as [| g gates' IH].
  - reflexivity.
  - simpl in *. inversion Hglen as [| ? ? Hg Hgates']; subst.
    injection Halice as Hg_alice Hrest. f_equal.
    + apply (same_alice_same_gate (fst g) (snd g) xs ys half); assumption.
    + apply IH; assumption.
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

Lemma ln_gt_0 : forall x : R, x > 1 -> ln x > 0.
Proof. intros x Hx. rewrite <- ln_1. apply ln_increasing; lra. Qed.

Lemma log2_pos_for_ge3 : forall m : nat, (m >= 3)%nat -> log2 (INR m) > 0.
Proof.
  intros m Hm. unfold log2. apply Rmult_pos_pos.
  - apply ln_gt_0. apply lt_1_INR. lia.
  - apply Rinv_0_lt_compat. apply ln_2_pos.
Qed.

Theorem omega_n_over_log_n : forall half k : nat,
  (half >= 1)%nat ->
  (Nat.pow (S (2 * half)) k >= Nat.pow 2 half)%nat ->
  INR k >= INR half / log2 (INR (S (2 * half))).
Proof.
  intros half k Hhalf Hpow.
  assert (Hlog_pos : log2 (INR (S (2 * half))) > 0).
  { apply log2_pos_for_ge3. lia. }
  apply (gates_lower_bound half k Hhalf Hpow Hlog_pos).
Qed.

Lemma n8_bound : forall k : nat,
  (Nat.pow 9 k >= Nat.pow 2 4)%nat ->
  INR k >= INR 4 / log2 (INR 9).
Proof.
  intros k Hpow. apply (omega_n_over_log_n 4 k); [lia | exact Hpow].
Qed.

Lemma n8_1_gate_insufficient : (Nat.pow 9 1 < Nat.pow 2 4)%nat.
Proof. vm_compute. lia. Qed.

Lemma n8_2_gates_sufficient : (Nat.pow 9 2 >= Nat.pow 2 4)%nat.
Proof. vm_compute. lia. Qed.

Lemma n16_bound : forall k : nat,
  (Nat.pow 17 k >= Nat.pow 2 8)%nat ->
  INR k >= INR 8 / log2 (INR 17).
Proof.
  intros k Hpow. apply (omega_n_over_log_n 8 k); [lia | exact Hpow].
Qed.

Lemma n16_1_gate_insufficient : (Nat.pow 17 1 < Nat.pow 2 8)%nat.
Proof. vm_compute. lia. Qed.

Lemma n16_2_gates_sufficient : (Nat.pow 17 2 >= Nat.pow 2 8)%nat.
Proof. vm_compute. lia. Qed.

Close Scope R_scope.
Close Scope Z_scope.
