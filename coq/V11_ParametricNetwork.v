(** * Parametric Parity Network Construction *)

(**
   Constructs a verified parity network for ANY input size n.

   Architecture:
   - Layer 1: (n+1) neurons detecting "HW >= k" for k = 0, 1, ..., n
   - Layer 2: 1 neuron with alternating weights, fires iff HW is even
   - Output: Negates L2 to get parity
*)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(** ** Definitions *)

Definition bit := bool.

Fixpoint hamming_weight (xs : list bit) : nat :=
  match xs with
  | [] => 0
  | true :: xs' => S (hamming_weight xs')
  | false :: xs' => hamming_weight xs'
  end.

Fixpoint parity (xs : list bit) : bit :=
  match xs with
  | [] => false
  | x :: xs' => xorb x (parity xs')
  end.

Definition heaviside (x : Z) : bit := if Z.geb x 0 then true else false.

(** ** Key Property: Parity-based detection *)

(**
   The key insight is simple:
   - We can detect if HW is even or odd
   - Parity = Nat.odd HW
   - So output = negb (Nat.even HW) = parity
*)

(** ** Network Components *)

(** L1: Threshold detectors *)
Fixpoint ones (n : nat) : list Z :=
  match n with O => [] | S n' => 1 :: ones n' end.

Fixpoint dot (ws : list Z) (xs : list bit) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' => (if x then w else 0) + dot ws' xs'
  end.

Lemma Znat_S : forall n, Z.of_nat (S n) = 1 + Z.of_nat n.
Proof. intro. lia. Qed.

Lemma dot_ones_eq_hw : forall xs,
  dot (ones (length xs)) xs = Z.of_nat (hamming_weight xs).
Proof.
  induction xs as [| x xs' IH]; simpl.
  - reflexivity.
  - destruct x.
    + simpl. rewrite IH. symmetry. apply Znat_S.
    + simpl. rewrite IH. reflexivity.
Qed.

(** L1 neuron k fires iff HW >= k *)
Definition L1_fires (k : nat) (xs : list bit) : bit :=
  (k <=? hamming_weight xs)%nat.

(** L2: Alternating sum detector *)
Definition L2_fires (h : nat) : bit :=
  Nat.even h.

Lemma L2_correct : forall h,
  L2_fires h = Nat.even h.
Proof. reflexivity. Qed.

(** Output: Negation *)
Definition output (l2 : bit) : bit := negb l2.

(** ** Complete Network *)

Definition parity_network (xs : list bit) : bit :=
  output (L2_fires (hamming_weight xs)).

(** ** Main Theorem *)

Lemma odd_S : forall n, Nat.odd (S n) = negb (Nat.odd n).
Proof.
  intros n. unfold Nat.odd.
  induction n.
  - reflexivity.
  - change (Nat.even (S (S n))) with (Nat.even n).
    rewrite IHn. rewrite Bool.negb_involutive. reflexivity.
Qed.

Lemma parity_is_odd_hw : forall xs,
  parity xs = Nat.odd (hamming_weight xs).
Proof.
  induction xs as [| x xs' IH]; simpl.
  - reflexivity.
  - destruct x; simpl.
    + rewrite IH. rewrite odd_S. reflexivity.
    + exact IH.
Qed.

Theorem parity_network_correct : forall xs,
  parity_network xs = parity xs.
Proof.
  intros xs.
  unfold parity_network, output, L2_fires.
  rewrite parity_is_odd_hw.
  unfold Nat.odd.
  destruct (Nat.even (hamming_weight xs)); reflexivity.
Qed.

(** ** Concrete Implementation *)

(**
   The abstract network above shows the LOGIC is correct:
   - L2_fires h = Nat.even h
   - output (L2_fires h) = negb (Nat.even h) = Nat.odd h = parity

   A CONCRETE implementation would use:

   Layer 1: (n+1) neurons
   - Neuron k: weights = [1,1,...,1] (n ones), bias = -k
   - Fires iff sum(inputs) - k >= 0 iff HW >= k

   Layer 2: 1 neuron
   - Weights = [1,-1,1,-1,...] (alternating, n+1 values)
   - Bias = -1
   - Pre-act = sum of ((-1)^k * [HW >= k]) - 1
   - For HW = h: = (alternating sum of h+1 ones) - 1
                 = (1 if h even, 0 if h odd) - 1
                 = (0 if h even, -1 if h odd)
   - Fires iff pre-act >= 0 iff h even

   Output: 1 neuron
   - Weight = -1, bias = 0
   - Fires iff L2 output = 0 iff h odd iff parity = 1
*)

(** Concrete neuron implementation *)
Definition neuron (ws : list Z) (b : Z) (xs : list bit) : bit :=
  heaviside (dot ws xs + b).

(** Alternating weights *)
Fixpoint alt_weights (n : nat) (sign : bool) : list Z :=
  match n with
  | O => []
  | S n' => (if sign then 1 else -1) :: alt_weights n' (negb sign)
  end.

(** L1 output: list of [HW >= 0, HW >= 1, ..., HW >= n] *)
Definition L1_concrete (n : nat) (xs : list bit) : list bit :=
  map (fun k => neuron (ones (length xs)) (- Z.of_nat k) xs) (seq 0 (S n)).

(** L2 concrete *)
Definition L2_concrete (n : nat) (xs : list bit) : bit :=
  neuron (alt_weights (S n) true) (-1) (L1_concrete n xs).

(** Output concrete *)
Definition output_concrete (l2 : bit) : bit :=
  heaviside (- if l2 then 1 else 0).

(** Full concrete network *)
Definition parity_concrete (n : nat) (xs : list bit) : bit :=
  output_concrete (L2_concrete n xs).

(** ** Lemmas for concrete implementation *)

(** L1 neuron k fires iff HW >= k *)
Lemma L1_neuron_correct : forall k xs,
  neuron (ones (length xs)) (- Z.of_nat k) xs = (k <=? hamming_weight xs)%nat.
Proof.
  intros k xs.
  unfold neuron, heaviside.
  rewrite dot_ones_eq_hw.
  set (h := hamming_weight xs).
  destruct (Nat.le_gt_cases k h) as [Hle | Hgt].
  - (* k <= h, so neuron fires *)
    assert (Hgeb: (Z.of_nat h + - Z.of_nat k >=? 0) = true).
    { apply Z.geb_le. lia. }
    rewrite Hgeb.
    symmetry. apply Nat.leb_le. exact Hle.
  - (* k > h, so neuron doesn't fire *)
    assert (Hgeb: (Z.of_nat h + - Z.of_nat k >=? 0) = false).
    { destruct (Z.of_nat h + - Z.of_nat k >=? 0) eqn:E; auto.
      apply Z.geb_le in E. lia. }
    rewrite Hgeb.
    symmetry. apply Nat.leb_gt. exact Hgt.
Qed.

(** L1_concrete produces threshold indicators *)
Lemma L1_concrete_nth : forall n k xs,
  (k <= n)%nat ->
  nth k (L1_concrete n xs) false = (k <=? hamming_weight xs)%nat.
Proof.
  intros n k xs Hk.
  unfold L1_concrete.
  remember (fun j : nat => neuron (ones (length xs)) (- Z.of_nat j) xs) as f.
  assert (Hseq: nth k (seq 0%nat (S n)) 0%nat = k).
  { apply seq_nth. lia. }
  assert (Hbnd: (k < length (seq 0%nat (S n)))%nat).
  { rewrite seq_length. lia. }
  erewrite nth_indep by (rewrite map_length; exact Hbnd).
  rewrite (map_nth f (seq 0%nat (S n)) 0%nat).
  rewrite Hseq. subst f. simpl.
  apply L1_neuron_correct.
Qed.

Lemma L1_concrete_length : forall n xs,
  length (L1_concrete n xs) = S n.
Proof.
  intros. unfold L1_concrete.
  rewrite map_length, seq_length. reflexivity.
Qed.

(** Alternating dot product with threshold pattern *)
Lemma alt_weights_length : forall n sign,
  length (alt_weights n sign) = n.
Proof.
  induction n; intros; simpl; auto.
Qed.

(** L1 concrete equals abstract threshold list *)
Lemma L1_concrete_eq : forall n xs,
  L1_concrete n xs = map (fun k => (k <=? hamming_weight xs)%nat) (seq 0%nat (S n)).
Proof.
  intros n xs.
  apply nth_ext with (d := false) (d' := false).
  - rewrite L1_concrete_length, map_length, seq_length. reflexivity.
  - intros i Hi.
    rewrite L1_concrete_length in Hi.
    rewrite L1_concrete_nth by lia.
    assert (Hbnd: (i < length (seq 0%nat (S n)))%nat) by (rewrite seq_length; lia).
    rewrite nth_indep with (d' := (0%nat <=? hamming_weight xs)%nat)
      by (rewrite map_length; exact Hbnd).
    rewrite (map_nth (fun k => (k <=? hamming_weight xs)%nat) (seq 0%nat (S n)) 0%nat).
    rewrite seq_nth by lia. simpl. reflexivity.
Qed.

(** Key insight: alternating sum of first (h+1) ones starting with +1 *)
(** 1 - 1 + 1 - 1 + ... for h+1 terms = 1 if h even, 0 if h odd *)

Fixpoint alt_sum_first (h : nat) : Z :=
  match h with
  | O => 1
  | S h' => (if Nat.even h then 1 else -1) + alt_sum_first h'
  end.

Lemma even_S : forall n, Nat.even (S n) = negb (Nat.even n).
Proof.
  induction n.
  - reflexivity.
  - simpl in *. rewrite IHn. symmetry. apply Bool.negb_involutive.
Qed.

Lemma alt_sum_first_correct : forall h,
  alt_sum_first h = if Nat.even h then 1 else 0.
Proof.
  induction h as [| h' IH].
  - reflexivity.
  - change (alt_sum_first (S h')) with ((if Nat.even (S h') then 1 else -1) + alt_sum_first h').
    rewrite IH. rewrite even_S.
    destruct (Nat.even h'); reflexivity.
Qed.

(** Dot product as fold_left *)
Lemma dot_fold_aux : forall ws xs acc,
  fold_left Z.add (map (fun p : Z * bit => if snd p then fst p else 0) (combine ws xs)) acc =
  acc + dot ws xs.
Proof.
  induction ws as [| w ws' IH]; intros [| x xs'] acc; simpl; try lia.
  rewrite IH. destruct x; lia.
Qed.

Lemma dot_alt_ind : forall ws xs,
  dot ws xs = fold_left Z.add (map (fun p : Z * bit => if snd p then fst p else 0) (combine ws xs)) 0.
Proof.
  intros. rewrite dot_fold_aux. lia.
Qed.

(** Dot with appended false is unchanged (when lengths match) *)
Lemma dot_app_false : forall ws w xs,
  length ws = length xs ->
  dot (ws ++ [w]) (xs ++ [false]) = dot ws xs.
Proof.
  induction ws as [| w' ws' IHws]; intros w xs Hlen.
  - destruct xs; simpl in *; try discriminate. reflexivity.
  - destruct xs as [| x xs']; simpl in *; try discriminate.
    injection Hlen as Hlen'. rewrite IHws by exact Hlen'. reflexivity.
Qed.

Lemma dot_cons : forall w ws x xs,
  dot (w :: ws) (x :: xs) = (if x then w else 0) + dot ws xs.
Proof. reflexivity. Qed.

Lemma alt_weights_S : forall n sign,
  alt_weights (S n) sign = (if sign then 1 else -1) :: alt_weights n (negb sign).
Proof. reflexivity. Qed.

Lemma repeat_S : forall A (x : A) n,
  repeat x (S n) = x :: repeat x n.
Proof. reflexivity. Qed.

Lemma negb_true : negb true = false. Proof. reflexivity. Qed.
Lemma negb_false : negb false = true. Proof. reflexivity. Qed.

Lemma if_true : forall A (x y : A), (if true then x else y) = x. Proof. reflexivity. Qed.
Lemma if_false : forall A (x y : A), (if false then x else y) = y. Proof. reflexivity. Qed.

Lemma alt_sum_first_S : forall h,
  alt_sum_first (S h) = (if Nat.even (S h) then 1 else -1) + alt_sum_first h.
Proof. reflexivity. Qed.

Lemma dot_alt_prefix : forall h sign,
  dot (alt_weights (S h) sign) (repeat true (S h)) =
  if sign then alt_sum_first h else - alt_sum_first h.
Proof.
  induction h as [| h' IH]; intros sign.
  - destruct sign; reflexivity.
  - rewrite alt_weights_S, repeat_S, dot_cons.
    destruct sign.
    + rewrite negb_true.
      change ((if true then 1 else 0) + dot (alt_weights (S h') false) (repeat true (S h')))
        with (1 + dot (alt_weights (S h') false) (repeat true (S h'))).
      rewrite (IH false).
      rewrite alt_sum_first_S, even_S, alt_sum_first_correct.
      destruct (Nat.even h'); reflexivity.
    + rewrite negb_false.
      change ((if true then (-1) else 0) + dot (alt_weights (S h') true) (repeat true (S h')))
        with ((-1) + dot (alt_weights (S h') true) (repeat true (S h'))).
      rewrite (IH true).
      rewrite alt_sum_first_S, even_S, alt_sum_first_correct.
      destruct (Nat.even h'); reflexivity.
Qed.

Lemma nth_repeat' : forall A (x : A) n m d, (n < m)%nat -> nth n (repeat x m) d = x.
Proof.
  intros A x n m d Hnm.
  rewrite nth_indep with (d' := x) by (rewrite repeat_length; lia).
  apply nth_repeat.
Qed.

Lemma threshold_map_split : forall n h,
  (h <= n)%nat ->
  map (fun k => (k <=? h)%nat) (seq 0 (S n)) =
  repeat true (S h) ++ repeat false (n - h).
Proof.
  intros n h Hle.
  apply nth_ext with (d := false) (d' := false).
  - rewrite map_length, seq_length, app_length, !repeat_length. lia.
  - intros i Hi.
    rewrite map_length, seq_length in Hi.
    destruct (Nat.le_gt_cases i h) as [Hile | Higt].
    + (* i <= h: both sides are true *)
      assert (Hleb: (i <=? h)%nat = true) by (apply Nat.leb_le; exact Hile).
      transitivity true.
      * assert (Hin: (i < length (map (fun k => (k <=? h)%nat) (seq 0 (S n))))%nat).
        { rewrite map_length, seq_length. lia. }
        rewrite nth_indep with (d' := true) by exact Hin.
        rewrite (map_nth (fun k => (k <=? h)%nat) (seq 0 (S n)) 0%nat).
        rewrite seq_nth by lia. simpl. exact Hleb.
      * symmetry. rewrite app_nth1 by (rewrite repeat_length; lia).
        apply nth_repeat'. lia.
    + (* i > h: both sides are false *)
      assert (Hleb: (i <=? h)%nat = false) by (apply Nat.leb_gt; lia).
      transitivity false.
      * assert (Hin: (i < length (map (fun k => (k <=? h)%nat) (seq 0 (S n))))%nat).
        { rewrite map_length, seq_length. lia. }
        rewrite nth_indep with (d' := true) by exact Hin.
        rewrite (map_nth (fun k => (k <=? h)%nat) (seq 0 (S n)) 0%nat).
        rewrite seq_nth by lia. simpl. exact Hleb.
      * symmetry. rewrite app_nth2 by (rewrite repeat_length; lia).
        rewrite repeat_length.
        apply nth_repeat'. lia.
Qed.

(** Dot with repeat false is 0 *)
Lemma dot_repeat_false : forall ws, dot ws (repeat false (length ws)) = 0.
Proof.
  induction ws as [| w ws' IH]; simpl; auto.
Qed.

Lemma dot_repeat_false' : forall ws n, length ws = n -> dot ws (repeat false n) = 0.
Proof.
  intros ws n Hlen. rewrite <- Hlen. apply dot_repeat_false.
Qed.

(** Split dot product over concatenation *)
Lemma dot_app : forall ws1 ws2 xs1 xs2,
  length ws1 = length xs1 ->
  dot (ws1 ++ ws2) (xs1 ++ xs2) = dot ws1 xs1 + dot ws2 xs2.
Proof.
  induction ws1 as [| w ws1' IH]; intros ws2 xs1 xs2 Hlen.
  - destruct xs1; simpl in *; try discriminate. simpl. lia.
  - destruct xs1 as [| x xs1']; simpl in *; try discriminate.
    injection Hlen as Hlen'.
    rewrite IH by exact Hlen'.
    destruct x; lia.
Qed.

(** Alt weights split *)
Lemma even_S_negb : forall n, Nat.even (S n) = negb (Nat.even n).
Proof.
  induction n.
  - reflexivity.
  - change (Nat.even (S (S n)) = negb (Nat.even (S n))).
    change (Nat.even (S (S n))) with (Nat.even n).
    rewrite IHn.
    symmetry. apply Bool.negb_involutive.
Qed.

Lemma alt_weights_app_aux : forall n m sign,
  alt_weights (n + m) sign = alt_weights n sign ++ alt_weights m (Nat.iter n negb sign).
Proof.
  induction n as [| n' IH]; intros m sign.
  - simpl. reflexivity.
  - replace (S n' + m)%nat with (S (n' + m))%nat by lia.
    simpl alt_weights at 1 2. simpl app. simpl Nat.iter.
    f_equal.
    rewrite IH.
    f_equal. f_equal.
    (* Need: Nat.iter n' negb (negb sign) = negb (Nat.iter n' negb sign) *)
    clear. induction n'; simpl; auto.
    rewrite IHn'. reflexivity.
Qed.

Lemma iter_negb_even : forall n sign,
  Nat.iter n negb sign = if Nat.even n then sign else negb sign.
Proof.
  induction n as [| n' IH]; intros sign.
  - reflexivity.
  - simpl Nat.iter. rewrite IH.
    rewrite even_S_negb.
    destruct (Nat.even n'), sign; reflexivity.
Qed.

Lemma alt_weights_app : forall n m sign,
  alt_weights (n + m) sign = alt_weights n sign ++ alt_weights m (if Nat.even n then sign else negb sign).
Proof.
  intros. rewrite <- iter_negb_even. apply alt_weights_app_aux.
Qed.

(** Length of repeat *)
Lemma repeat_length_eq : forall A (x : A) n, length (repeat x n) = n.
Proof. intros. apply repeat_length. Qed.

(** Dot product of alt_weights with threshold list equals alt_sum_first *)
Lemma dot_alt_threshold : forall n h,
  (h <= n)%nat ->
  dot (alt_weights (S n) true) (map (fun k => (k <=? h)%nat) (seq 0%nat (S n))) =
  alt_sum_first h.
Proof.
  intros n h Hle.
  rewrite threshold_map_split by exact Hle.
  replace (S n) with (S h + (n - h))%nat by lia.
  rewrite alt_weights_app.
  rewrite dot_app by (rewrite alt_weights_length, repeat_length; reflexivity).
  rewrite dot_alt_prefix.
  rewrite (dot_repeat_false' _ (n-h)%nat) by (apply alt_weights_length).
  rewrite alt_sum_first_correct.
  destruct (Nat.even h); lia.
Qed.

(** Direct approach: prove for the specific L1 output *)
Lemma L2_concrete_correct : forall n xs,
  length xs = n ->
  (hamming_weight xs <= n)%nat ->
  L2_concrete n xs = Nat.even (hamming_weight xs).
Proof.
  intros n xs Hlen Hbound.
  unfold L2_concrete, neuron, heaviside.
  rewrite L1_concrete_eq.
  set (h := hamming_weight xs).
  rewrite dot_alt_threshold by exact Hbound.
  rewrite alt_sum_first_correct.
  destruct (Nat.even h); simpl; reflexivity.
Qed.

(** Output concrete correctly negates *)
Lemma output_concrete_correct : forall b,
  output_concrete b = negb b.
Proof.
  intros []; unfold output_concrete, heaviside; simpl; reflexivity.
Qed.

(** The concrete implementation equals the abstract one *)
Theorem concrete_eq_abstract : forall n xs,
  length xs = n ->
  (hamming_weight xs <= n)%nat ->
  parity_concrete n xs = parity_network xs.
Proof.
  intros n xs Hlen Hbound.
  unfold parity_concrete, parity_network.
  rewrite output_concrete_correct.
  unfold output, L2_fires.
  f_equal.
  apply L2_concrete_correct; auto.
Qed.

(** ** Summary *)

(**
   VERIFIED:
   - parity_network_correct: The abstract network computes parity

   STRUCTURE:
   - L2_fires h = Nat.even h (by definition)
   - output (L2_fires h) = Nat.odd h = parity

   CONCRETE IMPLEMENTATION:
   - Layer 1: n+1 threshold neurons detecting HW >= k
   - Layer 2: Alternating-weight neuron detecting even HW
   - Output: Negation neuron

   The concrete implementation matches the abstract one (concrete_eq_abstract),
   completing the verified parametric construction.

   Total neurons for n-bit parity: n + 3
*)
