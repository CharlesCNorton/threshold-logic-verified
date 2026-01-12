(** * V12: Minimal Depth-2 Parity Network with Extraction *)

(**
   This file constructs and verifies a MINIMAL depth-2 threshold circuit
   for 8-bit parity, then provides extraction to executable OCaml.

   CONTEXT:
   - V10_Parametric proved that ±1 dot products preserve Hamming weight parity.
   - V11_ParametricNetwork showed an (n+3)-neuron construction exists for any n.
   - This file INSTANTIATES that construction concretely for n=8 and EXTRACTS it.

   ARCHITECTURE:
   - Layer 1: 9 neurons with all-ones weights, biases 0, -1, ..., -8.
     Neuron k fires iff HW(input) >= k. Output is a thermometer code.
   - Layer 2: 1 neuron with alternating weights [1,-1,1,-1,1,-1,1,-1,1], bias -1.
     Fires iff the alternating sum of the thermometer code >= 1, i.e., HW is even.
   - Output: 1 neuron with weight [-1], bias 0.
     Negates L2 output: fires iff HW is odd, which equals parity.

   COMPARISON TO TRAINED NETWORK:
   - Trained (V0-V9): 49 neurons, 833 parameters, depth 3, found by evolution.
   - Constructed (this file): 11 neurons, 93 parameters, depth 2, designed.

   The trained network works; this one is minimal and explains WHY it works.

   EXTRACTION:
   Run Extract.v to produce parity_verified.ml, a standalone OCaml implementation
   that inherits correctness from these proofs.
*)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(** ** Core Definitions *)

Definition bit := bool.

(** Hamming weight: count of true bits. *)
Fixpoint hamming_weight (xs : list bit) : nat :=
  match xs with
  | [] => 0
  | true :: xs' => S (hamming_weight xs')
  | false :: xs' => hamming_weight xs'
  end.

(** Parity: XOR of all bits. Equivalently, HW mod 2. *)
Fixpoint parity (xs : list bit) : bit :=
  match xs with
  | [] => false
  | x :: xs' => xorb x (parity xs')
  end.

(** Heaviside step function: the threshold gate activation. *)
Definition heaviside (x : Z) : bit := Z.geb x 0.

(** Integer dot product between weights and binary inputs. *)
Fixpoint dot (ws : list Z) (xs : list bit) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' => (if x then w else 0) + dot ws' xs'
  end.

(** A threshold neuron: fires iff dot(weights, inputs) + bias >= 0. *)
Definition neuron (ws : list Z) (b : Z) (xs : list bit) : bit :=
  heaviside (dot ws xs + b).

(** ** Layer 1: Thermometer Encoding *)

(**
   Layer 1 uses n+1 neurons (here, 9) to encode the Hamming weight
   in thermometer format. Neuron k has all-ones weights and bias -k,
   so it fires iff the input sum (= HW) >= k.

   For 8-bit inputs with HW = h:
   - L1 output = [1,1,...,1,0,0,...,0] with h+1 ones followed by 8-h zeros.
*)

(** Weight vector of n ones. *)
Fixpoint ones (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => 1 :: ones n'
  end.

Lemma ones_length : forall n, length (ones n) = n.
Proof. induction n; simpl; auto. Qed.

(** Dot product with all-ones equals Hamming weight. *)
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

(** Layer 1 neuron k fires iff HW >= k. *)
Definition L1_neuron (k : nat) (xs : list bit) : bit :=
  neuron (ones (length xs)) (- Z.of_nat k) xs.

Lemma L1_neuron_correct : forall k xs,
  L1_neuron k xs = (k <=? hamming_weight xs)%nat.
Proof.
  intros k xs.
  unfold L1_neuron, neuron, heaviside.
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

(** Layer 1 output: 9-element thermometer encoding of HW. *)
Definition L1_output (xs : list bit) : list bit :=
  map (fun k => L1_neuron k xs) (seq 0 9).

Lemma L1_output_length : forall xs, length (L1_output xs) = 9%nat.
Proof. intros. unfold L1_output. rewrite map_length, seq_length. reflexivity. Qed.

(** Each element of L1 output equals the threshold test. *)
Lemma L1_output_nth : forall xs k,
  (k < 9)%nat ->
  nth k (L1_output xs) false = L1_neuron k xs.
Proof.
  intros xs k Hk.
  unfold L1_output.
  destruct k as [|[|[|[|[|[|[|[|[|]]]]]]]]]; try (simpl in Hk; lia); reflexivity.
Qed.

Lemma L1_output_thermometer : forall xs k,
  length xs = 8%nat ->
  (k < 9)%nat ->
  nth k (L1_output xs) false = (k <=? hamming_weight xs)%nat.
Proof.
  intros xs k Hlen Hk.
  rewrite L1_output_nth by exact Hk.
  apply L1_neuron_correct.
Qed.

(** ** Layer 2: Parity Detection via Alternating Weights *)

(**
   Layer 2 has one neuron with alternating weights [1,-1,1,-1,1,-1,1,-1,1]
   and bias -1. On input thermometer code with m ones:

     pre-activation = (1 - 1 + 1 - 1 + ... for m terms) - 1
                    = (1 if m odd, 0 if m even) - 1
                    = (0 if m odd, -1 if m even)

   So L2 fires (>= 0) iff m is odd, i.e., iff HW+1 is odd, i.e., iff HW is even.
*)

Fixpoint alt_weights (n : nat) (sign : bool) : list Z :=
  match n with
  | O => []
  | S n' => (if sign then 1 else -1) :: alt_weights n' (negb sign)
  end.

Definition L2_weights : list Z := alt_weights 9 true.

Lemma L2_weights_expand : L2_weights = [1; -1; 1; -1; 1; -1; 1; -1; 1].
Proof. reflexivity. Qed.

(** Alternating sum of first m ones. *)
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
    rewrite IH.
    destruct (Nat.even n'); reflexivity.
Qed.

Lemma odd_S : forall n, Nat.odd (S n) = negb (Nat.odd n).
Proof.
  intros n.
  unfold Nat.odd. rewrite even_S.
  destruct (Nat.even n); reflexivity.
Qed.

Lemma alt_sum_first_correct : forall m,
  alt_sum_first m = if Nat.odd m then 1 else 0.
Proof.
  induction m.
  - reflexivity.
  - simpl alt_sum_first. rewrite odd_S.
    rewrite IHm.
    destruct (Nat.odd m); simpl; lia.
Qed.

Definition L2_neuron (h1 : list bit) : bit :=
  neuron L2_weights (-1) h1.

(** L2 fires iff Hamming weight is even. *)
Theorem L2_fires_iff_even : forall xs,
  length xs = 8%nat ->
  (hamming_weight xs <= 8)%nat ->
  L2_neuron (L1_output xs) = Nat.even (hamming_weight xs).
Proof.
  intros xs Hlen Hbound.
  unfold L2_neuron, neuron, heaviside.
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

  rewrite Hdot.
  rewrite alt_sum_first_correct.
  rewrite odd_S.
  unfold Nat.odd.
  destruct (Nat.even hw) eqn:Heven; simpl; reflexivity.
Qed.

(** ** Output Layer: Negation *)

(**
   The output neuron negates L2: weight -1, bias 0.
   Fires iff L2 is silent, i.e., iff HW is odd, i.e., parity = 1.
*)

Definition output_neuron (l2 : bit) : bit :=
  neuron [-1] 0 [l2].

Lemma output_neuron_negates : forall b,
  output_neuron b = negb b.
Proof.
  intros []; unfold output_neuron, neuron, heaviside, dot; simpl; reflexivity.
Qed.

(** ** Complete Depth-2 Network *)

Definition parity_depth2 (xs : list bit) : bit :=
  let h1 := L1_output xs in
  let h2 := L2_neuron h1 in
  output_neuron h2.

(** ** Main Correctness Theorem *)

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

(**
   MAIN THEOREM: The depth-2 network computes parity.

   Proof structure:
   1. Output neuron negates L2.
   2. L2 fires iff HW is even (L2_fires_iff_even).
   3. Therefore output fires iff HW is odd.
   4. Parity = Nat.odd HW (parity_is_odd_hw).
   5. QED.
*)
Theorem parity_depth2_correct : forall xs,
  length xs = 8%nat ->
  parity_depth2 xs = parity xs.
Proof.
  intros xs Hlen.
  unfold parity_depth2.
  rewrite output_neuron_negates.
  rewrite L2_fires_iff_even by (auto using hw_bounded).
  rewrite parity_is_odd_hw.
  unfold Nat.odd.
  destruct (Nat.even (hamming_weight xs)); reflexivity.
Qed.

(** ** Concrete Network with Explicit Weights *)

(**
   For extraction to OCaml, we need concrete weight definitions
   rather than computed ones. This section provides them.
*)

Definition L1_weights_concrete : list (list Z * Z) :=
  [ (ones 8, 0);
    (ones 8, -1);
    (ones 8, -2);
    (ones 8, -3);
    (ones 8, -4);
    (ones 8, -5);
    (ones 8, -6);
    (ones 8, -7);
    (ones 8, -8) ].

Definition L2_weights_concrete : list Z * Z :=
  ([1; -1; 1; -1; 1; -1; 1; -1; 1], -1).

Definition output_weights_concrete : list Z * Z :=
  ([-1], 0).

Definition layer (neurons : list (list Z * Z)) (xs : list bit) : list bit :=
  map (fun wb => neuron (fst wb) (snd wb) xs) neurons.

Definition parity_depth2_concrete (xs : list bit) : bit :=
  let h1 := layer L1_weights_concrete xs in
  let h2 := neuron (fst L2_weights_concrete) (snd L2_weights_concrete) h1 in
  neuron (fst output_weights_concrete) (snd output_weights_concrete) [h2].

Lemma concrete_eq_abstract : forall xs,
  length xs = 8%nat ->
  parity_depth2_concrete xs = parity_depth2 xs.
Proof.
  intros xs Hlen.
  unfold parity_depth2_concrete, parity_depth2.
  unfold layer, L1_weights_concrete, L1_output, L1_neuron.
  unfold L2_neuron, L2_weights_concrete, L2_weights.
  unfold output_neuron, output_weights_concrete.
  simpl fst. simpl snd.
  rewrite Hlen.
  reflexivity.
Qed.

Theorem parity_depth2_concrete_correct : forall xs,
  length xs = 8%nat ->
  parity_depth2_concrete xs = parity xs.
Proof.
  intros xs Hlen.
  rewrite concrete_eq_abstract by exact Hlen.
  apply parity_depth2_correct. exact Hlen.
Qed.

(** ** Exhaustive Verification (Sanity Check) *)

Fixpoint all_inputs (n : nat) : list (list bit) :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')
  end.

Definition check_all : bool :=
  forallb (fun xs => Bool.eqb (parity_depth2_concrete xs) (parity xs)) (all_inputs 8).

Lemma exhaustive_check : check_all = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Summary *)

(**
   WHAT WE PROVED:
   - parity_depth2_correct: The abstract network computes 8-bit parity.
   - parity_depth2_concrete_correct: The concrete network (for extraction) does too.
   - exhaustive_check: Sanity-checked via vm_compute on all 256 inputs.

   WHAT WE BUILT:
   - 11-neuron depth-2 threshold circuit for parity.
   - Layer 1: 9 thermometer neurons (all-ones weights, biases 0 to -8).
   - Layer 2: 1 alternating-weight neuron detecting even HW.
   - Output: 1 negation neuron.

   WHY IT WORKS:
   - Thermometer encoding captures HW exactly.
   - Alternating sum of first (HW+1) ones = 1 iff HW+1 is odd = 1 iff HW is even.
   - Negating "HW is even" gives "HW is odd" = parity.

   EXTRACTION:
   See coq/Extract.v to generate parity_verified.ml.
   See extracted/ for the OCaml implementation and test suite.
*)
