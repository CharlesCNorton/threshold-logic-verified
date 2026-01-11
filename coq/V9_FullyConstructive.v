(** * Complete Constructive Proof *)

(** Network correctness via algebraic decomposition. *)

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

Definition neuron (ws : list weight) (b : bias) (xs : list bit) : bit :=
  heaviside (dot ws xs + b).

Definition layer (neurons : list (list weight * bias)) (xs : list bit) : list bit :=
  map (fun wb => neuron (fst wb) (snd wb) xs) neurons.

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

(** ** Abstract Linear Forms *)

Definition g_func (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z :=
  (if x1 then 1 else 0) + (if x3 then 1 else 0) + (if x4 then 1 else 0) -
  (if x0 then 1 else 0) - (if x2 then 1 else 0) -
  (if x5 then 1 else 0) - (if x6 then 1 else 0) - (if x7 then 1 else 0).

Definition h_func (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z :=
  (if x0 then 1 else 0) - (if x1 then 1 else 0) + (if x2 then 1 else 0) -
  (if x3 then 1 else 0) + (if x4 then 1 else 0) + (if x5 then 1 else 0) +
  (if x6 then 1 else 0) + (if x7 then 1 else 0).

(** ** Actual Layer 1 Weight Vectors *)

Definition w_n0 : list weight := [1; -1; 1; -1; 1; 1; 1; 1].
Definition w_n1 : list weight := [-1; 1; -1; 1; 1; -1; -1; -1].
Definition w_n2 : list weight := [-1; -1; -1; -1; -1; -1; -1; 1].
Definition w_n3 : list weight := [0; 1; -1; -1; -1; 0; 1; 0].
Definition w_n4 : list weight := [1; -1; -1; 0; -1; 1; -1; 0].
Definition w_n5 : list weight := [-1; 1; -1; 1; -1; -1; -1; -1].
Definition w_n6 : list weight := [-1; 1; -1; 1; 1; -1; -1; -1].
Definition w_n7 : list weight := [1; -1; 1; -1; 1; 1; 1; 1].
Definition w_n8 : list weight := [1; 1; -1; 1; 1; 1; 1; -1].
Definition w_n9 : list weight := [-1; 1; -1; 1; 1; -1; -1; -1].
Definition w_n10 : list weight := [-1; 1; -1; 1; 1; -1; -1; -1].

(** ** Key Lemma: Dot products equal abstract functions *)

Lemma dot_n0_eq_h : forall x0 x1 x2 x3 x4 x5 x6 x7,
  dot w_n0 [x0;x1;x2;x3;x4;x5;x6;x7] = h_func x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros. unfold dot, w_n0, h_func.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Lemma dot_n7_eq_h : forall x0 x1 x2 x3 x4 x5 x6 x7,
  dot w_n7 [x0;x1;x2;x3;x4;x5;x6;x7] = h_func x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros. unfold dot, w_n7, h_func.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Lemma dot_n5_eq_neg_h : forall x0 x1 x2 x3 x4 x5 x6 x7,
  dot w_n5 [x0;x1;x2;x3;x4;x5;x6;x7] = - h_func x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros. unfold dot, w_n5, h_func.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Lemma dot_n1_eq_g : forall x0 x1 x2 x3 x4 x5 x6 x7,
  dot w_n1 [x0;x1;x2;x3;x4;x5;x6;x7] = g_func x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros. unfold dot, w_n1, g_func.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Lemma dot_n6_eq_g : forall x0 x1 x2 x3 x4 x5 x6 x7,
  dot w_n6 [x0;x1;x2;x3;x4;x5;x6;x7] = g_func x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros. unfold dot, w_n6, g_func.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Lemma dot_n9_eq_g : forall x0 x1 x2 x3 x4 x5 x6 x7,
  dot w_n9 [x0;x1;x2;x3;x4;x5;x6;x7] = g_func x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros. unfold dot, w_n9, g_func.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Lemma dot_n10_eq_g : forall x0 x1 x2 x3 x4 x5 x6 x7,
  dot w_n10 [x0;x1;x2;x3;x4;x5;x6;x7] = g_func x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros. unfold dot, w_n10, g_func.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

(** N2 and N8 have HW-dependent behavior *)
Lemma dot_n2_eq : forall x0 x1 x2 x3 x4 x5 x6 x7,
  dot w_n2 [x0;x1;x2;x3;x4;x5;x6;x7] =
  2 * (if x7 then 1 else 0) - Z.of_nat (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]).
Proof.
  intros. unfold dot, w_n2, hamming_weight.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Lemma dot_n8_eq : forall x0 x1 x2 x3 x4 x5 x6 x7,
  dot w_n8 [x0;x1;x2;x3;x4;x5;x6;x7] =
  Z.of_nat (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]) -
  2 * (if x2 then 1 else 0) - 2 * (if x7 then 1 else 0).
Proof.
  intros. unfold dot, w_n8, hamming_weight.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

(** ** Always-Firing Neurons: N3 and N4 *)

Fixpoint sum_negative (ws : list weight) : Z :=
  match ws with
  | [] => 0
  | w :: ws' => (if Z.ltb w 0 then w else 0) + sum_negative ws'
  end.

Lemma dot_lower_bound : forall ws xs,
  length ws = length xs -> sum_negative ws <= dot ws xs.
Proof.
  induction ws as [| w ws' IH]; intros xs Hlen; simpl.
  - lia.
  - destruct xs as [| x xs']; simpl in Hlen; try lia.
    injection Hlen as Hlen'. simpl. specialize (IH xs' Hlen').
    destruct x; destruct (Z.ltb w 0) eqn:Hw;
    try (apply Z.ltb_lt in Hw); try (apply Z.ltb_ge in Hw); lia.
Qed.

Lemma neuron_always_fires : forall ws b xs,
  length ws = length xs -> sum_negative ws + b >= 0 -> neuron ws b xs = true.
Proof.
  intros. unfold neuron, heaviside.
  assert (Hlower := dot_lower_bound ws xs H).
  destruct (Z.geb (dot ws xs + b) 0) eqn:E; auto.
  rewrite Z.geb_leb in E. apply Z.leb_gt in E. lia.
Qed.

Lemma sum_neg_n3 : sum_negative w_n3 = -3. Proof. reflexivity. Qed.
Lemma sum_neg_n4 : sum_negative w_n4 = -4. Proof. reflexivity. Qed.

Theorem N3_always_fires : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n3 5 [x0;x1;x2;x3;x4;x5;x6;x7] = true.
Proof.
  intros. apply neuron_always_fires.
  - reflexivity.
  - rewrite sum_neg_n3. lia.
Qed.

Theorem N4_always_fires : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n4 7 [x0;x1;x2;x3;x4;x5;x6;x7] = true.
Proof.
  intros. apply neuron_always_fires.
  - reflexivity.
  - rewrite sum_neg_n4. lia.
Qed.

(** ** Neuron Characterizations *)

Theorem N0_char : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n0 0 [x0;x1;x2;x3;x4;x5;x6;x7] =
  if Z.geb (h_func x0 x1 x2 x3 x4 x5 x6 x7) 0 then true else false.
Proof.
  intros. unfold neuron, heaviside, w_n0, h_func, dot.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Theorem N7_char : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n7 (-2) [x0;x1;x2;x3;x4;x5;x6;x7] =
  if Z.geb (h_func x0 x1 x2 x3 x4 x5 x6 x7) 2 then true else false.
Proof.
  intros. unfold neuron, heaviside. rewrite dot_n7_eq_h.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Theorem N5_char : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n5 0 [x0;x1;x2;x3;x4;x5;x6;x7] =
  if Z.leb (h_func x0 x1 x2 x3 x4 x5 x6 x7) 0 then true else false.
Proof.
  intros. unfold neuron, heaviside. rewrite dot_n5_eq_neg_h.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Theorem N1_char : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n1 1 [x0;x1;x2;x3;x4;x5;x6;x7] =
  if Z.geb (g_func x0 x1 x2 x3 x4 x5 x6 x7) (-1) then true else false.
Proof.
  intros. unfold neuron, heaviside. rewrite dot_n1_eq_g.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Theorem N6_char : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n6 3 [x0;x1;x2;x3;x4;x5;x6;x7] =
  if Z.geb (g_func x0 x1 x2 x3 x4 x5 x6 x7) (-3) then true else false.
Proof.
  intros. unfold neuron, heaviside. rewrite dot_n6_eq_g.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Theorem N9_char : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n9 0 [x0;x1;x2;x3;x4;x5;x6;x7] =
  if Z.geb (g_func x0 x1 x2 x3 x4 x5 x6 x7) 0 then true else false.
Proof.
  intros. unfold neuron, heaviside. rewrite dot_n9_eq_g.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Theorem N10_char : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n10 2 [x0;x1;x2;x3;x4;x5;x6;x7] =
  if Z.geb (g_func x0 x1 x2 x3 x4 x5 x6 x7) (-2) then true else false.
Proof.
  intros. unfold neuron, heaviside. rewrite dot_n10_eq_g.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Theorem N2_char : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n2 2 [x0;x1;x2;x3;x4;x5;x6;x7] =
  if Z.geb (2 * (if x7 then 1 else 0) -
            Z.of_nat (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7])) (-2)
  then true else false.
Proof.
  intros. unfold neuron, heaviside. rewrite dot_n2_eq.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

Theorem N8_char : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_n8 (-2) [x0;x1;x2;x3;x4;x5;x6;x7] =
  if Z.geb (Z.of_nat (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]) -
            2 * (if x2 then 1 else 0) - 2 * (if x7 then 1 else 0)) 2
  then true else false.
Proof.
  intros. unfold neuron, heaviside. rewrite dot_n8_eq.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

(** ** Full Layer 1 *)

Definition layer1_weights : list (list weight * bias) :=
  [(w_n0, 0); (w_n1, 1); (w_n2, 2); (w_n3, 5); (w_n4, 7);
   (w_n5, 0); (w_n6, 3); (w_n7, -2); (w_n8, -2); (w_n9, 0); (w_n10, 2)].

Definition l1_out (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : list bit :=
  layer layer1_weights [x0;x1;x2;x3;x4;x5;x6;x7].

Lemma l1_out_expand : forall x0 x1 x2 x3 x4 x5 x6 x7,
  l1_out x0 x1 x2 x3 x4 x5 x6 x7 =
  [neuron w_n0 0 [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n1 1 [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n2 2 [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n3 5 [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n4 7 [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n5 0 [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n6 3 [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n7 (-2) [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n8 (-2) [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n9 0 [x0;x1;x2;x3;x4;x5;x6;x7];
   neuron w_n10 2 [x0;x1;x2;x3;x4;x5;x6;x7]].
Proof. reflexivity. Qed.

(** ** L2-N1 Pre-activation *)

Definition w_l2n1 : list weight := [1; -1; 1; 1; -1; 1; -1; 1; 1; 1; 1].

Definition bool_to_Z (b : bool) : Z := if b then 1 else 0.

Definition L2N1_preact_actual (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z :=
  let h1 := l1_out x0 x1 x2 x3 x4 x5 x6 x7 in
  dot w_l2n1 h1 + (-3).

Definition A_abstract (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z :=
  let hv := h_func x0 x1 x2 x3 x4 x5 x6 x7 in
  bool_to_Z (Z.geb hv 0) + bool_to_Z (Z.leb hv 0) + bool_to_Z (Z.geb hv 2).

Definition B_abstract (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z :=
  let hw := Z.of_nat (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]) in
  let x2z := bool_to_Z x2 in
  let x7z := bool_to_Z x7 in
  bool_to_Z (Z.geb (2*x7z - hw) (-2)) + bool_to_Z (Z.geb (hw - 2*x2z - 2*x7z) 2).

Definition C_abstract (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z :=
  let gv := g_func x0 x1 x2 x3 x4 x5 x6 x7 in
  - bool_to_Z (Z.geb gv (-1)) - bool_to_Z (Z.geb gv (-3)) +
  bool_to_Z (Z.geb gv 0) + bool_to_Z (Z.geb gv (-2)).

(** Main correspondence theorem *)
Theorem L2N1_decomposition : forall x0 x1 x2 x3 x4 x5 x6 x7,
  L2N1_preact_actual x0 x1 x2 x3 x4 x5 x6 x7 =
  A_abstract x0 x1 x2 x3 x4 x5 x6 x7 +
  B_abstract x0 x1 x2 x3 x4 x5 x6 x7 +
  C_abstract x0 x1 x2 x3 x4 x5 x6 x7 - 3.
Proof.
  intros.
  unfold L2N1_preact_actual, A_abstract, B_abstract, C_abstract.
  rewrite l1_out_expand.
  rewrite N0_char, N1_char, N2_char, N5_char, N6_char, N7_char, N8_char, N9_char, N10_char.
  rewrite N3_always_fires, N4_always_fires.
  unfold dot, w_l2n1, bool_to_Z.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

(** ** g parity theorem *)

Theorem g_parity : forall x0 x1 x2 x3 x4 x5 x6 x7,
  Z.even (g_func x0 x1 x2 x3 x4 x5 x6 x7) =
  Nat.even (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]).
Proof.
  intros. unfold g_func, hamming_weight.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; reflexivity.
Qed.

(** ** C = 0 for even g *)

Theorem C_zero_even_g : forall x0 x1 x2 x3 x4 x5 x6 x7,
  Z.even (g_func x0 x1 x2 x3 x4 x5 x6 x7) = true ->
  C_abstract x0 x1 x2 x3 x4 x5 x6 x7 = 0.
Proof.
  intros. unfold C_abstract, g_func, bool_to_Z.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; simpl in H; try discriminate; reflexivity.
Qed.

(** ** B <= 1 for odd HW *)

Theorem B_bound_odd : forall x0 x1 x2 x3 x4 x5 x6 x7,
  Nat.odd (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]) = true ->
  B_abstract x0 x1 x2 x3 x4 x5 x6 x7 <= 1.
Proof.
  intros. unfold B_abstract, hamming_weight, bool_to_Z.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; simpl in H; try discriminate; simpl; lia.
Qed.

(** ** Main Bounds *)

Theorem even_HW_fires : forall x0 x1 x2 x3 x4 x5 x6 x7,
  Nat.even (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]) = true ->
  L2N1_preact_actual x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof.
  intros.
  rewrite L2N1_decomposition.
  assert (HC: C_abstract x0 x1 x2 x3 x4 x5 x6 x7 = 0).
  { apply C_zero_even_g. rewrite g_parity. exact H. }
  rewrite HC.
  unfold A_abstract, B_abstract, h_func, hamming_weight, bool_to_Z.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; simpl in H; try discriminate; simpl; lia.
Qed.

Theorem odd_HW_silent : forall x0 x1 x2 x3 x4 x5 x6 x7,
  Nat.odd (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]) = true ->
  L2N1_preact_actual x0 x1 x2 x3 x4 x5 x6 x7 < 0.
Proof.
  intros.
  rewrite L2N1_decomposition.
  unfold A_abstract, B_abstract, C_abstract, h_func, g_func, hamming_weight, bool_to_Z.
  destruct x0,x1,x2,x3,x4,x5,x6,x7; simpl in H; try discriminate; simpl; lia.
Qed.

(** ** L2-N0 and L2-N2 always fire *)

Definition w_l2n0 : list weight := [0; 0; -1; -1; 0; 0; -1; 1; -1; 1; -1].
Definition w_l2n2 : list weight := [1; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1].

Lemma sum_neg_l2n0 : sum_negative w_l2n0 = -5. Proof. reflexivity. Qed.
Lemma sum_neg_l2n2 : sum_negative w_l2n2 = 0. Proof. reflexivity. Qed.

Theorem L2N0_always_fires : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_l2n0 30 (l1_out x0 x1 x2 x3 x4 x5 x6 x7) = true.
Proof.
  intros. apply neuron_always_fires.
  - rewrite l1_out_expand. reflexivity.
  - rewrite sum_neg_l2n0. lia.
Qed.

Theorem L2N2_always_fires : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_l2n2 20 (l1_out x0 x1 x2 x3 x4 x5 x6 x7) = true.
Proof.
  intros. apply neuron_always_fires.
  - rewrite l1_out_expand. reflexivity.
  - rewrite sum_neg_l2n2. lia.
Qed.

(** ** L2-N1 behavior *)

Definition L2N1 (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : bit :=
  neuron w_l2n1 (-3) (l1_out x0 x1 x2 x3 x4 x5 x6 x7).

Theorem L2N1_eq_even_hw : forall x0 x1 x2 x3 x4 x5 x6 x7,
  L2N1 x0 x1 x2 x3 x4 x5 x6 x7 = Nat.even (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]).
Proof.
  intros.
  unfold L2N1, neuron, heaviside, l1_out.
  destruct (Nat.even (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7])) eqn:Heven.
  - (* even case *)
    assert (Hge := even_HW_fires x0 x1 x2 x3 x4 x5 x6 x7 Heven).
    unfold L2N1_preact_actual, l1_out in Hge.
    destruct (Z.geb (dot w_l2n1 (layer layer1_weights [x0;x1;x2;x3;x4;x5;x6;x7]) + -3) 0) eqn:E.
    + reflexivity.
    + rewrite Z.geb_leb in E. apply Z.leb_gt in E. lia.
  - (* odd case *)
    assert (Hodd: Nat.odd (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]) = true).
    { unfold Nat.odd. rewrite Heven. reflexivity. }
    assert (Hlt := odd_HW_silent x0 x1 x2 x3 x4 x5 x6 x7 Hodd).
    unfold L2N1_preact_actual, l1_out in Hlt.
    destruct (Z.geb (dot w_l2n1 (layer layer1_weights [x0;x1;x2;x3;x4;x5;x6;x7]) + -3) 0) eqn:E.
    + rewrite Z.geb_leb in E. apply Z.leb_le in E. lia.
    + reflexivity.
Qed.

(** ** Full Network *)

Definition layer2 (h1 : list bit) : list bit :=
  [neuron w_l2n0 30 h1; neuron w_l2n1 (-3) h1; neuron w_l2n2 20 h1].

Definition w_out : list weight := [1; -1; 1].

Definition network (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : bit :=
  let h1 := l1_out x0 x1 x2 x3 x4 x5 x6 x7 in
  let h2 := layer2 h1 in
  neuron w_out (-2) h2.

(** ** Parity Properties *)

Lemma odd_S : forall n, Nat.odd (S n) = negb (Nat.odd n).
Proof.
  induction n; simpl; auto.
  rewrite IHn. rewrite Bool.negb_involutive. reflexivity.
Qed.

Lemma parity_odd : forall xs, parity xs = Nat.odd (hamming_weight xs).
Proof.
  induction xs; simpl.
  - reflexivity.
  - destruct a; simpl.
    + rewrite IHxs. rewrite odd_S. reflexivity.
    + exact IHxs.
Qed.

(** ** Final Theorem *)

Lemma L2N1_direct : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_l2n1 (-3) (l1_out x0 x1 x2 x3 x4 x5 x6 x7) =
  Nat.even (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]).
Proof. intros. apply L2N1_eq_even_hw. Qed.

Theorem network_correct : forall x0 x1 x2 x3 x4 x5 x6 x7,
  network x0 x1 x2 x3 x4 x5 x6 x7 = parity [x0;x1;x2;x3;x4;x5;x6;x7].
Proof.
  intros.
  unfold network, layer2.
  rewrite L2N0_always_fires, L2N2_always_fires, L2N1_direct.
  unfold neuron, w_out, dot, heaviside.
  rewrite parity_odd.
  unfold Nat.odd.
  destruct (Nat.even (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7])); reflexivity.
Qed.

(** ** List-Based Wrapper *)

Fixpoint all_inputs (n : nat) : list (list bit) :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (all_inputs n') ++ map (cons true) (all_inputs n')
  end.

Theorem network_correct_all : forall xs,
  In xs (all_inputs 8) ->
  match xs with
  | [x0;x1;x2;x3;x4;x5;x6;x7] => network x0 x1 x2 x3 x4 x5 x6 x7 = parity xs
  | _ => True
  end.
Proof.
  intros xs Hin.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; auto.
  apply network_correct.
Qed.
