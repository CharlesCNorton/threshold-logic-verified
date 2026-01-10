(** * Threshold Logic Networks *)

(** Formal verification of binary threshold networks. *)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(** ** Definitions *)

Definition bit := bool.
Definition weight := Z.
Definition bias := Z.

(** Heaviside activation: 1 if x >= 0, else 0. *)
Definition heaviside (x : Z) : bit :=
  if Z.geb x 0 then true else false.

(** Dot product of weights and inputs. *)
Fixpoint dot (ws : list weight) (xs : list bit) : Z :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' =>
      (if x then w else 0) + dot ws' xs'
  end.

(** Single neuron: dot product + bias, then heaviside. *)
Definition neuron (ws : list weight) (b : bias) (xs : list bit) : bit :=
  heaviside (dot ws xs + b).

(** Layer: apply list of neurons to same input. *)
Definition layer (neurons : list (list weight * bias)) (xs : list bit) : list bit :=
  map (fun wb => neuron (fst wb) (snd wb) xs) neurons.

(** Parity function: XOR of all input bits. *)
Fixpoint parity (xs : list bit) : bit :=
  match xs with
  | [] => false
  | x :: xs' => xorb x (parity xs')
  end.

(** ** Examples and Tests *)

Example heaviside_pos : heaviside 5 = true.
Proof. reflexivity. Qed.

Example heaviside_zero : heaviside 0 = true.
Proof. reflexivity. Qed.

Example heaviside_neg : heaviside (-3) = false.
Proof. reflexivity. Qed.

Example dot_simple : dot [1; (-1); 1] [true; false; true] = 2.
Proof. reflexivity. Qed.

Example dot_all_false : dot [1; 2; 3] [false; false; false] = 0.
Proof. reflexivity. Qed.

Example parity_empty : parity [] = false.
Proof. reflexivity. Qed.

Example parity_one_true : parity [true] = true.
Proof. reflexivity. Qed.

Example parity_two_true : parity [true; true] = false.
Proof. reflexivity. Qed.

Example parity_mixed : parity [true; false; true; true] = true.
Proof. reflexivity. Qed.

Example neuron_simple : neuron [1; 1] 0 [true; true] = true.
Proof. reflexivity. Qed.

Example neuron_negative : neuron [1; 1] (-3) [true; true] = false.
Proof. reflexivity. Qed.

Example layer_simple : layer [([1; 1], -1); ([1; 1], -2)] [true; false] = [true; false].
Proof. reflexivity. Qed.

(** ** Helper Lemmas *)

Lemma parity_cons (x : bit) (xs : list bit) :
  parity (x :: xs) = xorb x (parity xs).
Proof. reflexivity. Qed.

Lemma parity_app (xs ys : list bit) :
  parity (xs ++ ys) = xorb (parity xs) (parity ys).
Proof.
  induction xs as [| x xs' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite xorb_assoc. reflexivity.
Qed.

Lemma dot_nil_l (xs : list bit) : dot [] xs = 0.
Proof. reflexivity. Qed.

Lemma dot_nil_r (ws : list weight) : dot ws [] = 0.
Proof. destruct ws; reflexivity. Qed.

Lemma heaviside_nonneg (x : Z) : x >= 0 -> heaviside x = true.
Proof.
  intros H.
  unfold heaviside.
  destruct (Z.geb x 0) eqn:E; auto.
  rewrite Z.geb_leb in E.
  apply Z.leb_gt in E. lia.
Qed.

Lemma heaviside_neg' (x : Z) : x < 0 -> heaviside x = false.
Proof.
  intros H.
  unfold heaviside.
  destruct (Z.geb x 0) eqn:E; auto.
  rewrite Z.geb_leb in E.
  apply Z.leb_le in E. lia.
Qed.

(** ** Input Generation *)

(** Generate all n-bit inputs. *)
Fixpoint all_inputs (n : nat) : list (list bit) :=
  match n with
  | O => [[]]
  | S n' =>
      let prev := all_inputs n' in
      map (cons false) prev ++ map (cons true) prev
  end.

Example all_inputs_length_2 : length (all_inputs 2) = 4%nat.
Proof. reflexivity. Qed.

Example all_inputs_length_8 : length (all_inputs 8) = 256%nat.
Proof. reflexivity. Qed.

(** ** 2-Bit Parity Network (Hand-Crafted) *)

(** XOR = (x1 OR x2) AND NOT (x1 AND x2).
    Layer 1 computes OR and AND.
    Output combines them. *)

Definition net2_layer1 : list (list weight * bias) :=
  [ ([1; 1], -1);    (** OR: x1 + x2 - 1 >= 0 *)
    ([1; 1], -2) ].  (** AND: x1 + x2 - 2 >= 0 *)

Definition net2_output : list weight * bias :=
  ([1; -1], -1).     (** h1 - h2 - 1 >= 0: OR and not AND *)

Definition network2 (xs : list bit) : bit :=
  let h1 := layer net2_layer1 xs in
  neuron (fst net2_output) (snd net2_output) h1.

(** Test the 2-bit network on all inputs. *)
Example net2_00 : network2 [false; false] = false.
Proof. reflexivity. Qed.

Example net2_10 : network2 [true; false] = true.
Proof. reflexivity. Qed.

Example net2_01 : network2 [false; true] = true.
Proof. reflexivity. Qed.

Example net2_11 : network2 [true; true] = false.
Proof. reflexivity. Qed.

(** Verify 2-bit network computes parity. *)
Definition check_one_2bit (xs : list bit) : bool :=
  Bool.eqb (network2 xs) (parity xs).

Theorem network2_correct :
  forallb check_one_2bit (all_inputs 2) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** 8-Bit Network (Parameterized) *)

Section Network8.

  (** Weight parameters to be instantiated after training. *)
  Variable l1_weights : list (list weight * bias).
  Variable l2_weights : list (list weight * bias).
  Variable out_weights : list weight * bias.

  Definition network8 (xs : list bit) : bit :=
    let h1 := layer l1_weights xs in
    let h2 := layer l2_weights h1 in
    neuron (fst out_weights) (snd out_weights) h2.

  Definition check_one_8bit (xs : list bit) : bool :=
    Bool.eqb (network8 xs) (parity xs).

  Definition check_all_8bit : bool :=
    forallb check_one_8bit (all_inputs 8).

  (** Correctness theorem: given weights that pass exhaustive check. *)
  Theorem network8_correct :
    check_all_8bit = true ->
    forall xs, In xs (all_inputs 8) -> network8 xs = parity xs.
  Proof.
    intros Hcheck xs Hin.
    unfold check_all_8bit in Hcheck.
    rewrite forallb_forall in Hcheck.
    specialize (Hcheck xs Hin).
    unfold check_one_8bit in Hcheck.
    apply eqb_prop in Hcheck.
    exact Hcheck.
  Qed.

  (** Find first failing input for debugging. *)
  Definition find_counterexample : option (list bit) :=
    find (fun xs => negb (check_one_8bit xs)) (all_inputs 8).

End Network8.

(** ** Concrete 8-Bit Instance *)

(** Placeholder weights: replace with trained values. *)
Definition layer1_weights : list (list weight * bias) := [].
Definition layer2_weights : list (list weight * bias) := [].
Definition output_weights : list weight * bias := ([], 0).

(** Instantiate network with placeholder weights. *)
Definition network := network8 layer1_weights layer2_weights output_weights.
Definition counterexamples := find_counterexample layer1_weights layer2_weights output_weights.

(** To complete verification after training:
    1. Replace placeholder weights with trained values
    2. Prove: check_all_8bit layer1_weights layer2_weights output_weights = true
       using [vm_compute. reflexivity.]
    3. Apply network8_correct to get full correctness theorem. *)

Example verify_when_ready :
  check_all_8bit layer1_weights layer2_weights output_weights = true ->
  forall xs, In xs (all_inputs 8) -> network xs = parity xs.
Proof.
  intros H.
  apply network8_correct.
  exact H.
Qed.

(** ** Weight Insertion Guide

    After training, export weights to JSON using:
      python src/train.py --export weights.json

    The JSON format is:
      {
        "layer1": {"weight": [[w11, w12, ...], ...], "bias": [b1, ...]},
        "layer2": {"weight": [[w21, w22, ...], ...], "bias": [b1, ...]},
        "output": {"weight": [[w31, w32, ...]], "bias": [b1]}
      }

    Convert to Coq syntax:
      - Each row of weights becomes a list: [w1; w2; w3; ...]
      - Each neuron is a pair: ([weights], bias)
      - Each layer is a list of neuron pairs

    Example for layer1 with 2 neurons, 8 inputs each:
      Definition layer1_weights : list (list weight * bias) :=
        [ ([1; -1; 0; 1; -1; 0; 1; -1], 2);
          ([0; 1; 1; -1; 0; -1; 1; 0], -3) ].

    After inserting weights:
      1. Replace the empty definitions for layer1_weights, layer2_weights, output_weights
      2. Add a lemma proving the check passes:
           Lemma weights_valid : check_all_8bit layer1_weights layer2_weights output_weights = true.
           Proof. vm_compute. reflexivity. Qed.
      3. If the proof fails, debug with:
           Compute counterexamples.
      4. Apply network8_correct with weights_valid to get the full correctness theorem.
*)
