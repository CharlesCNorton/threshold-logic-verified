# threshold-logic-verified

This repository contains Coq proofs establishing that certain binary threshold networks correctly compute the parity function. The project began with a trained neural network and evolved into a complete formal treatment of threshold-based parity computation, culminating in a verified construction that works for arbitrary input sizes.

## Background

### The Parity Function

The parity function takes a sequence of bits and returns 1 if an odd number of them are set, 0 otherwise. Equivalently, parity is the XOR of all input bits. For 8-bit inputs:

```
parity([0,0,0,0,0,0,0,0]) = 0  (0 bits set, even)
parity([1,0,0,0,0,0,0,0]) = 1  (1 bit set, odd)
parity([1,1,0,0,0,0,0,0]) = 0  (2 bits set, even)
parity([1,1,1,1,1,1,1,1]) = 0  (8 bits set, even)
```

Parity is a canonical hard function for neural networks. Unlike most classification tasks, parity depends on a global property of the input—the count of set bits modulo 2—rather than local features. Small perturbations to network weights produce negligible gradient signal until the network is already close to a correct solution, making gradient-based training unreliable.

### Threshold Networks

A threshold network (or threshold circuit) uses neurons that compute weighted sums of their inputs and fire if the sum exceeds a threshold. Formally, a threshold neuron with weights w₁, ..., wₙ and bias b computes:

```
output = 1  if  Σᵢ wᵢxᵢ + b ≥ 0
         0  otherwise
```

This is the Heaviside step function applied to an affine transformation. When weights are restricted to {-1, 0, +1} (ternary weights), the network becomes amenable to formal analysis: the number of distinct weight configurations is finite, and the behavior on any input can be computed exactly in bounded integer arithmetic.

### Circuit Complexity Context

The complexity class TC⁰ consists of functions computable by constant-depth, polynomial-size threshold circuits. It has been known since the late 1980s that parity lies in TC⁰—threshold circuits can compute parity efficiently. The standard construction uses a "thermometer encoding" of the Hamming weight followed by parity detection on the unary representation.

This project does not claim to discover new complexity-theoretic results. Rather, it provides:

1. A formal Coq development proving these classical results
2. An end-to-end pipeline from trained networks to verified proofs
3. Constructive proofs that explain the algebraic structure underlying parity computation

## Project Origin

The project started with a practical question: can we train a small neural network to compute 8-bit parity and then prove it correct in Coq?

Training used evolutionary search rather than gradient descent. A population of networks with random ternary weights was evaluated on all 256 possible 8-bit inputs. Networks with higher accuracy were selected, mutated, and recombined over thousands of generations until one achieved 100% accuracy.

The trained network had architecture 8 → 32 → 16 → 1 with 833 parameters. Neuron ablation analysis revealed substantial redundancy: only 11 of 32 first-layer neurons and 3 of 16 second-layer neurons were critical for correct operation. Removing the others yielded a pruned network of architecture 8 → 11 → 3 → 1 with 139 parameters that computed the same function.

The weights were exported to Coq, where the initial correctness proof used `vm_compute` to exhaustively check all 256 inputs. This worked but provided no insight into why the network computed parity. The proof amounted to "we checked every case and they all passed."

## Proof Development

The repository contains 12 Coq files representing successive attempts to make the proof more constructive—to replace exhaustive enumeration with algebraic reasoning that explains the network's behavior.

### V0: Core Definitions

File: `V0_Core.v`

Establishes the basic vocabulary: bits, weights, biases, dot products, neurons, layers, Hamming weight, and parity. Defines the full 8 → 32 → 16 → 1 network with its trained weights and proves correctness by `vm_compute` over all 256 inputs.

Key definitions:

```coq
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
```

The correctness theorem:

```coq
Theorem network_verified :
  forall xs, In xs (all_inputs 8) -> network xs = parity xs.
Proof. vm_compute. reflexivity. Qed.
```

This proof succeeds but tells us nothing about the structure.

### V1: Pruned Network

File: `V1_Exhaustive.v`

A self-contained file defining the pruned 8 → 11 → 3 → 1 network. Same proof strategy: `vm_compute` over 256 inputs. The smaller network is easier to analyze manually, so subsequent proof attempts focus on this architecture.

### V2: Always-Fire Lemmas

File: `V2_AlwaysFireLemmas.v`

First attempt at constructive reasoning. Observes that some neurons in the network fire on every input regardless of the input values. These "always-fire" neurons have biases large enough to dominate any possible negative contribution from their weights.

The key lemma:

```coq
Fixpoint sum_negative (ws : list weight) : Z :=
  match ws with
  | [] => 0
  | w :: ws' => (if Z.ltb w 0 then w else 0) + sum_negative ws'
  end.

Lemma neuron_always_fires : forall ws b xs,
  length ws = length xs ->
  sum_negative ws + b >= 0 ->
  neuron ws b xs = true.
```

If the sum of all negative weights plus the bias is still non-negative, the neuron fires regardless of which inputs are active. This is a constructive bound that doesn't require enumerating inputs.

Applying this to specific neurons:

```coq
Theorem L2N0_always_fires : forall x0 x1 x2 x3 x4 x5 x6 x7,
  neuron w_l2n0 30 (l1_out x0 x1 x2 x3 x4 x5 x6 x7) = true.
Proof.
  intros. apply neuron_always_fires.
  - reflexivity.
  - (* sum_negative w_l2n0 = -5, bias = 30, so -5 + 30 = 25 ≥ 0 *)
    compute. lia.
Qed.
```

Two of the three layer-2 neurons (N0 and N2) always fire. This leaves only N1 as the "interesting" neuron whose behavior determines the output.

### V3: Flip Property

File: `V3_FlipProperty.v`

An alternative characterization of parity through the bit-flip property: flipping any single bit flips the parity. This is equivalent to saying parity is the unique Boolean function (up to negation) that changes value whenever exactly one input changes.

```coq
Definition flips_parity (f : list bit -> bit) :=
  forall xs i, i < length xs ->
    f (flip_bit xs i) = negb (f xs).

Lemma parity_flips : flips_parity parity.
```

The proof attempts to show that the network also satisfies this property. While mathematically valid, this approach didn't lead to cleaner proofs than direct analysis.

### V4-V5: Structural Refactoring

Files: `V4_PartiallyConstructive.v`, `V5_StructuredProof.v`

Intermediate versions reorganizing the proof structure. Separate the constructive lemmas (always-fire bounds) from the remaining exhaustive components. The goal was to minimize the scope of `vm_compute` calls.

### V6: Hamming Weight Decomposition

File: `V6_HWClassDecomposition.v`

Rather than checking all 256 inputs, partition them by Hamming weight. There are 9 possible Hamming weights (0 through 8), and all inputs with the same Hamming weight have the same parity (even weights give parity 0, odd weights give parity 1).

If we can show that the network output depends only on Hamming weight, we reduce 256 cases to 9. This version uses 9 smaller `vm_compute` calls, each checking only the inputs at a particular Hamming weight.

The insight that network behavior depends only on Hamming weight—not on which specific bits are set—foreshadows the algebraic analysis in later versions.

### V7: Algebraic Insights

File: `V7_AlgebraicInsights.v`

Breakthrough: identify an algebraic relationship between the layer-1 weight vectors and the parity function.

Define the "g function" for the weight vectors of certain layer-1 neurons:

```coq
Definition g_func (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z :=
  (if x1 then 1 else 0) + (if x3 then 1 else 0) + (if x4 then 1 else 0) -
  (if x0 then 1 else 0) - (if x2 then 1 else 0) -
  (if x5 then 1 else 0) - (if x6 then 1 else 0) - (if x7 then 1 else 0).
```

This is the dot product of the input with a specific ±1 weight pattern. The key theorem:

```coq
Theorem g_parity : forall x0 x1 x2 x3 x4 x5 x6 x7,
  Z.even (g_func x0 x1 x2 x3 x4 x5 x6 x7) =
  Nat.even (hamming_weight [x0;x1;x2;x3;x4;x5;x6;x7]).
```

The g function has the same parity as the Hamming weight. This is not a coincidence; it follows from the structure of ±1 weight vectors. If we partition the 8 positions into "positive" (weight +1) and "negative" (weight -1), then:

- Let A = count of active bits at positive positions
- Let B = count of active bits at negative positions
- Then g = A - B and HW = A + B
- So g = HW - 2B, which means g ≡ HW (mod 2)

This holds for any ±1 weight pattern, not just the specific g_func above.

### V8: A+B+C Decomposition

File: `V8_ABCDecomposition.v`

Apply the g-parity insight to analyze the critical neuron L2-N1. Express its pre-activation as a sum of three components:

```coq
Definition L2N1_preact_actual (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z :=
  let h1 := l1_out x0 x1 x2 x3 x4 x5 x6 x7 in
  dot w_l2n1 h1 + (-3).

Definition A_abstract (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z := (* h-dependent terms *)
Definition B_abstract (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z := (* HW-dependent terms *)
Definition C_abstract (x0 x1 x2 x3 x4 x5 x6 x7 : bit) : Z := (* g-dependent terms *)

Theorem L2N1_decomposition : forall x0 x1 x2 x3 x4 x5 x6 x7,
  L2N1_preact_actual x0 x1 x2 x3 x4 x5 x6 x7 =
  A_abstract x0 x1 x2 x3 x4 x5 x6 x7 +
  B_abstract x0 x1 x2 x3 x4 x5 x6 x7 +
  C_abstract x0 x1 x2 x3 x4 x5 x6 x7 - 3.
```

The C component (depending on g) equals 0 whenever the Hamming weight is even, because g has even parity in that case and the threshold conditions are symmetric around zero.

For even Hamming weight: C = 0, and A + B ≥ 3, so the pre-activation is non-negative and N1 fires.
For odd Hamming weight: A + B + C ≤ 2, so the pre-activation is negative and N1 is silent.

This reduces the proof to showing bounds on A, B, and C, which can be done by 256-way case analysis on the 8 input bits using `destruct` followed by `lia` or `reflexivity`.

### V9: Fully Constructive

File: `V9_FullyConstructive.v`

The complete constructive proof with zero `vm_compute`. Every theorem is proven by:

1. Unfolding definitions
2. Case analysis on the 8 input bits (`destruct x0, x1, x2, x3, x4, x5, x6, x7`)
3. For each of the 256 cases, the goal reduces to a trivial arithmetic statement solved by `reflexivity` or `lia`

This is still 256-way case analysis, but it happens inside Coq's kernel rather than through the `vm_compute` oracle. The proof term itself contains the structure, and each case is independently verifiable.

The main theorem:

```coq
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
```

The proof is short because it invokes the structural lemmas: two neurons always fire, one neuron fires iff HW is even, and the output combines them to produce parity.

### V10: Parametric Algebraic Property

File: `V10_Parametric.v`

Generalize the g-parity insight from 8 bits to arbitrary length. The core theorem:

```coq
Theorem dot_parity_equals_hw_parity : forall ws xs,
  length ws = length xs ->
  Z.even (signed_dot ws xs) = Nat.even (hamming_weight xs).
```

Here `signed_dot` computes the dot product where weights are represented as booleans (true = +1, false = -1). The theorem states that for any ±1 weight vector and any bit vector of the same length, the dot product has the same parity as the Hamming weight.

Proof sketch:
- Partition positions into positive (weight +1) and negative (weight -1)
- Let A = count of active bits at positive positions
- Let B = count of active bits at negative positions
- Then signed_dot = A - B and HW = A + B
- A - B = (A + B) - 2B ≡ A + B (mod 2)
- So Z.even(signed_dot) = Nat.even(HW)

The Coq proof formalizes this using auxiliary functions `count_pos` and `count_neg`, proves the decomposition lemmas, and derives the parity equality through properties of even/odd arithmetic.

This theorem holds for any n, not just n = 8. It is the algebraic foundation for parity computation via threshold networks.

### V11: Parametric Network Construction

File: `V11_ParametricNetwork.v`

Construct a verified parity network for arbitrary input size n. The architecture uses n + 3 neurons total:

**Layer 1: n + 1 threshold neurons**

Neuron k (for k = 0, 1, ..., n) fires if and only if the Hamming weight is at least k. With all-ones weights and bias -k:

```coq
Definition L1_fires (k : nat) (xs : list bit) : bit :=
  (k <=? hamming_weight xs)%nat.

Lemma L1_neuron_correct : forall k xs,
  neuron (ones (length xs)) (- Z.of_nat k) xs = (k <=? hamming_weight xs)%nat.
```

The layer-1 output is a "thermometer code" of the Hamming weight: if HW = h, then neurons 0 through h fire and neurons h+1 through n are silent. This produces a bit vector of the form [1, 1, ..., 1, 0, 0, ..., 0] with h+1 ones followed by n-h zeros.

**Layer 2: 1 neuron with alternating weights**

Take the thermometer code from layer 1 and compute a weighted sum with alternating signs [+1, -1, +1, -1, ...]. The sum of the first h+1 terms of an alternating ±1 sequence is 1 if h is even, 0 if h is odd.

```coq
Lemma alt_sum_first_correct : forall h,
  alt_sum_first h = if Nat.even h then 1 else 0.
```

With bias -1, the layer-2 neuron fires when the alternating sum is at least 1, i.e., when h is even.

**Output: 1 neuron**

Negates the layer-2 output. Fires when layer 2 is silent (h odd), producing parity.

The main theorems:

```coq
Theorem parity_network_correct : forall xs,
  parity_network xs = parity xs.

Theorem concrete_eq_abstract : forall n xs,
  length xs = n ->
  (hamming_weight xs <= n)%nat ->
  parity_concrete n xs = parity_network xs.
```

The abstract network (`parity_network`) directly computes `negb (Nat.even (hamming_weight xs))`, which equals parity. The concrete network (`parity_concrete`) implements this using actual threshold neurons, and the proof shows the two are equivalent.

## Proof Techniques

### Avoiding vm_compute

The `vm_compute` tactic in Coq compiles the goal to bytecode and executes it, returning the result. For a theorem like "for all 8-bit inputs, network(x) = parity(x)", `vm_compute` evaluates both sides for all 256 inputs and checks equality.

This is fast and always works for decidable properties over finite domains. But it provides no insight. The proof term is opaque, and the trusted computing base includes the bytecode compiler and virtual machine.

A constructive proof instead:

1. Identifies structural properties (always-fire neurons, parity-preserving weight patterns)
2. Proves these properties using standard tactics
3. Combines them to derive the main theorem

The resulting proof term is larger but consists entirely of basic logical steps that Coq's kernel can verify directly.

### 256-Way Case Analysis

Even "constructive" proofs of 8-bit theorems require examining 256 cases somewhere. The question is whether this happens:

- Externally: `vm_compute` runs code outside the kernel
- Internally: `destruct x0, ..., x7` generates 256 proof obligations that the kernel verifies

The internal approach embeds the case analysis in the proof term. Each case reduces to a trivial arithmetic fact that `lia` or `reflexivity` discharges. The proof is verbose but fully explicit.

For parametric theorems (arbitrary n), case analysis is replaced by induction. The V10 and V11 proofs use structural induction on lists, with arithmetic lemmas handling the inductive steps.

### Arithmetic Automation

The `lia` tactic (Linear Integer Arithmetic) decides the theory of linear arithmetic over integers. It handles goals like:

```
1 + Z.of_nat (count_pos ws' xs') - Z.of_nat (count_neg ws' xs') =
Z.of_nat (1 + count_pos ws' xs') - Z.of_nat (count_neg ws' xs')
```

Most proof obligations after case analysis reduce to such arithmetic trivialities. `lia` discharges them without requiring manual reasoning.

For non-linear goals (products, divisions), `lia` fails and manual lemmas are needed. The parity proofs stay within the linear fragment.

## Network Analysis

### Why the Trained Network Works

The trained 8 → 11 → 3 → 1 network was found by evolutionary search. Why does it compute parity?

**Layer 1** computes 11 different threshold functions of the input. Each neuron has a ±1 weight pattern and an integer bias. The neuron fires when the weighted sum plus bias is non-negative.

Several of the weight patterns turn out to have the same parity as the Hamming weight. This isn't because the training optimized for this property; it's a consequence of the algebraic structure of ±1 weights (the g ≡ HW mod 2 theorem).

**Layer 2** has 3 neurons receiving input from layer 1:

- N0 has bias 30, large enough that it always fires regardless of layer-1 outputs
- N2 has bias 20, also large enough to always fire
- N1 is the critical neuron. Its weight pattern and bias are tuned so that it fires exactly when the Hamming weight is even

The proof of N1's behavior uses the A+B+C decomposition. The pre-activation is a sum of contributions from different types of layer-1 neurons, and the algebraic properties ensure the sum is non-negative iff HW is even.

**Output** takes the three layer-2 outputs with weights [+1, -1, +1] and bias -2:

```
output = h2[0] - h2[1] + h2[2] - 2
```

Since h2[0] = 1 and h2[2] = 1 always:

```
output = 1 - h2[1] + 1 - 2 = -h2[1]
```

The output fires (≥ 0) when h2[1] = 0, i.e., when N1 is silent, i.e., when HW is odd. This is exactly parity.

### The Parametric Construction

The V11 construction is simpler than the trained network because it's designed for verifiability rather than found by search.

**Layer 1: Thermometer encoding**

Use n+1 neurons with identical all-ones weight vectors but different biases. Neuron k has bias -k and fires iff HW ≥ k. The output encodes the Hamming weight in unary:

```
HW = 0: [1, 0, 0, 0, ...]
HW = 1: [1, 1, 0, 0, ...]
HW = 2: [1, 1, 1, 0, ...]
...
HW = n: [1, 1, 1, 1, ...]
```

**Layer 2: Alternating sum**

Apply weights [+1, -1, +1, -1, ...] to the thermometer code. The sum of the first k+1 terms of an alternating ±1 sequence starting with +1 is:

- 1 if k is even (the +1 terms dominate)
- 0 if k is odd (the terms cancel)

With bias -1, the neuron fires when the sum ≥ 1, i.e., when k (the Hamming weight) is even.

**Output: Negation**

Invert the layer-2 output. Fire when HW is odd, which is parity.

The construction uses n + 3 neurons total. This is not optimal—threshold circuits can compute parity with O(n / log n) gates in depth 2—but it is simple and the proof is straightforward.

## File Reference

### Source Files

| File | Description |
|------|-------------|
| `src/model.py` | PyTorch implementation of threshold networks with ternary weights |
| `src/train.py` | Gradient-based training with straight-through estimators |
| `src/random_search.py` | Evolutionary search (genetic algorithm) for network weights |
| `src/export_coq.py` | Convert trained weights from JSON to Coq definitions |

### Coq Files

| File | Lines | Description |
|------|-------|-------------|
| `V0_Core.v` | ~400 | Core definitions, full network, exhaustive proof |
| `V1_Exhaustive.v` | ~120 | Pruned network, exhaustive proof |
| `V2_AlwaysFireLemmas.v` | ~320 | Always-fire lemma development |
| `V3_FlipProperty.v` | ~380 | Bit-flip characterization of parity |
| `V4_PartiallyConstructive.v` | ~230 | Mixed constructive/exhaustive |
| `V5_StructuredProof.v` | ~210 | Refactored proof structure |
| `V6_HWClassDecomposition.v` | ~500 | Hamming weight class partition |
| `V7_AlgebraicInsights.v` | ~420 | The g ≡ HW (mod 2) theorem |
| `V8_ABCDecomposition.v` | ~330 | Pre-activation decomposition |
| `V9_FullyConstructive.v` | ~500 | Complete constructive 8-bit proof |
| `V10_Parametric.v` | ~280 | Parametric algebraic property |
| `V11_ParametricNetwork.v` | ~500 | Parametric network construction |
| `Weights.v` | ~150 | Weight data for full network |

### Data Files

| File | Description |
|------|-------------|
| `weights.json` | Trained weights in JSON format |

## Building and Running

### Prerequisites

**Python environment:**
- Python 3.10 or later
- PyTorch 2.0 or later
- NumPy

**Coq environment:**
- Coq 8.19 or later

### Training a Network

The evolutionary search typically finds a working network within 10,000-20,000 generations:

```bash
cd src
python random_search.py
```

This produces `weights.json` containing the trained weights. Training progress is printed to stdout.

Gradient-based training is also available but less reliable:

```bash
python train.py --export weights.json
```

### Exporting to Coq

Convert the trained weights to Coq definitions:

```bash
python export_coq.py weights.json > ../coq/Weights.v
```

The generated file defines the weight matrices and bias vectors as Coq constants.

### Compiling Proofs

Each proof file is self-contained except for `Weights.v`, which depends on `V0_Core.v`.

Compile individual files:

```bash
cd coq
coqc V9_FullyConstructive.v
coqc V10_Parametric.v
coqc V11_ParametricNetwork.v
```

Compile all files:

```bash
for f in V*.v Weights.v; do
  echo "Compiling $f..."
  coqc "$f"
done
```

Compilation times vary. The constructive proofs (V9, V10, V11) compile in a few seconds. Files with large `vm_compute` calls may take longer.

### Verifying the Proofs

After compilation, Coq has verified all theorems in the files. The `.vo` files contain the compiled proof objects.

To inspect a proof interactively:

```bash
coqtop -l V9_FullyConstructive.v
```

Then use `Print` to examine definitions and `Check` to verify theorem statements:

```coq
Print network_correct.
Check network_correct.
```

## Extensions

### Other Boolean Functions

The techniques here extend to other Boolean functions computable by threshold circuits:

**Majority**: Output 1 if more than half of inputs are 1. This is a single threshold neuron with all-ones weights and bias -(n/2 + 1).

**Threshold-k**: Output 1 if at least k inputs are 1. Single threshold neuron with all-ones weights and bias -k.

**Symmetric functions**: Any function depending only on Hamming weight. Use the thermometer encoding from V11 followed by an appropriate combination layer.

For non-symmetric functions, the analysis is more complex and the constructive proof techniques may not apply directly.

### Larger Input Sizes

The V11 construction works for any n. Compiling the Coq proof for larger n may be slow due to the size of the generated definitions, but the proof structure is independent of n.

For the trained 8-bit network, extending to 16 bits would require retraining and re-analyzing the specific weight patterns. The algebraic insights (g ≡ HW mod 2, A+B+C decomposition) would still apply, but the specific bounds would change.

### Extracting Executable Code

Coq's extraction mechanism can produce OCaml or Haskell code from verified definitions:

```coq
Require Import ExtrOcamlBasic.
Extraction "parity.ml" parity_network.
```

The extracted code computes parity using the verified algorithm. This provides a path from formal proof to executable implementation.

## References

### Threshold Circuits and Complexity

The placement of parity in TC⁰ and the structure of threshold circuits are covered in:

- Parberry, I. (1994). Circuit Complexity and Neural Networks. MIT Press.
- Siu, K. Y., Roychowdhury, V., & Kailath, T. (1991). Depth-efficient threshold circuits for arithmetic functions. IEEE Trans. Information Theory.
- Hajnal, A., Maass, W., Pudlák, P., Szegedy, M., & Turán, G. (1993). Threshold circuits of bounded depth. Journal of Computer and System Sciences.

### Neural Network Verification

Formal verification of neural networks is an active research area, though most work focuses on adversarial robustness rather than exact correctness:

- Katz, G., Barrett, C., Dill, D. L., Julian, K., & Kochenderfer, M. J. (2017). Reluplex: An efficient SMT solver for verifying deep neural networks. CAV.
- Huang, X., Kwiatkowska, M., Wang, S., & Wu, M. (2017). Safety verification of deep neural networks. CAV.

This project differs by proving exact functional correctness (network computes parity) rather than local robustness (small perturbations don't change classification).

### Coq and Proof Assistants

- The Coq Development Team. The Coq Proof Assistant Reference Manual. https://coq.inria.fr/
- Chlipala, A. (2013). Certified Programming with Dependent Types. MIT Press.

## Trained Weights

Pre-trained weights for the 8-bit parity network are available on HuggingFace:

[phanerozoic/tiny-parity-prover](https://huggingface.co/phanerozoic/tiny-parity-prover)

The repository includes both the full network (833 parameters) and the pruned network (139 parameters), along with inference code and test results.

## License

MIT License. See LICENSE file for details.

## Acknowledgments

The project benefited from Coq's powerful tactic language for automating arithmetic reasoning, and from the decades of research on threshold circuits that established the theoretical foundations.
