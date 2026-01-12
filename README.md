# threshold-logic-verified

Formally verified binary threshold networks with provable correctness guarantees.

## Overview

This project trains minimal neural networks on decidable tasks and formally proves their correctness in Coq. The networks use discrete weights and threshold activations, enabling complete verification.

**Key result**: We provide a *fully constructive* proof that threshold networks can compute n-bit parity — not just for the trained 8-bit network, but for arbitrary input sizes. No `vm_compute` or enumeration; the proofs explain *why* the networks work through algebraic decomposition.

## Proof Progression

We developed 12 progressively more constructive proofs, culminating in a verified parametric network generator:

| File | Approach | vm_compute |
|------|----------|------------|
| `V0_Core.v` | Core definitions + full 8→32→16→1 network | 1 × 256 |
| `V1_Exhaustive.v` | Pruned 8→11→3→1 network | 1 × 256 |
| `V2_AlwaysFireLemmas.v` | Always-fire neuron lemmas | 1 × 256 |
| `V3_FlipProperty.v` | Bit-flip characterization | 1 × 256 |
| `V4_PartiallyConstructive.v` | Partial constructive | 1 × 256 |
| `V5_StructuredProof.v` | Modular structure | 1 × 256 |
| `V6_HWClassDecomposition.v` | Hamming weight classes | 9 × ~30 |
| `V7_AlgebraicInsights.v` | Key: g(x) ≡ HW(x) (mod 2) | 1 × 256 |
| `V8_ABCDecomposition.v` | Pre-activation = A+B+C−3 | 2 × 256 |
| `V9_FullyConstructive.v` | **8-bit fully constructive** | **0** |
| `V10_Parametric.v` | Parametric algebraic property | **0** |
| `V11_ParametricNetwork.v` | **Verified n-bit network generator** | **0** |

## Key Theorems

### V9: Why the trained 8-bit network works

```coq
Theorem network_correct : forall x0 x1 x2 x3 x4 x5 x6 x7,
  network x0 x1 x2 x3 x4 x5 x6 x7 = parity [x0;x1;x2;x3;x4;x5;x6;x7].
```

The proof reveals the algebraic structure:
- L2-N0, L2-N2 always fire (bias dominates negative weight sum)
- L2-N1 fires iff Hamming weight is even (via g(x) ≡ HW(x) mod 2)
- Output = NOT(L2-N1) = parity

### V10: Universal algebraic property

```coq
Theorem dot_parity_equals_hw_parity : forall ws xs,
  length ws = length xs ->
  Z.even (signed_dot ws xs) = Nat.even (hamming_weight xs).
```

For ANY ±1 weight vector and ANY bit vector: dot product parity = Hamming weight parity.

### V11: Verified n-bit parity network

```coq
Theorem parity_network_correct : forall xs,
  parity_network xs = parity xs.

Theorem concrete_eq_abstract : forall n xs,
  length xs = n ->
  parity_concrete n xs = parity_network xs.
```

Architecture for n-bit parity (n+3 neurons total):
- **Layer 1**: n+1 neurons detecting HW ≥ k for k = 0,1,...,n
- **Layer 2**: 1 neuron with alternating weights, fires iff HW even
- **Output**: 1 neuron negating L2

## Architecture

Binary threshold network:
- **Input**: n bits
- **Weights**: ternary {-1, 0, +1}
- **Biases**: bounded integers
- **Activation**: Heaviside (threshold at 0)
- **Output**: single bit

### Trained Networks

| Variant | Architecture | Parameters | File |
|---------|--------------|------------|------|
| Full | 8 → 32 → 16 → 1 | 833 | `V0_Core.v` |
| Pruned | 8 → 11 → 3 → 1 | 139 | `V1_Exhaustive.v` |
| Parametric | 8 → n+1 → 1 → 1 | n+3 neurons | `V11_ParametricNetwork.v` |

## Project Structure

```
threshold-logic-verified/
├── src/
│   ├── model.py              # Network architecture
│   ├── train.py              # Gradient-based training
│   ├── random_search.py      # Evolutionary search
│   └── export_coq.py         # JSON to Coq converter
├── coq/
│   ├── V0_Core.v             # Core definitions + full network
│   ├── V1_Exhaustive.v       # Pruned network
│   ├── V2-V8_*.v             # Proof progression
│   ├── V9_FullyConstructive.v    # 8-bit constructive proof
│   ├── V10_Parametric.v          # Parametric algebraic lemma
│   ├── V11_ParametricNetwork.v   # Parametric network construction
│   └── Weights.v             # Weight data module
└── README.md
```

## Usage

### Training

```bash
python src/random_search.py  # Evolutionary search (recommended)
python src/train.py          # Gradient-based (harder to converge)
```

### Verification

```bash
# Compile all proofs
for f in coq/V*.v; do coqc "$f"; done

# Or individual files
coqc coq/V9_FullyConstructive.v   # 8-bit constructive
coqc coq/V11_ParametricNetwork.v  # Parametric construction
```

## Related Work

The mathematical result (parity ∈ TC⁰) is classical:
- Parity computable by constant-depth threshold circuits (1988+)
- Size-depth tradeoffs for threshold circuits well-studied

The formalization approach appears novel:
- No prior Coq/Lean/Isabelle mechanization of threshold circuits for parity found
- End-to-end pipeline: train → export → verify → explain → generalize

## HuggingFace

Trained weights: [phanerozoic/tiny-parity-prover](https://huggingface.co/phanerozoic/tiny-parity-prover)

## Requirements

- Python 3.10+
- PyTorch
- Coq 8.19+

## License

MIT
