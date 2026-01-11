# threshold-logic-verified

Formally verified binary threshold networks with provable correctness guarantees.

## Overview

This project trains minimal neural networks on decidable tasks and formally proves their correctness in Coq. The networks use discrete weights and threshold activations, enabling exhaustive verification over all possible inputs.

## Architecture

Binary threshold network with:
- **Input**: n bits
- **Weights**: ternary {-1, 0, +1}
- **Biases**: bounded integers
- **Activation**: Heaviside (threshold at 0)
- **Output**: single bit

## Models

### Full Network

The original trained network for 8-bit parity.

| Parameter | Value |
|-----------|-------|
| Architecture | 8 → 32 → 16 → 1 |
| Total parameters | 833 |
| Coq proof | `coq/ThresholdLogic.v` + `coq/Weights.v` |

### Pruned Network

Neuron ablation analysis revealed that only 11 of 32 Layer-1 neurons and 3 of 16 Layer-2 neurons are critical for correctness. Removing the redundant neurons yields a minimal subnetwork with identical behavior.

| Parameter | Value |
|-----------|-------|
| Architecture | 8 → 11 → 3 → 1 |
| Total parameters | 139 |
| Reduction | 83.3% |
| Coq proof | `coq/PrunedThresholdLogic.v` |

## Project Structure

```
threshold-logic-verified/
├── src/
│   ├── model.py          # Network architecture
│   ├── train.py          # Training script
│   └── export_coq.py     # JSON to Coq converter
├── coq/
│   ├── ThresholdLogic.v  # Core definitions
│   ├── Weights.v         # Full network weights and proof
│   └── PrunedThresholdLogic.v  # Pruned network (self-contained)
└── README.md
```

## Usage

1. Train the network:
   ```
   python src/train.py --export weights.json
   ```

2. Convert weights to Coq:
   ```
   python src/export_coq.py weights.json
   ```

3. Compile and verify:
   ```
   coqc coq/ThresholdLogic.v
   coqc coq/Weights.v
   coqc coq/PrunedThresholdLogic.v
   ```

## Verification

Both networks are proven correct by exhaustive enumeration of all 256 possible 8-bit inputs. The main theorems establish that for every input, the network output equals the parity function.

```coq
Theorem network_verified :
  forall xs, In xs (all_inputs 8) -> network xs = parity xs.
```

Additional properties proven include bit-flip invariance: `network(NOT x) = network(x)`.

## HuggingFace

Trained weights are available at [phanerozoic/tiny-parity-prover](https://huggingface.co/phanerozoic/tiny-parity-prover).

## Requirements

- Python 3.10+
- PyTorch
- Coq 8.19+

## License

MIT
