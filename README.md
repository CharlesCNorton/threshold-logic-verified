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

## Initial Target

**Task**: n-bit parity (XOR of all input bits)

| Parameter | Value |
|-----------|-------|
| Input bits | 8 |
| Layer 1 | 16 neurons |
| Layer 2 | 8 neurons |
| Output | 1 neuron |
| Total parameters | 289 |

Verification: exhaustive enumeration of all 256 inputs in Coq.

## Project Structure

```
threshold-logic-verified/
├── src/
│   ├── model.py       # Network architecture
│   ├── train.py       # Training script
│   └── export_coq.py  # JSON to Coq converter
├── coq/
│   └── ThresholdLogic.v  # Definitions and proofs
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

3. Insert the output into `coq/ThresholdLogic.v` and compile:
   ```
   coqc coq/ThresholdLogic.v
   ```

## Requirements

- Python 3.10+
- PyTorch
- Coq 8.19+

## License

MIT
