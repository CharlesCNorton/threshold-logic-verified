"""
Binary Threshold Network for Parity Learning.

Architecture:
- Input: n bits in {0, 1}
- Weights: ternary in {-1, 0, +1}
- Biases: bounded integers in [-max_fan_in, +max_fan_in]
- Activation: Heaviside (x >= 0 -> 1, else 0)
- Output: single bit
"""

import torch
import torch.nn as nn


class StraightThroughTernary(torch.autograd.Function):
    """Straight-through estimator for ternary quantization with temperature."""

    @staticmethod
    def forward(ctx, x, temperature):
        if temperature <= 0:
            return torch.sign(torch.round(x)).clamp(-1, 1)
        else:
            soft = torch.tanh(x / temperature)
            return soft

    @staticmethod
    def backward(ctx, grad_output):
        return grad_output, None


class StraightThroughHeaviside(torch.autograd.Function):
    """Straight-through estimator for Heaviside with temperature."""

    @staticmethod
    def forward(ctx, x, temperature):
        if temperature <= 0:
            return (x >= 0).float()
        else:
            return torch.sigmoid(x / temperature)

    @staticmethod
    def backward(ctx, grad_output):
        return grad_output, None


def ternary(x, temperature=0):
    return StraightThroughTernary.apply(x, temperature)


def heaviside(x, temperature=0):
    return StraightThroughHeaviside.apply(x, temperature)


class TernaryLinear(nn.Module):
    """Linear layer with ternary weights and integer biases."""

    def __init__(self, in_features, out_features, bias_bound):
        super().__init__()
        self.in_features = in_features
        self.out_features = out_features
        self.bias_bound = bias_bound

        self.weight = nn.Parameter(torch.zeros(out_features, in_features))
        self.bias = nn.Parameter(torch.zeros(out_features))

        self._init_weights()

    def _init_weights(self):
        nn.init.uniform_(self.weight, -1.5, 1.5)
        nn.init.uniform_(self.bias, -self.bias_bound, self.bias_bound)

    def forward(self, x, temperature=0):
        w = ternary(self.weight, temperature)
        b = torch.round(self.bias).clamp(-self.bias_bound, self.bias_bound)
        return torch.nn.functional.linear(x, w, b)

    def get_discrete_weights(self):
        """Extract discrete weights for verification."""
        w = torch.sign(torch.round(self.weight)).clamp(-1, 1).int()
        b = torch.round(self.bias).clamp(-self.bias_bound, self.bias_bound).int()
        return w, b

    def l1_loss(self):
        """L1 penalty to encourage sparsity."""
        return torch.abs(self.weight).mean()


class ThresholdNetwork(nn.Module):
    """
    Binary threshold network for n-bit parity.

    Architecture:
        Input (n) -> TernaryLinear (k1) -> Heaviside
                  -> TernaryLinear (k2) -> Heaviside
                  -> TernaryLinear (1)  -> Heaviside -> Output

    Bias bounds: each layer uses fan-in as bound (max possible activation).
    """

    def __init__(self, n_bits=8, hidden1=16, hidden2=8):
        super().__init__()
        self.n_bits = n_bits

        self.layer1 = TernaryLinear(n_bits, hidden1, bias_bound=n_bits)
        self.layer2 = TernaryLinear(hidden1, hidden2, bias_bound=hidden1)
        self.output = TernaryLinear(hidden2, 1, bias_bound=hidden2)

    def forward(self, x, temperature=0):
        x = heaviside(self.layer1(x, temperature), temperature)
        x = heaviside(self.layer2(x, temperature), temperature)
        x = heaviside(self.output(x, temperature), temperature)
        return x.squeeze(-1)

    def forward_discrete(self, x):
        """Forward pass with explicitly discretized weights."""
        w1, b1 = self.layer1.get_discrete_weights()
        w2, b2 = self.layer2.get_discrete_weights()
        w3, b3 = self.output.get_discrete_weights()

        x = x.float()
        x = (torch.nn.functional.linear(x, w1.float(), b1.float()) >= 0).float()
        x = (torch.nn.functional.linear(x, w2.float(), b2.float()) >= 0).float()
        x = (torch.nn.functional.linear(x, w3.float(), b3.float()) >= 0).float()
        return x.squeeze(-1)

    def l1_loss(self):
        """Total L1 penalty across all layers."""
        return (self.layer1.l1_loss() +
                self.layer2.l1_loss() +
                self.output.l1_loss())

    def export_weights(self):
        """Export all discrete weights for Coq verification."""
        w1, b1 = self.layer1.get_discrete_weights()
        w2, b2 = self.layer2.get_discrete_weights()
        w3, b3 = self.output.get_discrete_weights()

        return {
            'layer1': {'weight': w1.tolist(), 'bias': b1.tolist()},
            'layer2': {'weight': w2.tolist(), 'bias': b2.tolist()},
            'output': {'weight': w3.tolist(), 'bias': b3.tolist()},
        }

    def count_parameters(self):
        """Count total parameters."""
        total = 0
        for layer in [self.layer1, self.layer2, self.output]:
            total += layer.weight.numel() + layer.bias.numel()
        return total


def parity(x):
    """Ground truth parity function."""
    return x.sum(dim=-1) % 2


def generate_all_inputs(n_bits):
    """Generate all 2^n binary input vectors in MSB-first order (matches Coq)."""
    n = 2 ** n_bits
    inputs = torch.zeros(n, n_bits)
    for i in range(n):
        for j in range(n_bits):
            inputs[i, j] = (i >> (n_bits - 1 - j)) & 1
    return inputs


def verify_network(model, n_bits):
    """Exhaustively verify network correctness on all inputs."""
    inputs = generate_all_inputs(n_bits)
    targets = parity(inputs)
    outputs = model.forward_discrete(inputs)

    correct = (outputs == targets).all().item()
    accuracy = (outputs == targets).float().mean().item()
    n_errors = (outputs != targets).sum().item()

    if not correct:
        errors = (outputs != targets).nonzero(as_tuple=True)[0]
        error_inputs = inputs[errors]
        error_outputs = outputs[errors]
        error_targets = targets[errors]
        return False, accuracy, n_errors, (error_inputs, error_outputs, error_targets)

    return True, 1.0, 0, None
