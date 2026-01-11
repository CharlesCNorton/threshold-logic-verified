"""
Training script for binary threshold network on parity task.
"""

import argparse
import json
import torch
import torch.nn as nn
import torch.optim as optim

from model import (
    ThresholdNetwork,
    parity,
    generate_all_inputs,
    verify_network,
)


def set_seed(seed):
    """Set all random seeds for reproducibility."""
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)
    torch.backends.cudnn.deterministic = True
    torch.backends.cudnn.benchmark = False


def get_temperature(epoch, total_epochs, start_temp=1.0, end_temp=0.0):
    """Anneal temperature from start to end over training."""
    progress = epoch / total_epochs
    return start_temp * (1 - progress) + end_temp * progress


def train_single(
    n_bits=8,
    hidden1=16,
    hidden2=8,
    epochs=10000,
    lr=0.01,
    l1_weight=0.001,
    grad_clip=1.0,
    start_temp=1.0,
    device='cuda',
    verbose=True,
    use_sgd=False,
):
    """Train a single network instance."""

    inputs = generate_all_inputs(n_bits).to(device)
    targets = parity(inputs).to(device)

    model = ThresholdNetwork(n_bits, hidden1, hidden2).to(device)

    if verbose:
        print(f"  Parameters: {model.count_parameters()}")

    if use_sgd:
        optimizer = optim.SGD(model.parameters(), lr=lr, momentum=0.9, nesterov=True)
    else:
        optimizer = optim.Adam(model.parameters(), lr=lr)

    best_accuracy = 0.0
    best_weights = None

    for epoch in range(epochs):
        model.train()
        temperature = get_temperature(epoch, epochs, start_temp, 0.0)

        optimizer.zero_grad()

        out = model(inputs, temperature)
        loss = ((out - targets) ** 2).mean()
        loss = loss + l1_weight * model.l1_loss()

        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), grad_clip)
        optimizer.step()

        if (epoch + 1) % 500 == 0 or epoch == 0:
            model.eval()
            with torch.no_grad():
                correct, accuracy, n_errors, _ = verify_network(model, n_bits)

            if accuracy > best_accuracy:
                best_accuracy = accuracy
                best_weights = model.export_weights()

            if verbose:
                status = "VERIFIED" if correct else f"{accuracy*100:.2f}% ({n_errors} errors)"
                print(f"  Epoch {epoch+1}: loss={loss.item():.4f}, temp={temperature:.3f}, {status}")

            if correct:
                return model, True, best_weights

    return model, False, best_weights


def train(
    n_bits=8,
    hidden1=16,
    hidden2=8,
    epochs=10000,
    lr=0.01,
    l1_weight=0.001,
    grad_clip=1.0,
    start_temp=1.0,
    n_restarts=5,
    seed=42,
    device='cuda',
    verbose=True,
):
    """Train with multiple restarts, keeping best result."""

    if not torch.cuda.is_available() and device == 'cuda':
        device = 'cpu'
        if verbose:
            print("CUDA not available, using CPU")

    if verbose:
        print(f"Training {n_bits}-bit parity with {n_restarts} restarts")
        print(f"Architecture: {n_bits} -> {hidden1} -> {hidden2} -> 1")
        print(f"Device: {device}, LR: {lr}, L1: {l1_weight}, Temp: {start_temp} -> 0")

    best_model = None
    best_weights = None
    best_accuracy = 0.0

    for restart in range(n_restarts):
        current_seed = seed + restart
        set_seed(current_seed)

        if verbose:
            print(f"\nRestart {restart+1}/{n_restarts} (seed={current_seed})")

        model, verified, weights = train_single(
            n_bits=n_bits,
            hidden1=hidden1,
            hidden2=hidden2,
            epochs=epochs,
            lr=lr,
            l1_weight=l1_weight,
            grad_clip=grad_clip,
            start_temp=start_temp,
            device=device,
            verbose=verbose,
            use_sgd=True,
        )

        if verified:
            if verbose:
                print(f"\nNetwork verified at restart {restart+1}!")
            return model, True, weights

        _, accuracy, _, _ = verify_network(model, n_bits)
        if accuracy > best_accuracy:
            best_accuracy = accuracy
            best_model = model
            best_weights = weights

    return best_model, False, best_weights


def verify_export(weights, n_bits, device='cpu'):
    """Verify exported weights before saving."""
    model = ThresholdNetwork(n_bits).to(device)

    w1 = torch.tensor(weights['layer1']['weight'], dtype=torch.float32)
    b1 = torch.tensor(weights['layer1']['bias'], dtype=torch.float32)
    w2 = torch.tensor(weights['layer2']['weight'], dtype=torch.float32)
    b2 = torch.tensor(weights['layer2']['bias'], dtype=torch.float32)
    w3 = torch.tensor(weights['output']['weight'], dtype=torch.float32)
    b3 = torch.tensor(weights['output']['bias'], dtype=torch.float32)

    model.layer1.weight.data = w1
    model.layer1.bias.data = b1
    model.layer2.weight.data = w2
    model.layer2.bias.data = b2
    model.output.weight.data = w3
    model.output.bias.data = b3

    correct, accuracy, n_errors, _ = verify_network(model, n_bits)
    return correct, accuracy, n_errors


def export_for_coq(weights, output_path, n_bits):
    """Export model weights to JSON after verification."""
    correct, accuracy, n_errors = verify_export(weights, n_bits)

    if not correct:
        print(f"WARNING: Exported weights fail verification ({accuracy*100:.2f}%, {n_errors} errors)")
        print("Saving anyway for debugging...")

    with open(output_path, 'w') as f:
        json.dump(weights, f, indent=2)

    if correct:
        print(f"Weights exported to {output_path} (VERIFIED)")
    else:
        print(f"Weights exported to {output_path} (UNVERIFIED)")

    return correct


def train_curriculum(
    target_bits=8,
    hidden1=64,
    hidden2=32,
    epochs_per_stage=5000,
    lr=0.01,
    l1_weight=0.0,
    grad_clip=1.0,
    start_temp=2.0,
    n_restarts=10,
    seed=42,
    device='cuda',
    verbose=True,
):
    """Train using curriculum learning: 2-bit -> 4-bit -> 8-bit."""

    if not torch.cuda.is_available() and device == 'cuda':
        device = 'cpu'
        if verbose:
            print("CUDA not available, using CPU")

    stages = [2, 4, target_bits]

    if verbose:
        print(f"Curriculum learning: {' -> '.join(map(str, stages))}-bit parity")
        print(f"Architecture: n -> {hidden1} -> {hidden2} -> 1")

    best_weights = None

    for stage_idx, n_bits in enumerate(stages):
        if verbose:
            print(f"\n{'='*50}")
            print(f"Stage {stage_idx+1}/{len(stages)}: {n_bits}-bit parity")
            print(f"{'='*50}")

        model, verified, weights = train(
            n_bits=n_bits,
            hidden1=hidden1,
            hidden2=hidden2,
            epochs=epochs_per_stage,
            lr=lr,
            l1_weight=l1_weight,
            grad_clip=grad_clip,
            start_temp=start_temp,
            n_restarts=n_restarts,
            seed=seed,
            device=device,
            verbose=verbose,
        )

        if n_bits == target_bits:
            if verified:
                return model, True, weights
            else:
                return model, False, weights

    return None, False, None


def main():
    parser = argparse.ArgumentParser(description='Train threshold network on parity')
    parser.add_argument('--n-bits', type=int, default=8, help='Number of input bits')
    parser.add_argument('--hidden1', type=int, default=64, help='First hidden layer size')
    parser.add_argument('--hidden2', type=int, default=32, help='Second hidden layer size')
    parser.add_argument('--epochs', type=int, default=10000, help='Training epochs per restart')
    parser.add_argument('--lr', type=float, default=0.01, help='Learning rate')
    parser.add_argument('--l1', type=float, default=0.0, help='L1 regularization weight')
    parser.add_argument('--grad-clip', type=float, default=1.0, help='Gradient clipping norm')
    parser.add_argument('--start-temp', type=float, default=2.0, help='Starting temperature')
    parser.add_argument('--restarts', type=int, default=10, help='Number of random restarts')
    parser.add_argument('--seed', type=int, default=42, help='Base random seed')
    parser.add_argument('--device', type=str, default='cuda', help='Device (cuda/cpu)')
    parser.add_argument('--export', type=str, default=None, help='Export weights to JSON')
    parser.add_argument('--curriculum', action='store_true', help='Use curriculum learning')
    args = parser.parse_args()

    if args.curriculum:
        model, verified, weights = train_curriculum(
            target_bits=args.n_bits,
            hidden1=args.hidden1,
            hidden2=args.hidden2,
            epochs_per_stage=args.epochs,
            lr=args.lr,
            l1_weight=args.l1,
            grad_clip=args.grad_clip,
            start_temp=args.start_temp,
            n_restarts=args.restarts,
            seed=args.seed,
            device=args.device,
        )
    else:
        model, verified, weights = train(
            n_bits=args.n_bits,
            hidden1=args.hidden1,
            hidden2=args.hidden2,
            epochs=args.epochs,
            lr=args.lr,
            l1_weight=args.l1,
            grad_clip=args.grad_clip,
            start_temp=args.start_temp,
            n_restarts=args.restarts,
            seed=args.seed,
            device=args.device,
        )

    if verified:
        print("\nFinal verification: PASSED")
    else:
        if model:
            correct, accuracy, n_errors, _ = verify_network(model, args.n_bits)
            print(f"\nFinal verification: FAILED ({accuracy*100:.2f}%, {n_errors} errors)")

    if weights:
        output_path = args.export if args.export else 'weights.json'
        export_for_coq(weights, output_path, args.n_bits)


if __name__ == '__main__':
    main()
