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


def train(
    n_bits=8,
    hidden1=16,
    hidden2=8,
    epochs=10000,
    lr=0.1,
    batch_size=None,
    device='cuda',
    verbose=True,
):
    """Train the threshold network on parity."""

    if not torch.cuda.is_available() and device == 'cuda':
        device = 'cpu'
        print("CUDA not available, using CPU")

    inputs = generate_all_inputs(n_bits).to(device)
    targets = parity(inputs).to(device)

    if batch_size is None:
        batch_size = len(inputs)

    model = ThresholdNetwork(n_bits, hidden1, hidden2).to(device)

    if verbose:
        print(f"Model parameters: {model.count_parameters()}")
        print(f"Training on {len(inputs)} inputs")
        print(f"Device: {device}")

    optimizer = optim.Adam(model.parameters(), lr=lr)
    criterion = nn.BCELoss()

    best_accuracy = 0.0
    best_weights = None

    for epoch in range(epochs):
        model.train()

        perm = torch.randperm(len(inputs))
        total_loss = 0.0

        for i in range(0, len(inputs), batch_size):
            idx = perm[i:i+batch_size]
            x = inputs[idx]
            y = targets[idx]

            optimizer.zero_grad()
            out = model(x)
            loss = criterion(out, y)
            loss.backward()
            optimizer.step()

            total_loss += loss.item()

        if (epoch + 1) % 100 == 0 or epoch == 0:
            model.eval()
            with torch.no_grad():
                correct, accuracy, _ = verify_network(model, n_bits)

            if accuracy > best_accuracy:
                best_accuracy = accuracy
                best_weights = model.export_weights()

            if verbose:
                status = "VERIFIED" if correct else f"{accuracy*100:.2f}%"
                print(f"Epoch {epoch+1}: loss={total_loss:.4f}, accuracy={status}")

            if correct:
                if verbose:
                    print(f"\nNetwork verified correct at epoch {epoch+1}!")
                return model, True

    return model, False


def export_for_coq(model, output_path):
    """Export model weights to JSON for Coq verification."""
    weights = model.export_weights()
    with open(output_path, 'w') as f:
        json.dump(weights, f, indent=2)
    print(f"Weights exported to {output_path}")


def main():
    parser = argparse.ArgumentParser(description='Train threshold network on parity')
    parser.add_argument('--n-bits', type=int, default=8, help='Number of input bits')
    parser.add_argument('--hidden1', type=int, default=16, help='First hidden layer size')
    parser.add_argument('--hidden2', type=int, default=8, help='Second hidden layer size')
    parser.add_argument('--epochs', type=int, default=10000, help='Training epochs')
    parser.add_argument('--lr', type=float, default=0.1, help='Learning rate')
    parser.add_argument('--device', type=str, default='cuda', help='Device (cuda/cpu)')
    parser.add_argument('--export', type=str, default=None, help='Export weights to JSON')
    args = parser.parse_args()

    model, verified = train(
        n_bits=args.n_bits,
        hidden1=args.hidden1,
        hidden2=args.hidden2,
        epochs=args.epochs,
        lr=args.lr,
        device=args.device,
    )

    if verified:
        print("\nFinal verification: PASSED")
        if args.export:
            export_for_coq(model, args.export)
        else:
            export_for_coq(model, 'weights.json')
    else:
        correct, accuracy, errors = verify_network(model, args.n_bits)
        print(f"\nFinal verification: FAILED ({accuracy*100:.2f}% correct)")
        if errors is not None:
            print(f"Number of errors: {len(errors[0])}")


if __name__ == '__main__':
    main()
