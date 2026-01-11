"""
Random search for parity network - gradient-free optimization.
"""

import json
import torch
import numpy as np
from model import ThresholdNetwork, generate_all_inputs, parity, verify_network


def random_ternary_network(n_bits, hidden1, hidden2, device='cuda'):
    """Create network with random ternary weights."""
    model = ThresholdNetwork(n_bits, hidden1, hidden2).to(device)

    with torch.no_grad():
        for layer in [model.layer1, model.layer2, model.output]:
            layer.weight.data = torch.randint(-1, 2, layer.weight.shape, dtype=torch.float32, device=device)
            layer.bias.data = torch.randint(-layer.bias_bound, layer.bias_bound + 1,
                                            layer.bias.shape, dtype=torch.float32, device=device)
    return model


def mutate_network(model, mutation_rate=0.1, device='cuda'):
    """Mutate a network by randomly changing some weights."""
    new_model = ThresholdNetwork(model.n_bits,
                                  model.layer1.out_features,
                                  model.layer2.out_features).to(device)

    with torch.no_grad():
        for old_layer, new_layer in [(model.layer1, new_model.layer1),
                                      (model.layer2, new_model.layer2),
                                      (model.output, new_model.output)]:
            new_layer.weight.data = old_layer.weight.data.clone()
            new_layer.bias.data = old_layer.bias.data.clone()

            mask = torch.rand_like(new_layer.weight) < mutation_rate
            mutations = torch.randint(-1, 2, new_layer.weight.shape,
                                      dtype=torch.float32, device=device)
            new_layer.weight.data[mask] = mutations[mask]

            bias_mask = torch.rand_like(new_layer.bias) < mutation_rate
            bias_mutations = torch.randint(-new_layer.bias_bound, new_layer.bias_bound + 1,
                                           new_layer.bias.shape, dtype=torch.float32, device=device)
            new_layer.bias.data[bias_mask] = bias_mutations[bias_mask]

    return new_model


def evaluate(model, inputs, targets):
    """Count correct predictions."""
    with torch.no_grad():
        outputs = model.forward_discrete(inputs)
        return (outputs == targets).sum().item()


def random_search(n_bits=8, hidden1=32, hidden2=16, max_iterations=100000,
                  device='cuda', verbose=True):
    """Pure random search."""

    if not torch.cuda.is_available() and device == 'cuda':
        device = 'cpu'

    inputs = generate_all_inputs(n_bits).to(device)
    targets = parity(inputs).to(device)
    n_total = len(inputs)

    best_model = None
    best_score = 0

    for i in range(max_iterations):
        model = random_ternary_network(n_bits, hidden1, hidden2, device)
        score = evaluate(model, inputs, targets)

        if score > best_score:
            best_score = score
            best_model = model
            if verbose:
                print(f"Iteration {i}: {score}/{n_total} ({100*score/n_total:.2f}%)")

            if score == n_total:
                print(f"\nFound perfect solution at iteration {i}!")
                return model, True

        if verbose and i % 10000 == 0 and i > 0:
            print(f"Iteration {i}: best so far = {best_score}/{n_total}")

    return best_model, False


def hill_climb(model, inputs, targets, max_iterations=10000, device='cuda', verbose=True):
    """Hill climbing from a starting point."""
    n_total = len(inputs)
    current_score = evaluate(model, inputs, targets)

    for i in range(max_iterations):
        for mutation_rate in [0.01, 0.05, 0.1, 0.2]:
            candidate = mutate_network(model, mutation_rate, device)
            score = evaluate(candidate, inputs, targets)

            if score > current_score:
                model = candidate
                current_score = score
                if verbose:
                    print(f"Hill climb {i}: {score}/{n_total} ({100*score/n_total:.2f}%)", flush=True)

                if score == n_total:
                    return model, True
                break

    return model, False


def exhaustive_local_search(model, inputs, targets, device='cuda', verbose=True):
    """Try flipping each weight to find improvements."""
    n_total = len(inputs)
    current_score = evaluate(model, inputs, targets)
    improved = True

    while improved:
        improved = False
        for layer in [model.layer1, model.layer2, model.output]:
            for i in range(layer.weight.shape[0]):
                for j in range(layer.weight.shape[1]):
                    original = layer.weight.data[i, j].item()
                    for new_val in [-1, 0, 1]:
                        if new_val != original:
                            layer.weight.data[i, j] = new_val
                            score = evaluate(model, inputs, targets)
                            if score > current_score:
                                current_score = score
                                improved = True
                                if verbose:
                                    print(f"Improved to {score}/{n_total} ({100*score/n_total:.2f}%)", flush=True)
                                if score == n_total:
                                    return model, True
                            else:
                                layer.weight.data[i, j] = original

            for i in range(layer.bias.shape[0]):
                original = layer.bias.data[i].item()
                for delta in [-1, 1]:
                    new_val = original + delta
                    if -layer.bias_bound <= new_val <= layer.bias_bound:
                        layer.bias.data[i] = new_val
                        score = evaluate(model, inputs, targets)
                        if score > current_score:
                            current_score = score
                            improved = True
                            if verbose:
                                print(f"Improved to {score}/{n_total} ({100*score/n_total:.2f}%)", flush=True)
                            if score == n_total:
                                return model, True
                        else:
                            layer.bias.data[i] = original

    return model, False


def evolutionary_search(n_bits=8, hidden1=32, hidden2=16, population_size=100,
                        generations=1000, device='cuda', verbose=True):
    """Simple evolutionary algorithm."""

    if not torch.cuda.is_available() and device == 'cuda':
        device = 'cpu'

    inputs = generate_all_inputs(n_bits).to(device)
    targets = parity(inputs).to(device)
    n_total = len(inputs)

    population = [random_ternary_network(n_bits, hidden1, hidden2, device)
                  for _ in range(population_size)]

    best_ever = None
    best_ever_score = 0
    last_improvement = 0

    for gen in range(generations):
        scores = [evaluate(m, inputs, targets) for m in population]

        best_idx = np.argmax(scores)
        best_score = scores[best_idx]

        if best_score > best_ever_score:
            best_ever_score = best_score
            best_ever = population[best_idx]
            if verbose:
                print(f"Gen {gen}: {best_score}/{n_total} ({100*best_score/n_total:.2f}%)", flush=True)

        if best_score == n_total:
            print(f"\nFound perfect solution at generation {gen}!")
            return population[best_idx], True

        sorted_indices = np.argsort(scores)[::-1]
        elite_size = population_size // 5
        elite = [population[i] for i in sorted_indices[:elite_size]]

        new_population = elite[:]

        if best_score > best_ever_score:
            last_improvement = gen

        while len(new_population) < population_size:
            parent_idx = np.random.randint(elite_size)
            parent = elite[parent_idx]

            r = np.random.random()
            if r < 0.4:
                child = mutate_network(parent, mutation_rate=0.05, device=device)
            elif r < 0.7:
                child = mutate_network(parent, mutation_rate=0.15, device=device)
            elif r < 0.85:
                child = mutate_network(parent, mutation_rate=0.3, device=device)
            else:
                child = random_ternary_network(n_bits, hidden1, hidden2, device)

            new_population.append(child)

        population = new_population

        if verbose and gen % 100 == 0 and gen > 0:
            print(f"Gen {gen}: best = {best_ever_score}/{n_total}", flush=True)

    return best_ever, False


def main():
    import argparse
    parser = argparse.ArgumentParser(description='Random search for parity network')
    parser.add_argument('--n-bits', type=int, default=8)
    parser.add_argument('--hidden1', type=int, default=32)
    parser.add_argument('--hidden2', type=int, default=16)
    parser.add_argument('--method', choices=['random', 'evolutionary', 'hybrid'], default='evolutionary')
    parser.add_argument('--iterations', type=int, default=100000)
    parser.add_argument('--population', type=int, default=200)
    parser.add_argument('--generations', type=int, default=2000)
    parser.add_argument('--device', type=str, default='cuda')
    parser.add_argument('--export', type=str, default='weights.json')
    args = parser.parse_args()

    if args.method == 'random':
        model, success = random_search(args.n_bits, args.hidden1, args.hidden2,
                                       args.iterations, args.device)
    elif args.method == 'evolutionary':
        model, success = evolutionary_search(args.n_bits, args.hidden1, args.hidden2,
                                             args.population, args.generations, args.device)
    elif args.method == 'hybrid':
        print("Phase 1: Evolutionary search for good starting point...")
        model, success = evolutionary_search(args.n_bits, args.hidden1, args.hidden2,
                                             args.population, args.generations // 2, args.device)
        if not success:
            print("\nPhase 2: Exhaustive local search...")
            inputs = generate_all_inputs(args.n_bits).to(args.device)
            targets = parity(inputs).to(args.device)
            model, success = exhaustive_local_search(model, inputs, targets, args.device)

    if success:
        print("\nVERIFIED - Perfect solution found!")
    else:
        correct, accuracy, n_errors, _ = verify_network(model, args.n_bits)
        print(f"\nBest solution: {accuracy*100:.2f}% ({n_errors} errors)")

    weights = model.export_weights()
    with open(args.export, 'w') as f:
        json.dump(weights, f, indent=2)
    print(f"Weights saved to {args.export}")


if __name__ == '__main__':
    main()
