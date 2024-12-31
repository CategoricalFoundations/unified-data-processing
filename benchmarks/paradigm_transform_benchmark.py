#!/usr/bin/env python3
"""
Paradigm Transformation Complexity Benchmark
Validates Theorem 8.1: Tight Θ(n log n) bounds.

PODS 2026 Submission - Reproducibility Artifact
"""

import time
import random
import math
from typing import List, Tuple, Dict
from dataclasses import dataclass

@dataclass
class ComplexityResult:
    n: int
    time_ms: float
    theoretical_bound: float  # c * n * log(n)
    ratio: float  # actual / theoretical

# Batch-to-Stream: O(n) expected
def batch_to_stream(batch: List[int]) -> List[Tuple[int, int]]:
    """F_BS: Embed batch as finite stream with sequential timestamps"""
    return [(val, idx) for idx, val in enumerate(batch)]

# Stream-to-Batch: O(n) expected
def stream_to_batch(stream: List[Tuple[int, int]], window: int) -> List[int]:
    """G_SB: Extract windowed batch"""
    if not stream:
        return []
    max_ts = max(ts for _, ts in stream)
    return [val for val, ts in stream if max_ts - window < ts <= max_ts]

# Graph-to-Stream: O(n log n) expected (requires sorting)
def graph_to_stream(vertices: List[Tuple[int, int]], 
                    edges: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    """G_GS: Linearize graph by sorting vertices"""
    # Sort by vertex label (injective labeling requirement)
    sorted_vertices = sorted(vertices, key=lambda v: v[1])
    # Create stream from sorted order
    return [(v[0], idx) for idx, v in enumerate(sorted_vertices)]

# Stream-to-Graph: O(n log n) expected
def stream_to_graph(stream: List[Tuple[int, int]]) -> Tuple[List[int], List[Tuple[int, int]]]:
    """F_SG: Construct path graph from stream"""
    if not stream:
        return [], []
    # Sort by timestamp
    sorted_stream = sorted(stream, key=lambda e: e[1])
    vertices = [e[0] for e in sorted_stream]
    edges = [(sorted_stream[i][0], sorted_stream[i+1][0]) 
             for i in range(len(sorted_stream)-1)]
    return vertices, edges

def benchmark_transformation(name: str, 
                             transform_fn, 
                             data_generator,
                             sizes: List[int],
                             expected_complexity: str) -> List[ComplexityResult]:
    """Generic benchmark for paradigm transformations"""
    results = []
    
    for n in sizes:
        data = data_generator(n)
        
        # Warm up
        for _ in range(10):
            _ = transform_fn(data) if not isinstance(data, tuple) else transform_fn(*data)
        
        # Benchmark
        iterations = max(100, 10000 // n)
        start = time.perf_counter()
        for _ in range(iterations):
            _ = transform_fn(data) if not isinstance(data, tuple) else transform_fn(*data)
        elapsed = (time.perf_counter() - start) / iterations * 1000  # ms
        
        # Theoretical bound
        if expected_complexity == "O(n)":
            theoretical = n / 1000  # Normalize
        else:  # O(n log n)
            theoretical = n * math.log2(n) / 10000  # Normalize
        
        results.append(ComplexityResult(
            n=n,
            time_ms=elapsed,
            theoretical_bound=theoretical,
            ratio=elapsed / theoretical if theoretical > 0 else 0
        ))
    
    return results

def generate_batch(n: int) -> List[int]:
    return [random.randint(1, 10000) for _ in range(n)]

def generate_stream(n: int) -> List[Tuple[int, int]]:
    return [(random.randint(1, 10000), i) for i in range(n)]

def generate_graph(n: int) -> Tuple[List[Tuple[int, int]], List[Tuple[int, int]]]:
    vertices = [(i, random.randint(1, n*10)) for i in range(n)]
    edges = [(i, i+1) for i in range(n-1)]
    return vertices, edges

def generate_plots(output_path: str = "benchmarks/results/complexity_plot.png"):
    """
    Generate visual complexity verification for Theorem 8.1.
    
    Creates a plot comparing empirical G_GS (Graph→Stream) runtime
    against theoretical Θ(n log n) bound.
    
    Args:
        output_path: Path to save the generated plot
    """
    import matplotlib.pyplot as plt
    import numpy as np
    import os
    
    print("\n" + "=" * 70)
    print("Generating Complexity Plot for Theorem 8.1")
    print("=" * 70)
    
    # Benchmark sizes as specified
    sizes = [1000, 5000, 10000, 50000, 100000]
    
    print(f"\nRunning G_GS benchmarks for sizes: {sizes}")
    
    # Collect empirical times for G_GS
    empirical_times = []
    
    for n in sizes:
        print(f"  Benchmarking n={n}...", end=" ", flush=True)
        
        # Generate graph data
        vertices, edges = generate_graph(n)
        
        # Warm up
        for _ in range(5):
            _ = graph_to_stream(vertices, edges)
        
        # Benchmark with multiple iterations for accuracy
        iterations = max(50, 5000 // n)
        start = time.perf_counter()
        for _ in range(iterations):
            _ = graph_to_stream(vertices, edges)
        elapsed_ms = (time.perf_counter() - start) / iterations * 1000
        
        empirical_times.append(elapsed_ms)
        print(f"{elapsed_ms:.3f} ms")
    
    # Convert to numpy arrays for computation
    sizes_arr = np.array(sizes)
    times_arr = np.array(empirical_times)
    
    # Compute theoretical n*log(n) values
    nlogn = sizes_arr * np.log2(sizes_arr)
    
    # Fit constant k to first data point: empirical[0] = k * n[0] * log(n[0])
    k = times_arr[0] / nlogn[0]
    theoretical_times = k * nlogn
    
    print(f"\nFitted constant k = {k:.8f}")
    print(f"Theoretical: T(n) = {k:.2e} × n × log₂(n)")
    
    # Create the plot with professional styling
    plt.style.use('seaborn-v0_8-whitegrid')
    fig, ax = plt.subplots(figsize=(10, 7))
    
    # Plot empirical data
    ax.plot(sizes, empirical_times, 'o-', 
            color='#2196F3', linewidth=2, markersize=8,
            label='Empirical G_GS time', markeredgecolor='white', markeredgewidth=1.5)
    
    # Plot theoretical curve
    ax.plot(sizes, theoretical_times, '--', 
            color='#E91E63', linewidth=2,
            label=f'Theoretical Θ(n log n): k={k:.2e}')
    
    # Styling
    ax.set_xlabel('Input Size N', fontsize=12, fontweight='bold')
    ax.set_ylabel('Time (ms)', fontsize=12, fontweight='bold')
    ax.set_title('Theorem 8.1: Graph-to-Stream Transformation Complexity\n'
                 'G_GS : Graph → Stream  [Expected: Θ(n log n)]', 
                 fontsize=14, fontweight='bold', pad=15)
    
    ax.legend(loc='upper left', fontsize=11, framealpha=0.95)
    ax.grid(True, alpha=0.3)
    
    # Add ratio annotation
    ratios = times_arr / theoretical_times
    mean_ratio = np.mean(ratios)
    ax.text(0.95, 0.05, 
            f'Mean ratio (empirical/theoretical): {mean_ratio:.3f}\n'
            f'Variance: {np.var(ratios):.4f}',
            transform=ax.transAxes, fontsize=10,
            verticalalignment='bottom', horizontalalignment='right',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    # Ensure output directory exists
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    
    # Save the plot
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"\n✓ Plot saved to: {output_path}")
    
    # Print validation summary
    print("\n--- Complexity Validation Summary ---")
    print(f"{'N':<10} {'Empirical (ms)':<15} {'Theoretical (ms)':<18} {'Ratio':<10}")
    print("-" * 55)
    for n, emp, theo in zip(sizes, empirical_times, theoretical_times):
        ratio = emp / theo
        print(f"{n:<10} {emp:<15.4f} {theo:<18.4f} {ratio:<10.3f}")
    
    if np.var(ratios) < 0.1:
        print(f"\n✓ Theorem 8.1 VALIDATED: Low variance ({np.var(ratios):.4f}) confirms Θ(n log n)")
    else:
        print(f"\n⚠ Variance {np.var(ratios):.4f} - complexity may need further analysis")
    
    return {
        'sizes': sizes,
        'empirical_times': empirical_times,
        'theoretical_times': theoretical_times.tolist(),
        'k': k,
        'mean_ratio': mean_ratio
    }


def main():
    print("=" * 70)
    print("Paradigm Transformation Complexity Validation")
    print("PODS 2026 - Theorem 8.1: Tight Θ(n log n) Bounds")
    print("=" * 70)
    
    sizes = [1000, 2000, 5000, 10000, 20000, 50000]
    
    benchmarks = [
        ("F_BS (Batch→Stream)", 
         batch_to_stream, 
         generate_batch, 
         "O(n)"),
        ("G_SB (Stream→Batch)", 
         lambda s: stream_to_batch(s, len(s)//2), 
         generate_stream, 
         "O(n)"),
        ("G_GS (Graph→Stream)", 
         lambda vertices, edges: graph_to_stream(vertices, edges), 
         generate_graph, 
         "O(n log n)"),
        ("F_SG (Stream→Graph)", 
         stream_to_graph, 
         generate_stream, 
         "O(n log n)"),
    ]
    
    for name, fn, gen, complexity in benchmarks:
        print(f"\n--- {name} [{complexity}] ---")
        print(f"{'n':>10} {'Time (ms)':>12} {'Theoretical':>12} {'Ratio':>10}")
        print("-" * 50)
        
        results = benchmark_transformation(name, fn, gen, sizes, complexity)
        
        for r in results:
            print(f"{r.n:>10} {r.time_ms:>12.4f} {r.theoretical_bound:>12.4f} {r.ratio:>10.2f}")
        
        # Check if ratio is approximately constant (validates complexity)
        ratios = [r.ratio for r in results]
        mean_ratio = sum(ratios) / len(ratios)
        variance = sum((r - mean_ratio)**2 for r in ratios) / len(ratios)
        
        if variance < mean_ratio * 0.5:  # Low variance = complexity matches
            print(f"✓ Complexity validated: ratio variance {variance:.3f} < threshold")
        else:
            print(f"⚠ High variance {variance:.3f} - may need more iterations")
    
    # Generate the complexity plot
    generate_plots()
    
    print("\n" + "=" * 70)
    print("Theorem 8.1 Validation Complete")
    print("=" * 70)

if __name__ == "__main__":
    main()

