#!/usr/bin/env python3
"""
Running Example from Paper (Example 1.1)
Demonstrates batch-stream-graph transformations with categorical semantics.

PODS 2026 Submission - Anonymous
"""

from dataclasses import dataclass
from typing import List, Dict, Any, Callable
from collections import Counter
import time


@dataclass
class StreamEvent:
    """A stream event with value and timestamp."""
    value: Any
    timestamp: int
    multiplicity: int = 1


@dataclass
class BatchResult:
    """A batch query result as a multiset."""
    data: Counter
    
    def __repr__(self):
        return f"BatchResult({dict(self.data)})"


@dataclass
class StreamResult:
    """A stream of results over time."""
    events: List[StreamEvent]
    watermark: int
    
    def current_result(self) -> Counter:
        """Get current accumulated result."""
        result = Counter()
        for e in self.events:
            if e.timestamp <= self.watermark:
                result[e.value] += e.multiplicity
        return result


# =============================================================================
# FUNCTORS: F_BS (Batch → Stream) and G_SB (Stream → Batch)
# =============================================================================

def F_BS(batch: BatchResult) -> StreamResult:
    """
    Batch-to-Stream functor (Definition 4.1).
    Embeds a batch as a finite stream with sequential timestamps.
    """
    events = []
    timestamp = 0
    for value, count in batch.data.items():
        for _ in range(count):
            events.append(StreamEvent(value=value, timestamp=timestamp))
            timestamp += 1
    return StreamResult(events=events, watermark=timestamp)


def G_SB(stream: StreamResult, window_size: int) -> BatchResult:
    """
    Stream-to-Batch functor (Definition 4.2).
    Extracts a window of events as a batch.
    """
    result = Counter()
    for e in stream.events[:window_size]:
        result[e.value] += e.multiplicity
    return BatchResult(data=result)


# =============================================================================
# QUERIES
# =============================================================================

def sum_query(batch: BatchResult) -> int:
    """Simple sum aggregation query."""
    return sum(k * v for k, v in batch.data.items())


def selection_query(batch: BatchResult, predicate: Callable) -> BatchResult:
    """Selection σ_φ."""
    return BatchResult(data=Counter({k: v for k, v in batch.data.items() if predicate(k)}))


def projection_query(batch: BatchResult, proj_func: Callable) -> BatchResult:
    """Projection π_f."""
    result = Counter()
    for k, v in batch.data.items():
        result[proj_func(k)] += v
    return BatchResult(data=result)


# =============================================================================
# KAN EXTENSION: Streaming Query Extension
# =============================================================================

def kan_extension_sum(stream: StreamResult) -> List[tuple]:
    """
    Left Kan extension of sum query along F_BS.
    Lan_{F_BS}(sum) : Stream → Results
    
    Demonstrates Theorem 5.4: (Lan_K Q)(S + Δ) = (Lan_K Q)(S) ⊕ Q(Δ)
    """
    running_sum = 0
    results = []
    
    for event in stream.events:
        if event.timestamp <= stream.watermark:
            # Delta decomposition: new result = old result + delta(new event)
            delta = event.value * event.multiplicity
            running_sum += delta
            results.append((event.timestamp, running_sum, delta))
    
    return results


# =============================================================================
# Z-RELATIONS: Retractions
# =============================================================================

def demonstrate_z_relations():
    """
    Demonstrate Z-relations with retractions (Section 6).
    Shows that insertions and retractions cancel correctly.
    """
    print("\n=== Z-Relations with Retractions ===\n")
    
    # Initial stream with positive multiplicities
    events = [
        StreamEvent(value=10, timestamp=1, multiplicity=1),
        StreamEvent(value=20, timestamp=2, multiplicity=1),
        StreamEvent(value=30, timestamp=3, multiplicity=1),
    ]
    stream = StreamResult(events=events, watermark=3)
    
    print(f"Initial stream: {[(e.value, e.multiplicity) for e in stream.events]}")
    print(f"Running sum: {sum(e.value * e.multiplicity for e in stream.events)}")
    
    # Add retraction (negative multiplicity)
    stream.events.append(StreamEvent(value=20, timestamp=4, multiplicity=-1))
    stream.watermark = 4
    
    print(f"\nAfter retraction of 20:")
    print(f"Stream: {[(e.value, e.multiplicity) for e in stream.events]}")
    print(f"Running sum: {sum(e.value * e.multiplicity for e in stream.events)}")
    
    # Verify: 10 + 20 + 30 - 20 = 40
    expected = 40
    actual = sum(e.value * e.multiplicity for e in stream.events)
    assert actual == expected, f"Expected {expected}, got {actual}"
    print(f"✓ Retraction correctly applied: sum = {actual}")


# =============================================================================
# MAIN DEMONSTRATION
# =============================================================================

def main():
    print("=" * 60)
    print("Running Example from Paper (Example 1.1)")
    print("Category-Theoretic Foundations for Cross-Paradigm Data Processing")
    print("=" * 60)
    
    # Create batch data
    print("\n=== Batch Processing ===\n")
    batch = BatchResult(data=Counter({10: 1, 20: 1, 30: 1}))
    print(f"Batch data: {batch}")
    print(f"Sum query result: {sum_query(batch)}")
    
    # Transform to stream via F_BS
    print("\n=== Batch-to-Stream Transformation (F_BS) ===\n")
    stream = F_BS(batch)
    print(f"Stream events: {[(e.value, e.timestamp) for e in stream.events]}")
    print(f"Watermark: {stream.watermark}")
    
    # Apply Kan extension of sum
    print("\n=== Kan Extension of Sum (Theorem 5.4) ===\n")
    streaming_results = kan_extension_sum(stream)
    print("Event-by-event processing:")
    for ts, running, delta in streaming_results:
        print(f"  t={ts}: value={delta:+d} → running sum = {running}")
    
    # Verify Kan extension preserves semantics
    print("\n=== Semantic Preservation Verification ===\n")
    batch_result = sum_query(batch)
    stream_result = streaming_results[-1][1] if streaming_results else 0
    
    print(f"Batch query result: {batch_result}")
    print(f"Stream query result (final): {stream_result}")
    
    if batch_result == stream_result:
        print("✓ Kan extension preserves semantics (Theorem 5.4)")
    else:
        print("✗ MISMATCH - check implementation")
    
    # Transform back to batch via G_SB
    print("\n=== Stream-to-Batch Transformation (G_SB) ===\n")
    window_size = 3
    recovered_batch = G_SB(stream, window_size)
    print(f"Window size W = {window_size}")
    print(f"Recovered batch: {recovered_batch}")
    
    # Verify round-trip (Theorem 4.10)
    if batch.data == recovered_batch.data:
        print("✓ Round-trip preserves data when |D| ≤ W (Theorem 4.10)")
    
    # Demonstrate Z-relations
    demonstrate_z_relations()
    
    # Delta rule demonstration
    print("\n=== Delta Rules (Theorem 5.5) ===\n")
    
    # Original state
    R = BatchResult(data=Counter({1: 1, 2: 1, 3: 1}))
    delta_R = BatchResult(data=Counter({4: 1}))
    
    print(f"Initial R: {R}")
    print(f"Update ΔR: {delta_R}")
    
    # Selection with predicate x > 1
    predicate = lambda x: x > 1
    
    # Full recompute
    R_plus_delta = BatchResult(data=R.data + delta_R.data)
    full_result = selection_query(R_plus_delta, predicate)
    
    # Incremental (delta rule)
    R_filtered = selection_query(R, predicate)
    delta_filtered = selection_query(delta_R, predicate)
    incremental_result = BatchResult(data=R_filtered.data + delta_filtered.data)
    
    print(f"\nSelection σ_(x>1):")
    print(f"  Full recompute: {full_result}")
    print(f"  Incremental:    {incremental_result}")
    
    if full_result.data == incremental_result.data:
        print("  ✓ Delta rule correct: σ_φ(R + ΔR) = σ_φ(R) + σ_φ(ΔR)")
    
    print("\n" + "=" * 60)
    print("Demonstration complete.")
    print("=" * 60)


if __name__ == "__main__":
    main()
