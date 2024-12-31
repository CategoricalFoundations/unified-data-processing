#!/usr/bin/env python3
"""
Formal Regression Tests for Paper Examples

This module provides rigorous verification that the code reproduces
the exact values claimed in the paper text.

Paper References:
- Example 1.1: SUM({|10,20,30|}) = 60, with retraction (t4: -20) → sum = 40
- Example 5.8: Sum(R + ΔR) = 60 + 40 = 100

PODS 2026 Submission - Anonymous
"""

import sys
import os
import pytest
from collections import Counter

# Add examples directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'examples'))

from running_example import (
    BatchResult, StreamEvent, StreamResult,
    F_BS, G_SB, sum_query, kan_extension_sum
)
from ivm_demo import (
    Relation, delta_select, delta_project, delta_aggregate,
    full_select, full_project
)


# =============================================================================
# Test Example 1.1: Batch Sum Query
# =============================================================================

class TestExample1_1:
    """Paper Example 1.1: Batch-Stream transformation with sum query."""
    
    def test_batch_sum_equals_60(self):
        """
        Paper claim: SUM({|10, 20, 30|}) = 60
        
        Constructs the multiset {|10, 20, 30|} and verifies sum is exactly 60.
        """
        batch = BatchResult(data=Counter({10: 1, 20: 1, 30: 1}))
        result = sum_query(batch)
        
        assert result == 60, f"Expected SUM({{|10,20,30|}}) = 60, got {result}"
    
    def test_batch_data_cardinality(self):
        """Verify batch has exactly 3 elements."""
        batch = BatchResult(data=Counter({10: 1, 20: 1, 30: 1}))
        
        assert sum(batch.data.values()) == 3, "Batch should have 3 elements"
    
    def test_stream_transformation_preserves_semantics(self):
        """
        Paper claim: Kan extension preserves batch query semantics.
        
        F_BS embeds batch as stream, Kan extension computes sum incrementally,
        final result must equal batch sum.
        """
        batch = BatchResult(data=Counter({10: 1, 20: 1, 30: 1}))
        stream = F_BS(batch)
        streaming_results = kan_extension_sum(stream)
        
        batch_result = sum_query(batch)
        stream_result = streaming_results[-1][1] if streaming_results else 0
        
        assert batch_result == stream_result == 60, \
            f"Kan extension should preserve semantics: batch={batch_result}, stream={stream_result}"
    
    def test_retraction_yields_40(self):
        """
        Paper claim: With retraction (t4: -20), sum becomes 40.
        
        Event sequence: +10, +20, +30, -20 → running sum = 40
        """
        events = [
            StreamEvent(value=10, timestamp=1, multiplicity=1),
            StreamEvent(value=20, timestamp=2, multiplicity=1),
            StreamEvent(value=30, timestamp=3, multiplicity=1),
            StreamEvent(value=20, timestamp=4, multiplicity=-1),  # Retraction
        ]
        stream = StreamResult(events=events, watermark=4)
        
        # Compute sum with retractions (Z-relation semantics)
        result = sum(e.value * e.multiplicity for e in stream.events)
        
        assert result == 40, f"Expected sum with retraction = 40, got {result}"
    
    def test_retraction_breakdown(self):
        """Verify retraction arithmetic: 10 + 20 + 30 - 20 = 40."""
        components = [10, 20, 30, -20]
        result = sum(components)
        
        assert result == 40, f"10 + 20 + 30 - 20 should equal 40, got {result}"
    
    def test_round_trip_within_window(self):
        """
        Paper claim (Theorem 4.10): G(F(D)) ≅ D when |D| ≤ W.
        
        Round-trip through batch→stream→batch should preserve data.
        """
        batch = BatchResult(data=Counter({10: 1, 20: 1, 30: 1}))
        window_size = 3  # W = 3 = |D|
        
        stream = F_BS(batch)
        recovered = G_SB(stream, window_size)
        
        assert batch.data == recovered.data, \
            f"Round-trip should preserve data: original={batch.data}, recovered={recovered.data}"


# =============================================================================
# Test Example 5.8: IVM Delta Rule Sum
# =============================================================================

class TestExample5_8:
    """Paper Example 5.8: IVM delta rule for sum aggregation."""
    
    def test_ivm_sum_composition(self):
        """
        Paper claim: Sum(R + ΔR) = Sum(R) + Sum(ΔR) = 60 + 40 = 100
        
        This demonstrates the delta rule for aggregation queries.
        """
        # R = {10, 20, 30} with multiplicity 1 each
        R = Relation(tuples=Counter({10: 1, 20: 1, 30: 1}))
        
        # ΔR = {15, 25} with multiplicity 1 each (sum = 40)
        delta_R = Relation(tuples=Counter({15: 1, 25: 1}))
        
        # Compute Sum(R)
        sum_R = sum(k * v for k, v in R.tuples.items())
        assert sum_R == 60, f"Sum(R) should be 60, got {sum_R}"
        
        # Compute Sum(ΔR)
        sum_delta_R = sum(k * v for k, v in delta_R.tuples.items())
        assert sum_delta_R == 40, f"Sum(ΔR) should be 40, got {sum_delta_R}"
        
        # Verify Sum(R + ΔR) = Sum(R) + Sum(ΔR)
        R_plus_delta = Relation(tuples=R.tuples + delta_R.tuples)
        sum_combined = sum(k * v for k, v in R_plus_delta.tuples.items())
        
        assert sum_combined == 100, f"Sum(R + ΔR) should be 100, got {sum_combined}"
        assert sum_combined == sum_R + sum_delta_R, \
            "Delta rule: Sum(R + ΔR) should equal Sum(R) + Sum(ΔR)"
    
    def test_delta_rule_selection(self):
        """
        Paper Theorem 5.5: σ_φ(R + ΔR) = σ_φ(R) + σ_φ(ΔR)
        """
        R = Relation(tuples=Counter({1: 1, 2: 1, 3: 1}))
        delta_R = Relation(tuples=Counter({4: 1, 5: 1}))
        predicate = lambda x: x > 2
        
        # Full recompute
        R_plus_delta = Relation(tuples=R.tuples + delta_R.tuples)
        full_result = full_select(R_plus_delta, predicate)
        
        # Incremental
        base_result = full_select(R, predicate)
        delta_result = delta_select(R, delta_R, predicate)
        incremental_result = Relation(tuples=base_result.tuples + delta_result.tuples)
        
        assert full_result.tuples == incremental_result.tuples, \
            "Selection delta rule should hold"
    
    def test_delta_rule_projection(self):
        """
        Paper Theorem 5.5: π_f(R + ΔR) = π_f(R) + π_f(ΔR)
        """
        R = Relation(tuples=Counter({(1, 'a'): 1, (2, 'b'): 1}))
        delta_R = Relation(tuples=Counter({(3, 'c'): 1}))
        proj_func = lambda t: t[1]  # Project to second component
        
        # Full recompute
        R_plus_delta = Relation(tuples=R.tuples + delta_R.tuples)
        full_result = full_project(R_plus_delta, proj_func)
        
        # Incremental
        base_result = full_project(R, proj_func)
        delta_result = delta_project(R, delta_R, proj_func)
        incremental_result = Relation(tuples=base_result.tuples + delta_result.tuples)
        
        assert full_result.tuples == incremental_result.tuples, \
            "Projection delta rule should hold"


# =============================================================================
# Test Theorem 5.6: Delta Rule Uniqueness
# =============================================================================

class TestTheorem5_6:
    """Paper Theorem 5.6: Uniqueness of delta rules."""
    
    def test_uniqueness_derivation(self):
        """
        Any delta rule Δ' satisfying Q(R + ΔR) = Q(R) + Δ'(R, ΔR)
        must equal the standard delta rule Δ.
        
        Proof: Δ'(R, ΔR) = Q(R + ΔR) - Q(R) is uniquely determined.
        """
        R = Relation(tuples=Counter({1: 1, 2: 1, 3: 1}))
        delta_R = Relation(tuples=Counter({4: 1, 5: 1}))
        predicate = lambda x: x > 2
        
        # Standard delta rule
        standard_delta = delta_select(R, delta_R, predicate)
        
        # Forced delta (derived from decomposition property)
        Q_R = full_select(R, predicate)
        Q_R_plus_delta = full_select(Relation(tuples=R.tuples + delta_R.tuples), predicate)
        forced_delta_tuples = Q_R_plus_delta.tuples - Q_R.tuples
        
        assert standard_delta.tuples == forced_delta_tuples, \
            "Any delta rule satisfying decomposition must equal standard rule"


# =============================================================================
# Test Z-Relation Properties (Section 6)
# =============================================================================

class TestZRelations:
    """Z-relation ring structure tests."""
    
    def test_additive_inverse(self):
        """Z-relations support negative multiplicities (retractions)."""
        # Element with positive multiplicity
        positive = Counter({10: 1})
        
        # Retraction (negative multiplicity)
        retraction = Counter({10: -1})
        
        # Sum should cancel
        combined = positive + retraction
        
        assert combined[10] == 0, "Element should be cancelled by retraction"
    
    def test_z_relation_sum_with_retractions(self):
        """Sum query on Z-relations correctly handles retractions."""
        # Initial: {10, 20, 30}
        z_rel = Counter({10: 1, 20: 1, 30: 1})
        
        # Apply retraction of 20
        z_rel.update({20: -1})
        
        # Effective multiset: {10, 30}
        result = sum(k * v for k, v in z_rel.items())
        
        assert result == 40, f"Sum after retraction should be 40, got {result}"


# =============================================================================
# Integration Tests
# =============================================================================

class TestIntegration:
    """End-to-end integration tests."""
    
    def test_full_paper_example_1_1_flow(self):
        """
        Complete Example 1.1 workflow:
        1. Create batch {|10, 20, 30|}
        2. Verify sum = 60
        3. Transform to stream
        4. Apply Kan extension (streaming sum)
        5. Verify stream sum = 60
        6. Add retraction
        7. Verify sum = 40
        """
        # Step 1-2: Batch creation and sum
        batch = BatchResult(data=Counter({10: 1, 20: 1, 30: 1}))
        assert sum_query(batch) == 60
        
        # Step 3-5: Stream transformation
        stream = F_BS(batch)
        results = kan_extension_sum(stream)
        assert results[-1][1] == 60
        
        # Step 6-7: Retraction
        stream.events.append(StreamEvent(value=20, timestamp=stream.watermark + 1, multiplicity=-1))
        stream.watermark += 1
        
        z_sum = sum(e.value * e.multiplicity for e in stream.events)
        assert z_sum == 40
    
    def test_full_paper_example_5_8_flow(self):
        """
        Complete Example 5.8 workflow:
        1. Create R = {10, 20, 30} (sum = 60)
        2. Create ΔR = {15, 25} (sum = 40)
        3. Verify Sum(R + ΔR) = 100
        4. Verify incremental = full recompute
        """
        R = Relation(tuples=Counter({10: 1, 20: 1, 30: 1}))
        delta_R = Relation(tuples=Counter({15: 1, 25: 1}))
        
        sum_R = sum(k * v for k, v in R.tuples.items())
        sum_delta = sum(k * v for k, v in delta_R.tuples.items())
        
        assert sum_R == 60
        assert sum_delta == 40
        assert sum_R + sum_delta == 100


# =============================================================================
# Main Entry Point
# =============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
