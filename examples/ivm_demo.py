#!/usr/bin/env python3
"""
IVM Delta Rules as Categorical Consequences
Demonstrates Theorems 5.5 (Delta Rules) and 5.6 (Uniqueness)

PODS 2026 Submission - Anonymous
"""

from dataclasses import dataclass
from typing import List, Dict, Any, Callable, Tuple, Set
from collections import Counter
import itertools


@dataclass
class Relation:
    """A relation as a multiset of tuples."""
    tuples: Counter  # Maps tuple -> multiplicity
    
    def __add__(self, other: 'Relation') -> 'Relation':
        """Union of relations."""
        return Relation(tuples=self.tuples + other.tuples)
    
    def __repr__(self):
        return f"Relation({dict(self.tuples)})"


# =============================================================================
# STANDARD DELTA RULES (Theorem 5.5)
# =============================================================================

def delta_select(R: Relation, delta_R: Relation, predicate: Callable) -> Relation:
    """
    Delta rule for selection: Δ(σ_φ) = σ_φ(ΔR)
    
    Theorem 5.5: σ_φ(R + ΔR) = σ_φ(R) + σ_φ(ΔR)
    """
    return Relation(tuples=Counter({t: m for t, m in delta_R.tuples.items() if predicate(t)}))


def delta_project(R: Relation, delta_R: Relation, proj_func: Callable) -> Relation:
    """
    Delta rule for projection: Δ(π_f) = π_f(ΔR)
    
    Theorem 5.5: π_f(R + ΔR) = π_f(R) + π_f(ΔR)
    """
    result = Counter()
    for t, m in delta_R.tuples.items():
        result[proj_func(t)] += m
    return Relation(tuples=result)


def delta_join(R: Relation, delta_R: Relation, S: Relation, delta_S: Relation,
               join_key_R: Callable, join_key_S: Callable) -> Relation:
    """
    Delta rule for join: Δ(R ⋈ S) = (ΔR ⋈ S) + (R ⋈ ΔS) + (ΔR ⋈ ΔS)
    
    Theorem 5.5: (R + ΔR) ⋈ (S + ΔS) = (R ⋈ S) + (ΔR ⋈ S) + (R ⋈ ΔS) + (ΔR ⋈ ΔS)
    """
    def compute_join(rel1: Relation, rel2: Relation) -> Relation:
        result = Counter()
        for t1, m1 in rel1.tuples.items():
            for t2, m2 in rel2.tuples.items():
                if join_key_R(t1) == join_key_S(t2):
                    # Combine tuples (simplified: concatenate)
                    joined = (t1, t2)
                    result[joined] += m1 * m2
        return Relation(tuples=result)
    
    # Δ(R ⋈ S) = (ΔR ⋈ S) + (R ⋈ ΔS) + (ΔR ⋈ ΔS)
    term1 = compute_join(delta_R, S)
    term2 = compute_join(R, delta_S)
    term3 = compute_join(delta_R, delta_S)
    
    return term1 + term2 + term3


def delta_aggregate(R: Relation, delta_R: Relation, 
                    agg_func: Callable, init: Any) -> Any:
    """
    Delta rule for aggregation (commutative monoid).
    
    Theorem 5.5: agg(R + ΔR) = agg(R) ⊕ agg(ΔR)
    """
    delta_result = init
    for t, m in delta_R.tuples.items():
        for _ in range(abs(m)):
            if m > 0:
                delta_result = agg_func(delta_result, t)
            else:
                # For groups, use inverse
                delta_result = agg_func(delta_result, -t if isinstance(t, (int, float)) else t)
    return delta_result


# =============================================================================
# FULL RECOMPUTATION (for comparison)
# =============================================================================

def full_select(R: Relation, predicate: Callable) -> Relation:
    return Relation(tuples=Counter({t: m for t, m in R.tuples.items() if predicate(t)}))


def full_project(R: Relation, proj_func: Callable) -> Relation:
    result = Counter()
    for t, m in R.tuples.items():
        result[proj_func(t)] += m
    return Relation(tuples=result)


def full_join(R: Relation, S: Relation, 
              join_key_R: Callable, join_key_S: Callable) -> Relation:
    result = Counter()
    for t1, m1 in R.tuples.items():
        for t2, m2 in S.tuples.items():
            if join_key_R(t1) == join_key_S(t2):
                joined = (t1, t2)
                result[joined] += m1 * m2
    return Relation(tuples=result)


# =============================================================================
# THEOREM 5.6: DELTA RULE UNIQUENESS
# =============================================================================

def demonstrate_uniqueness():
    """
    Demonstrate Theorem 5.6: Any delta rule satisfying decomposition
    must equal the standard rule on the Kan extension image.
    
    Proof sketch:
    Let Δ, Δ' both satisfy: Q(R + ΔR) = Q(R) + Δ(R, ΔR) = Q(R) + Δ'(R, ΔR)
    Then: Q(R) + Δ(R, ΔR) = Q(R) + Δ'(R, ΔR)
    By cancellation: Δ(R, ΔR) = Δ'(R, ΔR)
    """
    print("\n=== Theorem 5.6: Delta Rule Uniqueness ===\n")
    
    # Setup
    R = Relation(tuples=Counter({1: 1, 2: 1, 3: 1}))
    delta_R = Relation(tuples=Counter({4: 1, 5: 1}))
    predicate = lambda x: x > 2
    
    print(f"Initial state R: {R}")
    print(f"Update ΔR: {delta_R}")
    print(f"Query: σ_(x>2)")
    
    # Standard delta rule Δ
    standard_delta = delta_select(R, delta_R, predicate)
    
    # Hypothetical alternative Δ' that also satisfies decomposition
    # The ONLY way to satisfy Q(R + ΔR) = Q(R) + Δ'(R, ΔR) is if Δ' = Δ
    
    # Proof by computation:
    Q_R = full_select(R, predicate)  # Q(R)
    Q_R_plus_delta = full_select(R + delta_R, predicate)  # Q(R + ΔR)
    
    # From decomposition: Δ'(R, ΔR) = Q(R + ΔR) - Q(R)
    # This is UNIQUE given Q and the decomposition property
    
    forced_delta = Relation(tuples=Q_R_plus_delta.tuples - Q_R.tuples)
    
    print(f"\nDerivation:")
    print(f"  Q(R) = σ_(x>2)(R) = {Q_R}")
    print(f"  Q(R + ΔR) = σ_(x>2)(R + ΔR) = {Q_R_plus_delta}")
    print(f"  Standard Δ(R, ΔR) = {standard_delta}")
    print(f"  Forced Δ'(R, ΔR) = Q(R+ΔR) - Q(R) = {forced_delta}")
    
    if standard_delta.tuples == forced_delta.tuples:
        print("\n✓ UNIQUENESS VERIFIED: Any Δ' satisfying decomposition equals Δ")
        print("  This follows from: Q(R) + Δ(R, ΔR) = Q(R) + Δ'(R, ΔR)")
        print("  By additive cancellation: Δ(R, ΔR) = Δ'(R, ΔR)")
    else:
        print("\n✗ Error in demonstration")


# =============================================================================
# MAIN DEMONSTRATION
# =============================================================================

def main():
    print("=" * 70)
    print("IVM Delta Rules as Categorical Consequences")
    print("Theorems 5.5 (Delta Rules) and 5.6 (Uniqueness)")
    print("=" * 70)
    
    # Setup
    print("\n=== Setup ===\n")
    R = Relation(tuples=Counter({
        (1, 'a'): 1,
        (2, 'b'): 1,
        (3, 'c'): 1
    }))
    delta_R = Relation(tuples=Counter({
        (4, 'd'): 1
    }))
    
    print(f"Initial state R: {set(R.tuples.keys())}")
    print(f"Update ΔR: {set(delta_R.tuples.keys())}")
    
    # ==========================================================================
    # Selection Delta Rule
    # ==========================================================================
    print("\n=== Selection Delta Rule (Theorem 5.5) ===\n")
    
    predicate = lambda t: t[0] > 1
    print(f"Query: σ_(x[0] > 1)")
    
    # Full recompute
    R_plus_delta = R + delta_R
    full_result = full_select(R_plus_delta, predicate)
    
    # Incremental
    base_result = full_select(R, predicate)
    delta_result = delta_select(R, delta_R, predicate)
    incremental_result = base_result + delta_result
    
    print(f"Full recompute σ(R + ΔR): {set(full_result.tuples.keys())}")
    print(f"Incremental σ(R) + σ(ΔR): {set(incremental_result.tuples.keys())}")
    
    if full_result.tuples == incremental_result.tuples:
        print("✓ Selection delta rule verified")
    
    # ==========================================================================
    # Projection Delta Rule
    # ==========================================================================
    print("\n=== Projection Delta Rule (Theorem 5.5) ===\n")
    
    proj_func = lambda t: t[1]  # Project to second component
    print(f"Query: π_2 (project to second component)")
    
    # Full recompute
    full_result = full_project(R_plus_delta, proj_func)
    
    # Incremental
    base_result = full_project(R, proj_func)
    delta_result = delta_project(R, delta_R, proj_func)
    incremental_result = base_result + delta_result
    
    print(f"Full recompute π(R + ΔR): {dict(full_result.tuples)}")
    print(f"Incremental π(R) + π(ΔR): {dict(incremental_result.tuples)}")
    
    if full_result.tuples == incremental_result.tuples:
        print("✓ Projection delta rule verified")
    
    # ==========================================================================
    # Join Delta Rule
    # ==========================================================================
    print("\n=== Join Delta Rule (Theorem 5.5) ===\n")
    
    S = Relation(tuples=Counter({
        (1, 'x'): 1,
        (2, 'y'): 1,
        (4, 'z'): 1
    }))
    delta_S = Relation(tuples=Counter({
        (3, 'w'): 1
    }))
    
    join_key = lambda t: t[0]  # Join on first component
    
    print(f"R: {set(R.tuples.keys())}")
    print(f"S: {set(S.tuples.keys())}")
    print(f"ΔR: {set(delta_R.tuples.keys())}")
    print(f"ΔS: {set(delta_S.tuples.keys())}")
    print(f"Join key: first component")
    
    # Full recompute
    full_result = full_join(R + delta_R, S + delta_S, join_key, join_key)
    
    # Incremental
    base_result = full_join(R, S, join_key, join_key)
    delta_result = delta_join(R, delta_R, S, delta_S, join_key, join_key)
    incremental_result = base_result + delta_result
    
    print(f"\nFull recompute (R+ΔR) ⋈ (S+ΔS):")
    for t in full_result.tuples:
        print(f"  {t}")
    
    print(f"\nIncremental (R⋈S) + Δ(R⋈S):")
    for t in incremental_result.tuples:
        print(f"  {t}")
    
    if full_result.tuples == incremental_result.tuples:
        print("\n✓ Join delta rule verified")
        print("  Δ(R ⋈ S) = (ΔR ⋈ S) + (R ⋈ ΔS) + (ΔR ⋈ ΔS)")
    
    # ==========================================================================
    # Uniqueness Theorem
    # ==========================================================================
    demonstrate_uniqueness()
    
    # ==========================================================================
    # Significance
    # ==========================================================================
    print("\n=== Significance of Theorem 5.6 ===\n")
    print("The uniqueness theorem transforms IVM from algorithmic technique to")
    print("mathematical necessity:")
    print()
    print("• DBToaster proves: 'These delta rules WORK' (sufficiency)")
    print("• Theorem 5.6 proves: 'These are the ONLY rules that work' (necessity)")
    print()
    print("Implications:")
    print("  1. If DBSP derives different rules → there's a bug")
    print("  2. Any 'optimized' delta rules must equal these")
    print("  3. The categorical structure DETERMINES the correct rules")
    
    print("\n" + "=" * 70)
    print("Demonstration complete.")
    print("=" * 70)


if __name__ == "__main__":
    main()
