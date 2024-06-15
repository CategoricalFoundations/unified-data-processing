/-
  Demonstration.lean
  Executable semantics demonstrating theoretical results
  
  PODS 2026 Submission - Anonymous
  
  This module provides runnable implementations that demonstrate
  the categorical constructs in action.
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Basic

/-! ## Executable Running Example (Example 1.1) -/

/-- Transaction record -/
structure Transaction where
  id : Nat
  amount : Int
  timestamp : Nat
  deriving Repr, DecidableEq

/-- Batch sum query -/
def batchSum (txns : Multiset Transaction) : Int :=
  txns.toList.map (·.amount) |>.sum

/-- Example 1.1: Batch computation -/
#eval batchSum ⟨[⟨1, 10, 0⟩, ⟨2, 20, 0⟩, ⟨3, 30, 0⟩], rfl⟩  -- Expected: 60

/-! ## Stream Processing with Delta Rules -/

/-- Incremental sum update (Theorem 5.5) -/
def deltaSum (current : Int) (delta : Multiset Transaction) : Int :=
  current + batchSum delta

/-- Demonstrate delta decomposition -/
example : 
    let R := ⟨[⟨1, 10, 0⟩, ⟨2, 20, 0⟩, ⟨3, 30, 0⟩], rfl⟩
    let ΔR := ⟨[⟨4, 40, 0⟩], rfl⟩
    batchSum (R + ΔR) = deltaSum (batchSum R) ΔR := by
  native_decide

/-! ## Z-Relations with Retractions -/

/-- Z-relation: tuple with multiplicity -/
structure ZTuple (α : Type*) where
  value : α
  multiplicity : Int
  deriving Repr

/-- Collapse Z-stream to final state -/
def collapse (zstream : List (ZTuple α)) : List (α × Int) :=
  zstream.foldl (fun acc zt => 
    match acc.find? (·.1 == zt.value) with
    | some (v, m) => acc.map (fun (v', m') => if v' == v then (v', m' + zt.multiplicity) else (v', m'))
    | none => acc ++ [(zt.value, zt.multiplicity)]
  ) []

/-- Example 6.7: Retraction semantics -/
#eval collapse [⟨"a", 1⟩, ⟨"b", 1⟩, ⟨"a", -1⟩]  
-- Expected: [("a", 0), ("b", 1)] → effectively {b}

/-! ## Correction Monad for Late Data -/

/-- Correction pair: (current_result, pending_corrections) -/
structure Correction (α : Type*) [Add α] where
  current : α
  pending : α
  deriving Repr

/-- Apply corrections to get final result -/
def Correction.apply [Add α] (c : Correction α) : α := c.current + c.pending

/-- Monad unit: η(r) = (r, 0) -/
def Correction.pure [Add α] [Zero α] (r : α) : Correction α := ⟨r, 0⟩

/-- Demonstrate eventual preservation (Theorem 7.4) -/
example :
    let ontime := Correction.pure 60  -- On-time result
    let late := Correction.mk 60 (-20)  -- With late correction
    late.apply = 40 := by rfl

/-! ## Paradigm Transformation Demo -/

/-- F_BS: Batch to Stream -/
def batchToStream (batch : List α) : List (α × Nat) :=
  batch.enum.map fun ⟨i, x⟩ => (x, i)

/-- G_SB: Stream to Batch (window extraction) -/
def streamToBatch (stream : List (α × Nat)) (windowSize : Nat) : List α :=
  stream.filter (·.2 < windowSize) |>.map (·.1)

/-- Round-trip preservation (Corollary 4.3) -/
example :
    let batch := [1, 2, 3]
    let stream := batchToStream batch
    let recovered := streamToBatch stream 10  -- Window larger than batch
    recovered = batch := by rfl

/-! ## Complexity Validation -/

/-- Count comparisons in sort (for Theorem 8.1 validation) -/
def countingSort (xs : List Nat) : Nat × List Nat :=
  let rec merge (comparisons : Nat) : List Nat → List Nat → Nat × List Nat
    | [], ys => (comparisons, ys)
    | xs, [] => (comparisons, xs)
    | x::xs, y::ys => 
        if x ≤ y then 
          let (c, rest) := merge (comparisons + 1) xs (y::ys)
          (c, x :: rest)
        else 
          let (c, rest) := merge (comparisons + 1) (x::xs) ys
          (c, y :: rest)
  let rec mergeSort : List Nat → Nat × List Nat
    | [] => (0, [])
    | [x] => (0, [x])
    | xs => 
        let mid := xs.length / 2
        let (c1, left) := mergeSort (xs.take mid)
        let (c2, right) := mergeSort (xs.drop mid)
        let (c3, merged) := merge 0 left right
        (c1 + c2 + c3, merged)
  mergeSort xs

/-- Empirical O(n log n) validation -/
#eval countingSort [5, 2, 8, 1, 9, 3, 7, 4, 6]  
-- Shows comparison count ≈ n log n
