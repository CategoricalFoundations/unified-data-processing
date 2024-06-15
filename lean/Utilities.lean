/-
  Utilities.lean
  Helper definitions and basic structures for categorical data processing
  
  PODS 2026 Submission - Anonymous
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Colimits
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Basic

open CategoryTheory

/-! ## Universe Setup -/

universe u v w

/-! ## Typed Universe for Data -/

/-- Base types in the data universe -/
inductive BaseType : Type where
  | int : BaseType
  | string : BaseType
  | bool : BaseType
  | float : BaseType
  deriving DecidableEq, Repr

/-- A schema is a list of base types -/
abbrev Schema := List BaseType

/-- Values in the typed universe -/
inductive Value : BaseType → Type where
  | int : Int → Value BaseType.int
  | string : String → Value BaseType.string  
  | bool : Bool → Value BaseType.bool
  | float : Float → Value BaseType.float
  deriving Repr

/-- A tuple conforming to a schema -/
def Tuple : Schema → Type
  | [] => Unit
  | [t] => Value t
  | t :: ts => Value t × Tuple ts

/-! ## Finite Multisets -/

/-- Finite multiset over a type -/
abbrev FMultiset (α : Type*) := Multiset α

/-- Finite multiset with schema -/
structure TypedMultiset (σ : Schema) where
  data : FMultiset (Tuple σ)
  deriving Repr

/-! ## Timestamps and Watermarks -/

/-- Timestamp type (non-negative reals, approximated as rationals) -/
abbrev Timestamp := Nat

/-- Watermark indicating event-time progress -/
structure Watermark where
  value : Timestamp
  deriving DecidableEq, Repr

/-! ## Stream Events -/

/-- A stream event with value, timestamp, and optional multiplicity -/
structure StreamEvent (α : Type*) where
  value : α
  timestamp : Timestamp
  multiplicity : Int := 1
  deriving Repr

/-- Predicate for causal stream transformers -/
def IsCausal {α β : Type*} (f : List (StreamEvent α) → List (StreamEvent β)) : Prop :=
  ∀ (prefix suffix : List (StreamEvent α)),
    (f prefix).length ≤ (f (prefix ++ suffix)).length ∧
    ∀ i, i < (f prefix).length → (f prefix).get? i = (f (prefix ++ suffix)).get? i

/-! ## Graph Structures -/

/-- A labeled directed graph -/
structure LabeledGraph (V E : Type*) where
  vertices : Finset V
  edges : V → V → Bool
  vertexLabel : V → E
  edgeLabel : V → V → Option E

/-! ## Window Parameters -/

/-- Window size for stream-to-batch conversion -/
structure WindowSize where
  size : Nat
  size_pos : size > 0

/-! ## Z-Relations -/

/-- Z-relation: function from tuples to integers with finite support -/
structure ZRelation (α : Type*) [DecidableEq α] where
  multiplicity : α → Int
  support : Finset α
  support_spec : ∀ a, multiplicity a ≠ 0 ↔ a ∈ support

namespace ZRelation

variable {α : Type*} [DecidableEq α]

/-- Zero Z-relation -/
def zero : ZRelation α where
  multiplicity := fun _ => 0
  support := ∅
  support_spec := by simp

/-- Addition of Z-relations -/
def add (R S : ZRelation α) : ZRelation α where
  multiplicity := fun a => R.multiplicity a + S.multiplicity a
  support := R.support ∪ S.support
  support_spec := by
    intro a
    simp only [Finset.mem_union, ne_eq]
    constructor
    · intro h
      by_contra h'
      push_neg at h'
      have hr := (R.support_spec a).mpr.mt h'.1
      have hs := (S.support_spec a).mpr.mt h'.2
      simp at hr hs
      omega
    · intro h
      cases h with
      | inl hr => 
        have := (R.support_spec a).mp hr
        omega
      | inr hs =>
        have := (S.support_spec a).mp hs
        omega

/-- Negation of Z-relation -/
def neg (R : ZRelation α) : ZRelation α where
  multiplicity := fun a => -R.multiplicity a
  support := R.support
  support_spec := by
    intro a
    simp only [neg_ne_zero]
    exact R.support_spec a

instance : Zero (ZRelation α) := ⟨zero⟩
instance : Add (ZRelation α) := ⟨add⟩
instance : Neg (ZRelation α) := ⟨neg⟩

/-- Z-relations form an additive group -/
instance : AddCommGroup (ZRelation α) where
  add_assoc := by intros; ext; simp [add, add_assoc]
  zero_add := by intros; ext; simp [add, zero]
  add_zero := by intros; ext; simp [add, zero]
  add_comm := by intros; ext; simp [add, add_comm]
  add_left_neg := by intros; ext; simp [add, neg, zero]
  nsmul := nsmulRec
  zsmul := zsmulRec

end ZRelation

/-! ## Helper Lemmas -/

/-- List take preserves membership for elements in range -/
lemma List.get?_take_of_lt {α : Type*} (l : List α) (n i : Nat) (h : i < n) :
    (l.take n).get? i = l.get? i := by
  simp [List.get?_take, h]

/-- Multiset cardinality is non-negative -/
lemma Multiset.card_nonneg {α : Type*} (m : Multiset α) : 0 ≤ m.card := by
  exact Nat.zero_le m.card

end -- namespace
