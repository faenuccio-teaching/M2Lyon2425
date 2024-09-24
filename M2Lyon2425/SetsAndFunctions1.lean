import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common

open Set Classical

open scoped Set
section Definitions

-- # §1: Definitions

-- **A tautology**

example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  sorry

-- **The positive integers**

def PositiveIntegers : Set ℤ := by
  sorry

-- `⌘`

lemma one_pos : 1 ∈ PositiveIntegers := by sorry

def PositiveNaturals : Set ℕ := by sorry

example : 1 ∈ PositiveNaturals := by sorry

-- Why does this *fail*? How to fix it?
example : (-1) ∉ PositiveNaturals := sorry

-- **The even naturals**

def EvenNaturals : Set ℕ := by
  sorry

example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  sorry


-- **An abstract set**
def AbstractSet {α : Type} (P : α → Prop) : Set α := sorry
def AbstractSet' {α : Type} (P : α → Prop) : Set α := by sorry

-- The same, but it is a general principle that the second version is better
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := sorry


-- `⌘`

-- **Subsets as implication**
example {α : Type} (S T : Set α) (s : α) (hST : S ⊆ T) (hs : s ∈ S) : s ∈ T := by sorry



-- `⌘`

-- **A double inclusion**

example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  sorry

-- **Another take on subsets and sets as types**

def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := sorry

def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := sorry

-- Are they *equal*? This is an exercise below.

-- Why does this *fail*? How to fix it?
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : x ∈ S := sorry


-- **What is really this "injection"  `Set α ↪ Type`?**

-- Why does this *fail*? How to fix it?
example : ∀ n : PositiveIntegers, 0 ≤ n := by sorry


-- `⌘`

/- **§ Some exercises** -/

example : 1 ∉ EvenNaturals := by
  sorry

example : -1 ∉ PositiveIntegers := by
  sorry

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := by
  sorry

-- Why does this *fail*? How to fix it?
example : 1 ∉ EvenPositiveNaturals := sorry


-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := sorry

example : 3 ∈ OddNaturals := by sorry


example (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  sorry


-- Why does this *fail*?
example (α : Type) (S : Set α) : subsub = subsub' := sorry


end Definitions

-- # §2. Operations

section Operations

-- **Self-intersection is the identity, proven with extensionality**

example (α : Type) (S : Set α) : S ∩ S = S := by
  sorry


-- `⌘`


-- **The union**

example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  sorry


-- **An _unfixable_ problem**

example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry

-- `⌘`


-- **Empty set**

example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  sorry


-- `⌘`


-- **Complement and difference**

example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  sorry

-- `⌘`

-- **§ Indexed unions**

example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  sorry



example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  sorry

/- **§ Some exercises** -/

-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  sorry

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  sorry


-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  sorry

-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := by
  sorry

-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  sorry

example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  sorry


-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  sorry

end Operations
