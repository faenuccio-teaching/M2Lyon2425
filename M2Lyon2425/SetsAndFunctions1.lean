import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common

open Set Classical

open scoped Set
section Definitions

-- # §1: Definitions

-- **An error**
example (S : Set) := sorry

-- `⌘`

-- **A tautology**

example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  sorry

-- **The positive integers**

def PositiveIntegers : Set ℤ := (0 < ·)

-- `⌘`

lemma one_pos : 1 ∈ PositiveIntegers := by sorry

def PositiveNaturals : Set ℕ := (0 < ·)

example : 1 ∈ PositiveNaturals := by sorry

-- Why does this *fail*? How to fix it?
example : (-1) ∉ PositiveIntegers := by
  intro h
  replace h := h.out

-- **The even naturals**

def EvenNaturals : Set ℕ := (· % 2 = 0)

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

def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := P

def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := by
  intro a
  exact P a

-- Are they *equal*? This is an exercise below.

-- Why does this *fail*? How to fix it?
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : x ∈ S := sorry


-- **What is really this "injection"  `Set α ↪ Type`?**

-- Why does this *fail*? How to fix it?
example : ∀ n : PositiveIntegers, 0 ≤ n := by sorry


-- `⌘`

/- **§ Some exercises** -/

example : 1 ∉ EvenNaturals := by
  intro h
  replace := h.out
  exact Nat.succ_ne_self 0 (by rwa [Nat.mod_succ] at this)

example : -1 ∉ PositiveIntegers := by
  intro h
  replace := h.out
  rw [Int.neg_pos] at this
  have := Int.one_pos
  contradiction

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers :=
  setOf fun x ↦ x.1 % 2 = 0

-- Why does this *fail*? How to fix it?
example : ⟨1, Int.one_pos⟩ ∉ EvenPositiveNaturals := by
  intro h
  replace := h.out
  rw [Int.emod_eq_of_lt Int.one_nonneg _] at this
  exact Int.zero_ne_one this.symm
  rw [← Int.ofNat_one, ← Int.ofNat_two, Int.ofNat_lt]
  exact Nat.lt_add_one 1

-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := setOf (· % 2 = 1)

example : 3 ∈ OddNaturals := by
  change 3 % 2 = 1
  rw [← @Nat.succ_mod_two_eq_zero_iff 3]

example (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  refine ⟨fun h h₂ ↦ ?_, fun h ↦ ?_⟩
  · replace h := h.out
    replace h₂ := h₂.out
    exact Nat.succ_ne_self 0 (by rwa [h] at h₂)
  · change ¬n % 2 = 0 at h
    rwa [Nat.mod_two_ne_zero] at h

-- Why does this *fail*?
#print subsub
-- subsub is a function which takes a term of type (Set S) and returns
-- a term of type (Set S)
#print subsub'
-- subsub' is a function which takes a term of type (Set α) and returns
-- a term of type (Set S)
-- Consequently, subsub and subsub' don't have the same type
-- and the arguments of = must be of the same type
example (α : Type) (S : Set α) : subsub = subsub' := sorry


end Definitions

-- # §2. Operations

section Operations

-- **Self-intersection is the identity, proven with extensionality**

example (α : Type) (S : Set α) : S ∩ S = S := by
  ext s
  constructor
  · intro h
    exact h.right
  · intro h
    constructor
    · exact h
    · exact h


-- `⌘`


-- **The union**

example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  sorry


-- **An _unfixable_ problem**

example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry

-- `⌘`


-- **Empty set**

example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  ext d
  constructor
  · rintro ⟨hd_pos, hd_neg⟩
    rw [mem_setOf_eq] at hd_neg
    rw [lt_iff_not_le] at hd_neg
    apply hd_neg
    apply le_of_lt
    exact hd_pos
  · intro h
    exfalso
    exact h

-- `⌘`


-- **Complement and difference**

example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  sorry

-- `⌘`

-- **§ Indexed unions**

example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  sorry

def Intervals : ℕ → Set ℤ := by
  exact fun (n: ℕ) ↦ (fun m ↦ (-n : ℤ) ≤ m ∧ m ≤ n)

example : ⋂ n, Intervals n = {0} := sorry

example : ⋃ n, Intervals n = univ := sorry

example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  sorry

/- **§ Some exercises** -/

-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · change x ∈ S ∨ x ∈ T
    right
    exact h
  · change x ∈ S ∨ x ∈ T at h
    cases h with
    | inl h => exact H h
    | inr h => exact h

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases h with
    | intro left right =>
        cases right with
        | inl h =>
          left
          exact ⟨left, h⟩
        | inr h =>
          right
          exact ⟨left, h⟩
  · cases h with
    | inl h =>
        refine ⟨h.1, ?_⟩
        left
        exact h.2
    | inr h =>
        refine ⟨h.1, ?_⟩
        right
        exact h.2

-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  ext x
  refine ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ ?_⟩
  change x ∈ {x | 0 ≤ x} ∧ x ∈ {x | x ≤ 0}
  rw [h, mem_setOf_eq, mem_setOf_eq]
  exact ⟨le_refl 0, le_refl 0⟩

-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := by
  ext x
  refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  change x % 2 = 0 ∨ x % 2 = 1
  by_contra H
  have := Nat.le_pred_of_lt (x.mod_lt Nat.two_pos)
  rw [Nat.pred_eq_sub_one, Nat.add_one_sub_one, Nat.le_add_one_iff,
    Nat.le_zero_eq, zero_add] at this
  exact H this

-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  ext _
  refine ⟨fun h₂ ↦ h₂.2 (h h₂.1), fun h₂ ↦ ⟨?_, fun _ ↦ h₂⟩⟩
  exfalso
  exact h₂

example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  change ∀ x, x ∈ S \ (T ∪ R) → x ∈ (S \ T) \ R
  refine fun x hx ↦ ⟨⟨hx.1, ?_⟩, ?_⟩
  · have := hx.2
    change ¬(x ∈ T ∨ x ∈ R) at this
    push_neg at this
    exact this.1
  · have := hx.2
    change ¬(x ∈ T ∨ x ∈ R) at this
    push_neg at this
    exact this.2

-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · rw [mem_iInter] at h ⊢
    exact fun i ↦ (h i).1
  · rw [mem_iInter] at h ⊢
    exact fun i ↦ (h i).2
  · cases h with
  | intro left right =>
      rw [mem_iInter] at left right ⊢
      exact fun i ↦ ⟨left i, right i⟩

end Operations
