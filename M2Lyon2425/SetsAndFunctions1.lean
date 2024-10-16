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
-- example (S : Set) := sorry

-- `⌘`

-- **A tautology**

example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  rfl

-- **The positive integers**

def PositiveIntegers : Set ℤ := (0 < ·)

  -- `⌘`

lemma one_pos_int : 1 ∈ PositiveIntegers := Int.one_pos

def PositiveNaturals : Set ℕ := (0 < ·)

example : 1 ∈ PositiveNaturals := Nat.one_pos

-- Why does this *fail*? How to fix it?
example : (-1) ∉ PositiveIntegers := by
  intro hAbsu
  replace hAbsu : 0 < -1 := hAbsu
  exact (Int.negSucc_not_nonneg (0 + 0).succ).mp (by exact hAbsu)

-- **The even naturals**

def EvenNaturals : Set ℕ := (0 = · % 2)

lemma two_is_even : 2 ∈ EvenNaturals := by
  trivial

lemma EN_is_add_stable (n : Nat) (m : Nat) : (hn : n ∈ EvenNaturals) → (hm : m ∈ EvenNaturals) → (n+m) ∈ EvenNaturals := by
  intro hn hm
  replace hn := hn.out
  replace hm := hm.out
  change 0 = (n+m) % 2
  omega

example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  intro hn
  exact EN_is_add_stable n 2 hn two_is_even


-- **An abstract set**
--def AbstractSet {α : Type} (P : α → Prop) : Set α := sorry
--def AbstractSet' {α : Type} (P : α → Prop) : Set α := by sorry

-- The same, but it is a general principle that the second version is better
--example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := sorry


-- `⌘`

-- **Subsets as implication**
example {α : Type} (S T : Set α) (s : α) (hST : T ⊆ S) (hT : s ∈ T) : s ∈ S := hST hT

-- `⌘`

-- **A double inclusion**

example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  intro _ hS
  exact hTW (hST hS)

-- **Another take on subsets and sets as types**

--def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := sorry

--def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := sorry

-- Are they *equal*? This is an exercise below.

-- Why does this *fail*? How to fix it?
-- example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : x ∈ S := sorry


-- **What is really this "injection"  `Set α ↪ Type`?**

-- Why does this *fail*? How to fix it?
example : ∀ n : PositiveIntegers, 0 ≤ n.1 := by
  intro n
  exact le_of_lt n.2

-- `⌘`

/- **§ Some exercises** -/

example : 1 ∉ EvenNaturals := by
  intro h
  replace h := h.out
  omega

example : -1 ∉ PositiveIntegers := by
  intro h
  replace h := h.out
  omega

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set Nat := fun d ↦ (0 = d % 2) ∧ 0 < d

example : 1 ∉ EvenPositiveNaturals := by
  intro h
  replace h := h.out
  omega

def EvenPositiveNaturals2 : Set PositiveNaturals := fun d ↦ (0 = d.1 % 2)

-- example : ⟨1, Nat.one_pos⟩  ∉ EvenPositiveNaturals2 := by sorry

-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := fun d ↦ ¬ (EvenNaturals d)

example : 3 ∈ OddNaturals := by
  intro h
  replace h : 0 = 3 % 2 := h
  omega

example (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  rfl

lemma odd_n_eq_even_n_add_one (n : Nat) : n ∈ EvenNaturals ↔ (n + 1) ∈ OddNaturals := by
  constructor
  · intro h 
    replace h := h.out 
    have h1 : 1 = (n+1) % 2 := by omega
    have h2 : 0 ≠ 1 := by omega
    rw [h1] at h2
    exact h2 
  · intro h 
    change 0 ≠ (n+1) % 2 at h
    use Nat.succ_mod_two_eq_zero_iff -- 
    sorry

-- Why does this *fail*?
--example (α : Type) (S : Set α) : subsub = subsub' := sorry


end Definitions

-- # §2. Operations

section Operations

-- **Self-intersection is the identity, proven with extensionality**

example (α : Type) (S : Set α) : S ∩ S = S := by
  ext s
  constructor
  · intro h
    exact h.left -- `exact h.right` works too
  · intro h
    constructor
    · exact h
    · exact h

-- `⌘`


-- **The union**

example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  ext s
  constructor
  · intro h
    cases h with
    | inl h => exact H h
    | inr h => exact h
  · intro h 
    right
    exact h


-- **An _unfixable_ problem**

--example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry

-- `⌘`


-- **Empty set**

example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  ext n
  constructor
  · rintro ⟨hn_pos, hn_neg⟩
    rw [mem_setOf_eq, lt_iff_not_le] at hn_neg
    rw [mem_setOf_eq] at hn_pos
    apply hn_neg
    apply le_of_lt
    exact hn_pos
  · intro h
    exfalso
    exact h

-- `⌘`


-- **Complement and difference**

example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    by_cases hS : x ∈ S
    · right
      exact hS
    · left
      exact hS

-- `⌘`

-- **§ Indexed unions**

example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  constructor
  · intro h
    simp at h 
    exact h
  · intro h
    simp 
    exact h



example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  ext a 
  constructor
  · intro h
    simp; simp at h 
    constructor
    · exact h.right
    · exact h.left
  · intro h 
    simp; simp at h 
    constructor
    · exact h.right
    · exact h.left

def class_valabs_nat : ℕ → Set ℤ := fun n ↦ {(n : Int), (-n : Int)}

#check class_valabs_nat 3

/- **§ Some exercises** -/

-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  ext x
  constructor
  · intro hT
    right
    exact hT
  · rintro hST
    cases hST with
    | inl h => 
      exact H h
    | inr h => 
      exact h

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  ext x 
  constructor
  · intro h 
    have ⟨hS, hTR⟩ := h
    cases hTR with
    | inl hT => 
      left
      constructor
      · exact hS 
      · exact hT 
    | inr hR => 
      right 
      constructor
      · exact hS
      · exact hR
  · intro h 
    constructor 
    · cases h with
      | inl h => exact h.left
      | inr h => exact h.left
    · cases h with
      | inl h =>
        left
        exact h.right
      | inr h =>
        right 
        exact h.right


-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  ext n 
  constructor
  · intro h 
    have ⟨hl, hr⟩ := h
    rw [mem_setOf] at hl
    rw [mem_setOf] at hr
    simp
    omega
  · intro h 
    simp at h
    simp
    omega

-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := by
  ext n
  constructor
  · intro _ 
    trivial
  · intro _ 
    by_cases hpn : EvenNaturals n
    · left 
      exact hpn
    · right 
      exact hpn

-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  ext x 
  constructor
  · intro h2 
    simp at h2 
    have ⟨h2l, h2r⟩ := h2
    have h3 := h h2l
    trivial
  · intro hf 
    exfalso 
    exact hf

example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  intro a h 
  simp; simp at h
  rw [and_assoc]
  exact h


-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x 
  constructor
  · intro h 
    constructor
    · simp; simp at h
      intro i 
      exact (h i).left
    · simp; simp at h
      intro i 
      exact (h i).right
  · intro h 
    simp; simp at h
    intro i 
    exact ⟨h.left i, h.right i⟩

end Operations
