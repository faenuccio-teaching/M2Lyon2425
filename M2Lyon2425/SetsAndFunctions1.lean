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

def PositiveIntegers : Set ℤ := λ k => 0 < k

-- `⌘`

lemma one_pos : 1 ∈ PositiveIntegers := Int.one_pos

def PositiveNaturals : Set ℕ := λ n => 0 < n

example : 1 ∈ PositiveNaturals := Nat.one_pos

example : (-1) ∉ PositiveIntegers := by
  intro contra
  replace contra := contra.out
  exact (Int.negSucc_not_nonneg (0 + 0).succ).mp (by exact contra)

-- **The even naturals**

def EvenNaturals : Set ℕ := (· % 2 = 0)

example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  intro h; change (n % 2 = 0) at h; change ((n + 2) % 2 = 0); omega

-- **An abstract set**
def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α := by exact P

-- The same, but it is a general principle that the second version is better
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := by
  rfl

-- `⌘`

-- **Subsets as implication**
example {α : Type} (S T : Set α) (s : α) (hST : S ⊆ T) (hs : s ∈ S) : s ∈ T := by
  apply hST; assumption

-- `⌘`

-- **A double inclusion**

example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  intros s hS; exact (hTW (hST hS))

-- **Another take on subsets and sets as types**

def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := P

def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := λ x => P x.1

-- Are they *equal*? This is an exercise below.

-- Why does this *fail*? How to fix it?
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (_ : x ∈ subsub P) : x.1 ∈ S := x.2

-- **What is really this "injection"  `Set α ↪ Type`?**

-- Why does this *fail*? How to fix it?
example : ∀ n : PositiveIntegers, 0 ≤ n.1 := by 
  intro n; apply Int.le_of_lt; exact n.2

-- `⌘`

/- **§ Some exercises** -/

example : 1 ∉ EvenNaturals := by
  change (1 % 2 ≠ 0); omega

example : -1 ∉ PositiveIntegers := by
  intro contra; replace contra := contra.out; omega

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := by
  intro n
  exact (∃ k, n.1 = 2 * k)

-- Why does this *fail*? How to fix it?
example : ∀ x, x ∈ EvenPositiveNaturals → 1 ≠ x.1 := by
  intros x h e; cases h with
  | intro k h => omega
  
-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := (· % 2 = 1)

example : 3 ∈ OddNaturals := by
  rfl

lemma odd_even_complement (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  constructor
  · intros h h'; replace h := h.out; replace h' := h'.out; rw [h] at h'; trivial
  · intros h; change (n % 2 ≠ 0) at h; change (n % 2 = 1); omega

-- Why does this *fail*?
-- example (α : Type) (S : Set α) : subsub = subsub' := sorry
-- It doesn't have the same type

end Definitions

-- # §2. Operations

section Operations

-- **Self-intersection is the identity, proven with extensionality**

example (α : Type) (S : Set α) : S ∩ S = S := by
  ext x; constructor <;> intro h
  · exact h.left
  · constructor <;> trivial

-- `⌘`

-- **The union**

example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  ext x; constructor <;> intro h
  · cases h with
    | inl h => apply H; assumption
    | inr h => assumption
  · right; assumption

-- **An _unfixable_ problem**

-- example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry

-- `⌘`

-- **Empty set**

example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  ext x; constructor
  · rintro ⟨h0x, hx0⟩; replace h0x := h0x.out; replace hx0 := hx0.out
    rw [lt_iff_not_le] at h0x; apply le_of_lt at hx0; exact (h0x hx0)
  · intro h; exfalso; trivial

-- `⌘`

-- **Complement and difference**

lemma set_union_complement (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  ext x; constructor <;> intro _
  · trivial
  · by_cases h': x ∈ S
    · right; trivial
    · left; trivial

-- `⌘`

-- **§ Indexed unions**

lemma set_union_iff {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  constructor <;> intro h
  · cases h with
    | intro Ai h => 
      cases h with
      | intro h hin => 
        cases h with
        | intro i h => use i; simp at h; rw [h]; assumption
  · cases h with
    | intro i h => use (A i); constructor
                   · use i
                   · assumption

example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  ext x; constructor
  · rintro ⟨ hS, hAi ⟩
    cases hAi with
    | intro Ai h =>
      cases h with
      | intro h hin =>
        cases h with
        | intro i h => use (Ai ∩ S); constructor
                       · use i; simp; simp at h; rw [h]
                       · constructor <;> trivial
  · rintro ⟨ Ai, h ⟩
    cases h with
    | intro h hin => 
      cases h with
      | intro i h => 
        simp at h; rw [←h] at hin; constructor
        · exact hin.right
        · use (A i); constructor
          · use i
          · exact hin.left

/- **§ Some exercises** -/

-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  ext x; constructor
  · intro h; right; trivial
  · intro h; cases h with
    | inl hS => apply H; trivial
    | inr hR => assumption

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  ext x; constructor
  · rintro ⟨ hS, hTR ⟩; cases hTR with
    | inl hT => left; constructor <;> trivial
    | inr hR => right; constructor <;> trivial
  · intro h; cases h with
    | inl h => constructor
               · exact h.left
               · left; exact h.right
    | inr h => constructor
               · exact h.left
               · right; exact h.right

-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  ext x; constructor <;> simp
  · intros h0x hx0; apply le_antisymm <;> trivial
  · intro e; rw [e]; constructor <;> trivial

-- Using your definition of `OddNaturals` prove the following:
lemma odd_complement_even : OddNaturalsᶜ = EvenNaturals := by
  ext x; constructor <;> intro h
  · by_contra contra; rw [←odd_even_complement] at contra; trivial
  · by_contra contra; simp at contra; rw [odd_even_complement] at contra; trivial

example : EvenNaturals ∪ OddNaturals = univ := by
  rw [←odd_complement_even]; apply set_union_complement

-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  ext x; constructor
  · rintro ⟨ hT, hnS ⟩; apply h at hT; exact (hnS hT)
  · intro; exfalso; trivial

example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  intro x; rintro ⟨ hS, hnTU ⟩; constructor
  · constructor
    · trivial
    · intro hT; have hTR : x ∈ T ∪ R := by left; trivial
      exact (hnTU hTR)
  · intro hR; have hTR : x ∈ T ∪ R := by right; trivial
    exact (hnTU hTR)

-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x; constructor <;> intro h
  · constructor
    · intros S hr; cases hr with
      | intro i h' => 
        simp at h'; rw [←h']; specialize h (A i ∩ B i)
        have hi : (A i ∩ B i ∈ range fun i ↦ A i ∩ B i) := by use i
        have hAB : x ∈ A i ∩ B i := by exact (h hi)
        exact hAB.left
    · intros S hr; cases hr with
      | intro i h' =>
        simp at h'; rw [←h']; specialize h (A i ∩ B i)
        have hi : (A i ∩ B i ∈ range fun i ↦ A i ∩ B i) := by use i
        have hAB : x ∈ A i ∩ B i := by exact (h hi)
        exact hAB.right
  · intros S hr; cases hr with
    | intro i e => 
      simp at e; rw [←e]; cases h with
      | intro hA hB => constructor
                       · apply hA; use i
                       · apply hB; use i

end Operations
