import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common

open Set Classical
section Definitions

-- # §1: Definitions

/- **§ Basics** -/

-- **A tautology**
example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  rfl


-- **The positive integers**
def PositiveIntegers : Set ℤ := by
  -- *1* intro d
  -- *2* use if 0 < d then True else False
  -- *3* exact (0 < ·) d
  -- *4* exact @LT.lt ℤ _ 0
  -- *5* exact (fun d ↦ 0 < d)
  exact (0 < ·) -- keep this

example : 1 ∈ PositiveIntegers := by
  have := Nat.zero_lt_of_ne_zero (Nat.one_ne_zero)
  -- exact this -- *why does it fail?*
  rw [← Int.ofNat_lt] at this
  exact this --*Or also* rwa

-- **The even naturals**
def EvenNaturals : Set ℕ := by
  -- -- *1*
  -- intro d
  -- exact if d % 2 = 0 then True else False
  exact (· % 2 = 0) -- keep this

def EvenNaturals' : Set ℕ
  | 0 => True
  | Nat.succ m => ¬ EvenNaturals' m

example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  intro h
  replace h := h.out --not needed, but sometimes useful
  -- rw [Nat.add_mod_right]-- a pity it does not work...
  rw [mem_def]
  rw [← Nat.add_mod_right] at h -- try to comment the replace here
  exact h

lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ EvenNaturals' := by
  induction' n with m h_ind
  · constructor
    · intro _
      trivial
    · intro _
      trivial
  · constructor
    · intro hm
      replace hm : (m + 1) % 2 = 0 := hm --try to comment it out
      replace hm : m % 2 = 1 :=by
        rwa [Nat.succ_mod_two_eq_zero_iff] at hm
      replace hm : ¬ EvenNaturals m := by
        rw [EvenNaturals]
        rw [hm]
        exact Nat.one_ne_zero
      replace h_ind := (h_ind.mpr).mt hm
      exact h_ind
    · intro hm
      replace hm : ¬ EvenNaturals' m := by
        trivial
      replace h_ind := (h_ind.mp).mt hm
      replace h_ind : ¬ (m % 2) = 0 := h_ind
      rwa [Nat.mod_two_ne_zero, ← Nat.succ_mod_two_eq_zero_iff] at h_ind



-- **An abstract set**
def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α := setOf P

-- The same, but it is a general principle that the second version is better
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := by
  rfl



/- **§ Subsets** -/

-- **A double inclusion**

example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  intro s hs
  apply hTW
  apply hST
  exact hs
  -- *An alternative proof*
  -- intro s hs
  -- exact hTW <| hST hs
  -- *Another one*
  -- exact hTW (hST hs)

-- **Another take on subsets and sets as types**
def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := P

def subsub' (α : Type) (S : Set α) (P : α → Prop) : Set (S : Type) := by
  intro a
  exact P a

-- Are they *equal*? This is an exercise below.

-- Why does this *fail*? How to fix it?
-- example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : x ∈ S := sorry
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : {s : S // P s} := by
  use x
  exact hx


-- **What is really this "injection"  `Set α ↪ Type*`?**

-- Why does this *fail*? How to fix it?
-- example : ∀ n : PositiveIntegers, 0 ≤ n := by
example : ∀ n : PositiveIntegers, 0 < n.1 := by
  rintro ⟨n, hn⟩
  exact hn


/- **§ Some exercises** -/

example : 1 ∉ EvenNaturals := by
  intro h
  trivial
  -- tauto

example : -1 ∉ PositiveIntegers := by
  intro h
  trivial
  -- tauto

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := by
  rintro ⟨d, _⟩
  exact d % 2 = 0

-- Why does this *fail*? How to fix it?
example : 1 ∉ EvenPositiveNaturals := sorry
/- Lean complains because `3` is not a term of `EvenNaturals`, so it does not make sense
to check whether it satisifies a property defined on them. It can be made to work by writing -/
-- example : ⟨1, Int.zero_lt_one⟩ ∉ EvenPositiveNaturals := sorry


-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := (· % 2 = 1)

example : 3 ∈ OddNaturals := by
  rfl


example (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  constructor
  · intro h h_abs
    replace h : n % 2 = 1 := h
    replace h_abs : n % 2 = 0 := h_abs
    rw [h] at h_abs
    apply Nat.one_ne_zero
    exact h_abs
  · intro h
    replace h : ¬ n % 2 = 0 := h
    rwa [Nat.mod_two_ne_zero] at h


-- Why does this *fail*? How to fix it?
example : subsub = subsub' := sorry

end Definitions

-- # §2. Operations
section Operations

-- **Self-intersection is the identity, proven with extensionality**
example (α : Type) (S : Set α) : S ∩ S = S := by
  ext
  constructor
  · intro h --rintro ⟨h, h⟩
    exact h.1 -- exact h
  · intro h
    exact ⟨h, h⟩
-- *Alternative proof*
  -- ext
  -- rw [← eq_iff_iff]
  -- exact and_self _

-- **The union**
example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  ext x
  rw [Set.subset_def] at H
  exact or_iff_right_of_imp (H x)


-- **An _unfixable_ problem**
example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry


-- **Empty set**
example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  ext d
  constructor
  · rintro ⟨h_pos, h_neg⟩
    rw [mem_setOf_eq] at h_neg h_pos
    rw [lt_iff_not_le] at h_neg
    apply h_neg
    apply le_of_lt
    exact h_pos
  · intro h
    exfalso
    exact h


-- **Complement and difference**
example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  ext x
  constructor
  · intro
    trivial
  · intro
    by_cases hx : x ∈ S
    · apply Or.intro_right
      exact hx
    · exact Or.intro_left _ hx







/- **§ Some exercises** -/

-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := sorry
  -- ext
  -- constructor
  -- · intro h
  --   cases h
  --   · apply H
  --     assumption
  --   · assumption
  -- · intro h
  --   apply Or.intro_right
  --   exact h

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := sorry

-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  ext
  simp only [mem_inter_iff, mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro h
    exact (le_antisymm h.1 h.2).symm
  · intro h
    rw [h]
    exact ⟨le_refl _, le_refl _⟩


-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by sorry

example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := sorry


end Operations
