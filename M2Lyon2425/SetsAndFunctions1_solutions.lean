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
  rfl


-- **The positive integers**

def PositiveIntegers : Set ℤ := by
  -- *1* intro d
  -- *2* use if 0 < d then True else False
  -- *3* exact (0 < ·) d
  -- *4* exact @LT.lt ℤ _ 0
  -- *5* exact (fun d ↦ 0 < d)
  exact (0 < ·) -- keep this

lemma one_pos : 1 ∈ PositiveIntegers := by
  have := Nat.zero_lt_of_ne_zero (Nat.one_ne_zero)
  -- exact this -- *why does it fail?*
  rw [← Int.ofNat_lt] at this
  exact this --*Or also* rwa

def PositiveNaturals : Set ℕ := by
  exact (0 < ·)

example : 1 ∈ PositiveNaturals := by
  -- apply one_pos -- It *fails*!
  exact Nat.zero_lt_of_ne_zero Nat.one_ne_zero

-- Why does this *fail*? How to fix it?
-- example : (-1) ∉ PositiveNaturals := sorry
/- It fails because Lean cannot be convinced that `-1 : ℕ`. The best we can do is-/
example : (-1) ∉ PositiveIntegers := by
  intro h
  replace h := h.out --not "really" needed, but sometimes useful
  -- omega -- a nice tactic that can prove these "linear (in)equalities"
  exact (Int.negSucc_not_nonneg (0 + 0).succ).mp (by exact h)

-- **The even naturals**

def EvenNaturals : Set ℕ := by
  -- -- *1*
  -- intro d
  -- exact if d % 2 = 0 then True else False
  exact (· % 2 = 0) -- keep this

example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  intro h
  replace h := h.out
  -- rw [Nat.add_mod_right]-- a pity it does not work...
  rw [mem_def]
  rw [← Nat.add_mod_right] at h -- try to comment the `replace` three lines above
  exact h


-- **An abstract set**

def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α := setOf P

-- The same, but it is a general principle that the second version is better
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := by
  rfl



-- `⌘`

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

def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := by
  intro a
  exact P a

-- Are they *equal*? This is an exercise below.

-- Why does this *fail*? How to fix it?
-- example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : x ∈ S := sorry
/- *Sol.:* This fails because `x` is of type `↑S`, but `S` is in `Set α`, so only terms of type `α`
can be tested for membership in `S`. It can be made to work as follows:-/
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : {s : S // P s} := by
  use x
  exact hx


-- **What is really this "injection"  `Set α ↪ Type*`?**

-- Why does this *fail*? How to fix it?
-- example : ∀ n : PositiveIntegers, 0 ≤ n := sorry
/- *Sol.:*  This fails because `0` is a term of `ℕ`, whereas `n` is a term of `PositiveIntegers`.
They cannot be compared directly, because `n` is actually a *pair* of a natural number and a proof
of its positivity. It can be made to work as follows-/
example : ∀ n : PositiveIntegers, 0 < n.1 := by
  rintro ⟨-, hn⟩ --use first `rintro ⟨n, hn⟩` and then `rintro ⟨_, hn⟩`
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
-- example : 1 ∉ EvenPositiveNaturals := sorry
/- *Sol.:* Lean complains because `3` is not a term of `EvenNaturals`, so it does not make sense
to check whether it satisifies a property defined on them. It can be made to work by writing -/
example : ⟨1, Int.zero_lt_one⟩ ∉ EvenPositiveNaturals := sorry


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


-- Why does this *fail*?
-- example (α : Type) (S : Set α) : subsub = subsub' := sorry
/- *Sol.:*  Lean complanins because in `subsub'` `P` is defined on the type `α` whereas in `subsub`
it is defined on the type `↑S`. So this is an equality between functions defined on different types,
that makes no sense. -/


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

-- example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry
/- *Sol.:*  Well, it was unfixable, so there is no solution...-/


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




-- **§ Indexed unions**

example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [mem_iUnion] at h
    exact h
  · rw [mem_iUnion]
    exact h
  -- *Alternative proof*
  -- rw [mem_iUnion]



example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩


/- **§ Some exercises** -/

-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  ext
  constructor
  · intro h
    apply Or.intro_right
    exact h
  · intro h
    cases h
    · apply H
      assumption
    · assumption

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  ext x
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · rcases h2 with hT | hR
    · exact Or.intro_left _ (⟨h1, hT⟩ : And _ _ )
    · exact Or.intro_right _ (⟨h1, hR⟩ : And _ _ )
  · rcases h with ⟨hS, -⟩ | ⟨hS, -⟩ <;> assumption
  · rcases h with ⟨-, hT⟩ | ⟨-, hR⟩
    exact Or.intro_left _ hT
    exact Or.intro_right _ hR



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

-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := by
  ext x
  simp only [mem_union, mem_univ, iff_true] -- to be obtained by tipying `simp?`
  by_cases hx : x % 2 = 0
  · apply Or.inl
    exact hx
  · rw [Nat.mod_two_ne_zero] at hx
    apply Or.inr
    exact hx


-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  ext
  exact ⟨fun ⟨hT, hnS⟩ ↦ hnS <| h hT, fun _ ↦ by trivial⟩

example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  intro x ⟨hxS, hxnTR⟩
  rw [mem_diff]
  rw [mem_union, not_or] at hxnTR
  exact ⟨⟨hxS, fun h ↦ hxnTR.1 h⟩, hxnTR.2⟩
-- *An alternative tactic* replacing this `exact`: longer but easier to read:
  -- constructor
  -- · constructor
  --   · exact hxS
  --   · exact hxnTR.1
  -- exact hxnTR.2


-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i

end Operations
