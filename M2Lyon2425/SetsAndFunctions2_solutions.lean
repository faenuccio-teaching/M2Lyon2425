import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common
import Mathlib.Order.Basic
import Mathlib.Logic.Function.Defs
import «M2Lyon2425».«SetsAndFunctions1_solutions»

set_option linter.unusedVariables false


open Set Classical Function
section FirstTrap

-- # §1: A first trap


-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (T : Set β) (f g : S → β) :
  -- f = g ↔ ∀ a : α, a ∈ S → f a  = g a := by sorry
  f = g ↔ ∀ a : α, (ha : a ∈ S) → f ⟨a, ha⟩  = g ⟨a, ha⟩ := by
  constructor
  · intro h
    rw [h]
    -- rfl -- *fails*!
    exact fun _ _ ↦ rfl -- why? Because the whole type is not an equality type.
  · intro h
    funext x
    -- exact h --why?
    apply h -- or exact h _ _

-- **⌘**

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- We can upgrade a function `f` to a function between sets, using the image:
example : Set α → Set β := by
  intro S
  exact f '' S

example : 1 ∈ Nat.succ '' univ := by
  use 0
  constructor
  · trivial
  · rfl
-- *An alternative proof*

-- `⌘`

-- The **image**

example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  intro hS hfS
  apply hS
  rw [eq_empty_iff_forall_not_mem] at hfS ⊢
  intro x hx
  replace hfS := hfS (f x)
  apply hfS
  use x

-- `⌘`

-- The **preimage**

example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by
  constructor
  · rw [mem_preimage]
    trivial
  · intro h
    rw [mem_preimage] at h
    trivial

-- `⌘`

example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  intro m hm n hn
  simp only
  intro H
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one] at H
  by_cases h_mlt : m < n
  · exfalso
    have := Int.mul_lt_mul h_mlt (le_of_lt h_mlt) hm.out (le_of_lt hn.out)
    replace this := ne_of_lt this
    exact this H
  by_cases h_nlt : n < m
  · exfalso
    exact ((ne_of_lt <| Int.mul_lt_mul h_nlt (le_of_lt h_nlt) hn.out (le_of_lt hm.out))) H.symm
  exact eq_of_le_of_not_lt (le_of_not_lt h_nlt) h_mlt








/- **§ Some exercises** -/



-- The range is not *definitionally equal* to the image of the universal set: use extensionality!
example : range f = f '' univ := by
  ext x
  refine ⟨fun h ↦ ?_ , fun h ↦ ?_⟩
  · rw [mem_range] at h
    let y := Exists.choose h
    use y
    constructor
    · trivial
    · exact Exists.choose_spec h
  · rw [mem_range]
    use Exists.choose h
    exact (Exists.choose_spec h).2


-- Why does this code *fail*? Fix it, and then prove the statement
-- example (N : OddNaturals) : N ∈ Nat.succ '' (EvenNaturals) ∧ N ∈ Nat.succ ⁻¹' (EvenNaturals):=
example (N : OddNaturals) : N.1 ∈ Nat.succ '' (EvenNaturals) := by
  rcases N with ⟨n, hn⟩
  have hn' := hn.out
  rw [mem_image]
  match n with
  | 0 => trivial
  | m+1 =>
    rw [Nat.succ_mod_two_eq_one_iff] at hn'
    use m
    constructor
    · exact hn'
    · exact Nat.succ_eq_add_one _

-- Why does this code *fail*? Fix it, and then prove the statement
-- example (N : OddNaturals) :  N ∈ Nat.succ ⁻¹' (EvenNaturals) := by
example (N : OddNaturals) :  N.1 ∈ Nat.succ ⁻¹' (EvenNaturals) := by
  rcases N with ⟨n, hn⟩
  rw [mem_preimage]
  have hn' := hn.out
  by_cases hnz : n = 0
  · rw [hnz] at hn'
    trivial
  · replace hnz := Nat.exists_eq_succ_of_ne_zero hnz
    obtain ⟨m, hm⟩ := hnz -- `obtain` combines the `Exists.choose` and `Exists.choose_spec`
    rw [hm] at hn'
    rw [Nat.succ_mod_two_eq_one_iff] at hn'
    show n.succ % 2 = 0 --`show` changes the goal to something definitionally equivalent
    omega
    -- rw [hm]
    -- simp only [Nat.succ_eq_add_one]
    -- rwa [add_assoc, Nat.add_mod_right]



example : range Nat.succ ≠ univ := by
  intro h
  rw [Set.eq_univ_iff_forall] at h
  replace h := h 0
  have := Nat.succ_ne_zero (Exists.choose h)
  exact this (Exists.choose_spec h)



-- The following is a *statement* and not merely the *definition* of being injective; prove it.
example : Injective f ↔ InjOn f univ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro a ha b hb H
    apply h H
  · intro a b H
    exact h (trivial) (trivial) H



/- With the obvious definition of surjective, prove the following result: the complement is
  abreviated `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by
  refine ⟨fun h ↦ ?_ , fun h ↦ ?_⟩
  · rw [Set.compl_empty_iff]
    ext x
    constructor
    · intro H
      trivial
    · intro H
      obtain ⟨y, hy⟩ := h x
      use y
  · intro x
    rw [Set.compl_empty_iff] at h
    rw [eq_univ_iff_forall] at h
    replace h := h x
    exact h


end Operations

section InductiveTypes

-- # §3 : Inductive types and inductive predicates

-- def EvenNaturals' : Set ℕ
--   | 0 => True
--   | Nat.succ m => ¬ EvenNaturals' m

-- lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ EvenNaturals' := by
--   induction' n with m h_ind
--   · constructor
--     · intro _
--       trivial
--     · intro _
--       trivial
--   · constructor
--     · intro hm
--       replace hm : (m + 1) % 2 = 0 := hm --try to comment it out
--       replace hm : m % 2 = 1 :=by
--         rwa [Nat.succ_mod_two_eq_zero_iff] at hm
--       replace hm : ¬ EvenNaturals m := by
--         rw [EvenNaturals]
--         rw [hm]
--         exact Nat.one_ne_zero
--       replace h_ind := (h_ind.mpr).mt hm
--       exact h_ind
--     · intro hm
--       replace hm : ¬ EvenNaturals' m := by
--         trivial
--       replace h_ind := (h_ind.mp).mt hm
--       replace h_ind : ¬ (m % 2) = 0 := h_ind
--       rwa [Nat.mod_two_ne_zero, ← Nat.succ_mod_two_eq_zero_iff] at h_ind

end InductiveTypes
