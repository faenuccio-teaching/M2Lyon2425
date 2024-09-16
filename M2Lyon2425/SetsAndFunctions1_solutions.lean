import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common

open Set Classical
section Examples

/- # A tautology -/
example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  rfl


/- # The positive integers -/
def PositiveIntegers : Set ℤ := by
  -- intro d
  -- use if 0 < d then True else False --bleah!
  -- exact (0 < ·) d -- not bleah
  -- exact @LT.lt ℤ _ 0 -- uff
  -- exact (fun d ↦ 0 < d) -- mah
  exact (0 < ·) -- nicer

example : 1 ∈ PositiveIntegers := by
  have := Nat.zero_lt_of_ne_zero (Nat.one_ne_zero)
  -- exact this -- why?
  rw [← Int.ofNat_lt] at this
  exact this --rwa

/- # The even naturals -/
def EvenNaturals : Set ℕ := by
  -- intro d
  -- exact if d % 2 = 0 then True else False
  exact (· % 2 = 0)

def EvenNaturals' : Set ℕ
  | 0 => True
  | Nat.succ m => ¬ EvenNaturals' m


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




/- # An abstract set -/
def AbstracSet (α : Type) (P : α → Prop) : Set α := P


/- # Some sub-sub sets -/
def subsub (α : Type) (S : Set α) (P : α → Prop) : Set (S : Type) := by
  intro a
  exact P a

def subsub' (α : Type) (S : Set α) (P : S → Prop) : Set (S : Type) := P

example : subsub = subsub' := sorry

/- # A double inclusion -/

example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  intro s hs
  apply hTW
  apply hST
  exact hs
  -- intro s hs
  -- exact hTW <| hST hs -- exact hTW (hST hs)




/- # Some exercises -/

example : 1 ∉ EvenNaturals := by
  intro h
  trivial
  -- tauto

example : -1 ∉ PositiveIntegers := by
  intro h
  trivial

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := by
  have P : ℤ → Prop := (· % 2 = 0)
  rintro ⟨d, _⟩
  exact P d


example : 1 ∉ EvenPositiveNaturals := sorry --can you explain why Lean complains?
/- Lean complains because `3` is not a term of `EvenNaturals`, so it does not make sense
to check whether it satisifies a property defined on them. It can be made to work by writing
`example : ⟨1, Int.zero_lt_one⟩ ∉ EvenPositiveNaturals := sorry` -/


-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := sorry

example : 3 ∈ OddNaturals := sorry

example (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := sorry


end Examples


section Operations

-- Self-intersection is the identity, proven with **extensionality**
example (α : Type) (S : Set α) : S ∩ S = S := by sorry















-- The difference
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by sorry
















/- # Functions-/

-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (T : Set β) (f g : S → T) :
  f = g ↔ ∀ a : α, a ∈ S → f a  = g a := by sorry
















variable (α β : Type) (f : α → β)

-- We can upgrade a function `f` to a function between sets, using the image:
example : Set α → Set β := by sorry















-- The range is not *definitionally equal* to the image of the universal set: use extensionality!
example : range f = f '' univ := by sorry
















-- Why is the following a *statement* and not merely the *definition* of being injective?
example : Injective f ↔ InjOn f univ := by sorry

end Operations
