import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common

namespace ENS

-- # §1 : TripToEns

/-Define a type whose terms represent how one can reach the ENS: one can use a car, a bike, the
metro or any combination of those (with no repetition).-/
inductive TripToENS
  | car : TripToENS
  | bike : TripToENS
  | metro : TripToENS
  | one_change : TripToENS → TripToENS → TripToENS
  | two_changes : TripToENS → TripToENS → TripToENS → TripToENS

-- The following two lines are needed for the file to work: *leave* them as they are, please.
deriving Repr
open TripToENS

/- State that if you're not simply coming by bike nor by car, then either you come by metro or you
need at least one change.-/
example (a : TripToENS) (h1 : a ≠ bike) (h1 : a ≠ car) :
  a = metro
  ∨ (∃ b₁ b₂ , a = one_change b₁ b₂)
  ∨ (∃ c₁ c₂ c₃, a = two_changes c₁ c₂ c₃) := by
  -- cases' a with b1 b2 c1 c2 c3
  rcases a with _ | _ | _ | ⟨b1, b2⟩ | ⟨c1, c2, c3⟩
  · trivial
  · trivial
  · apply Or.inl
    rfl
  · apply Or.inr
    apply Or.inl
    use b1, b2
  · apply Or.inr
    apply Or.inr
    use c1, c2, c3

/- Define a function that expects a trip and outputs the *last* means of transportation -/
def lastTrip (a : TripToENS) : TripToENS :=
match a with
  | one_change b c => c
  | two_changes b c d => d
  | x => x

/-Evaluate your function agains three or four trips and see if it works-/
#eval (lastTrip (one_change car car))
#eval (lastTrip (one_change car bike))
#eval (lastTrip (two_changes bike car bike))
#eval (lastTrip (metro))
#eval (lastTrip (two_changes metro bike metro))


/- Define the set of `TripToENS` that entail no chages:-/
inductive NoChangesTrip' : TripToENS → Prop :=
  | only_car : NoChangesTrip' car
  | only_metro : NoChangesTrip' metro
  | only_bike : NoChangesTrip' bike

open NoChangesTrip'

def NoChangesTrip := setOf NoChangesTrip'

example : car ∈ NoChangesTrip := by
  exact only_car

example : one_change car bike ∉ NoChangesTrip := by
  intro h
  cases h

-- # §2 : Cofinite Topology

open Set


/- The cofinite topology as inductive type -/
inductive CofTop {α : Type} : Set α → Prop
| open_empty : CofTop ∅
| open_cofinite (S : Set α) : Finite ↑(Sᶜ) → CofTop S
open CofTop

variable {α : Type}

lemma interCofTop (S T : Set α) : CofTop S → CofTop T → CofTop (S ∩ T) := by
  intro hs ht
  rcases hs with _ | ⟨_, hs⟩
  · rw [empty_inter]
    exact open_empty
  · rcases ht with _ | ⟨_, ht⟩
    · rw [inter_empty]
      exact open_empty
    · apply open_cofinite
      rw [compl_inter]
      apply Set.Finite.union
      exact hs
      exact ht

lemma cofinite_of_Notempty (S : Set α) (hS : S ≠ ∅) : CofTop S → Finite ↑(Sᶜ) := by
  rintro ⟨h, h2⟩
  · trivial
  assumption

lemma iUnionCofTop (I : Type) (S : I → Set α) (hs : (i : I) → CofTop (S i)) :
  CofTop (⋃ i : I, S i) := by
  classical
  by_cases h : ∃ i, S i ≠ ∅
  · obtain ⟨i, hi⟩ := h
    let T := S i
    have := cofinite_of_Notempty T hi (hs i)
    apply open_cofinite
    rw [compl_iUnion]
    apply Finite.subset this
    refine iInter_subset_of_subset i (by rfl)
  · simp only [not_exists, ne_eq, not_not, ← iUnion_eq_empty] at h
    rw [h]
    exact open_empty

lemma univ_CofTop : CofTop (univ : (Set α)) := by
  apply open_cofinite
  rw [compl_univ]
  exact finite_empty

lemma empty_CofTop : CofTop (∅ : Set α) := open_empty

end ENS
