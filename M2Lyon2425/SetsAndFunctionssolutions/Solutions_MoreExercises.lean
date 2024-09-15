import Mathlib

open Set Function Classical

set_option autoImplicit false


/- # Exercises in the tutorial -/

/- ## Sets-/

-- A double inclusion
example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  intro x hx
  apply hTW
  apply hST
  exact hx

-- Self-intersection is the identity, proven with **extensionality**
example (α : Type) (S : Set α) : S ∩ S = S := by
  ext x
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, h⟩

-- Self-intersection is the identity, proven with **extensionality** in a more concise way
example (α : Type) (S : Set α) : S ∩ S = S := by
  ext x
  exact ⟨(·.1), fun h => ⟨h, h⟩⟩ -- the first `(·.1)` is a short way of writing `fun h => h.1`, so
  -- exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩



-- The difference
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  ext x
  constructor
  · intro ⟨hxS, hxnT⟩
    exact hxnT (h hxS)
  · intro H
    tauto

/- ## Functions-/

-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (T : Set β) (f g : S → T) :
  f = g ↔ ∀ a : α, a ∈ S → f a  = g a := by sorry
  -- f = g ↔ ∀ a : α, (ha : a ∈ S) → f ⟨a, ha⟩ = g ⟨a, ha⟩ := by
  -- constructor
  -- · intro H a ha
  --   rw [H]
  -- · intro H
  --   ext ⟨a, ha⟩
  --   rw [H]


variable (α β : Type) (f : α → β)
-- We can upgrade a function `f` to a function between sets, using the image:
example : Set α → Set β := by
  intro S
  use f '' S

-- The range is not *definitionally equal** to the image of the universal set: use extensionality!
example : range f = f '' univ := by
  -- rfl
  ext b
  constructor
  · intro ⟨a, hab⟩
    exact ⟨a, by triv, hab⟩
  · intro ⟨a, _, hab⟩
    exact ⟨a, hab⟩

-- Why is the following a *statement* and not merely the *definition* of being injective?
example : Injective f ↔ InjOn f univ := by
  constructor
  · exact fun hf x _ y _ H => hf H
  · intro hf x y H
    apply hf
    triv
    triv
    exact H
-- or simply := ⟨fun hf _ _ _ _ H=> hf H, fun hf _ _ => hf (by triv) (by triv)⟩

-- # More exercises

example (x : ℕ) : x ∈ ({1, 2, 3, 4} : Set ℕ) ∩ {1, 3} ↔ x = 1 ∨ x = 3 := by
  constructor
  · exact fun ⟨_, _⟩ => by assumption
  · rintro (h1 | h2)
    · exact ⟨Or.intro_left _ h1, Or.intro_left _ h1⟩
    · constructor
      · right; right; left; exact h2
      · right; exact h2

example : ({a | a ≤ 0} : Set ℤ) ∪ {a | a ≥ 0} = univ := by
  ext x
  constructor
  · intro
    trivial
  · intro H
    rcases x with (hpos | hneg)
    · right
      apply Int.ofNat_nonneg
    · left
      apply le_of_lt (Int.negSucc_lt_zero hneg)

example (α β : Type) (f : α → β) : f '' ∅ = ∅ := by
  ext
  exact ⟨fun ⟨y, h⟩ => h.1, fun h => by trivial⟩
