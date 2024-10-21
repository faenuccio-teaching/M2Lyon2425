import Mathlib

def nombre_constructible (a : Complex) :=
  ∃ n : ℕ,
    (1 < n) ∧
    ∃ K : ℕ → Type, ∀ i, i < n → Field (K i) →
      ∃ f : ℕ → ((K i) →+* (K (i + 1))), (i : Fin n) → Function.Injective (f i) ∧
      K ↑0

def est_une_tour
  {n : ℕ}
  (hn : 1 < n)
  {K : ℕ → Type}
  (i : ℕ)
  [Field (K i)] :
  ∃ f : (Field (K i)) →+* (Field (K (i+1))), 1=2 := by
    sorry

#print Field

/-
il existe n tel que n>1 et il existe K : ℕ → Type tel que
K i est un corps et il existe f : ℕ → (K i) →+* K (i+1)
-/
