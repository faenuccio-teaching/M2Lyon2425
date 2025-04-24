import Mathlib

/- Suite de Fibonacci -/

-- Définir la suite d'éléments de `ℕ` de fibonacci : `u 0 = 0`, `u 1 = 1`, `u (n + 2) = u (n + 1) + u (n)`
def u : ℕ → ℕ := sorry

-- Montrer la propriété de récurrence
lemma u_rec (n : ℕ) :
    u (n + 2) = u (n + 1) + u n := sorry

-- Montrer que la suite `u` est croissante
#check monotone_nat_of_le_succ

example : Monotone u := by
  sorry

-- Montrer par récurrence  `∑ i in range n, u (2 * i + 1) = u (2 * n)`
#check Finset.range_succ
#check Finset.sum_insert

example (n : ℕ) : ∑ i in Finset.range n, u (2 * i + 1) = u (2 * n) := by
  sorry

/- Filtres -/

example : Filter ℤ where
  sets := {A | ∃ n, Set.Iic n ⊆ A}
  univ_sets := by
    sorry
  sets_of_superset := by
    intro s t hs h
    sorry
  inter_sets := by
    intro s t hs ht
    sorry

#check Nat.exists_infinite_primes
open Filter in
example : ∃ᶠ n in atTop, Nat.Prime n := by
  sorry

/- Groupes -/

variable {G H K : Type*} [Group G] [Group H] [Group K]

open Subgroup

-- Définir le conjugué d'un sous-groupe comme l'ensemble des éléments de la forme `xhx⁻¹` pour `h ∈ H`
def conjugate (x : G) (H : Subgroup G) : Subgroup G where
  carrier := sorry
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

lemma mem_conjugate_iff {x y : G} {H : Subgroup G} :
    y ∈ conjugate x H ↔ ∃ h ∈ H, y = x * h * x⁻¹ := sorry

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := sorry

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := sorry
