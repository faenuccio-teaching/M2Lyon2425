import Mathlib.Data.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.EReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- Goal of the project: formalize the counterexamples of the chapter 10
of the book "Counterexamples in Analysis" by Bernard R. Gelbaum and
John M. H. Olmsted -/

-- Counterexample 1: Two disjoint closed sets that are at
-- a zero distance

def F1 : Set (ℝ × ℝ) := setOf fun (x,y) ↦ x*y = 1

def F2 : Set (ℝ × ℝ) := setOf fun (_,y) ↦ y=0

lemma F1_disjoint_F2 : F1 ∩ F2 = ∅ := by
  by_contra H
  rw [Set.ext_iff] at H
  push_neg at H
  cases' H with w h
  cases h with
  | inl h =>
      cases' h with h₁ _
      cases' h₁ with h h'
      change w.2 = 0 at h'
      change w.1 * w.2 = 1 at h
      rw [h', mul_zero] at h
      exact zero_ne_one h
  | inr h => exact h.2

lemma F1_closed : IsClosed F1 :=
  isClosed_eq (Continuous.mul continuous_fst continuous_snd) continuous_one

lemma F2_closed : IsClosed F2 :=
  isClosed_eq continuous_snd continuous_zero

noncomputable instance : Dist (ℝ × ℝ) where
  dist := fun p q ↦ ((q.1 - p.1)^(2 : ℝ) + (q.2 - p.2)^(2 : ℝ))^(1/(2 : ℝ))

def set_dist (A B : Set (ℝ × ℝ)) : Set ℝ := setOf (∃ p ∈ A, ∃ q ∈ B, Dist.dist p q = ·)

noncomputable def distance (A B : Set (ℝ × ℝ)):= InfSet.sInf (set_dist A B)

lemma dist_F1_F2_eq_zero : distance F1 F2 = 0 := by
  have h : ∀ x ∈ set_dist F1 F2, 0 ≤ x := sorry
  have h₂ := Real.sInf_nonneg _ h
  have h₃ : ¬0 < sInf (set_dist F1 F2) := by
    intro h₃
    have h₄ : sInf (set_dist F1 F2) ∈ lowerBounds (set_dist F1 F2) := by
      change ∀ a, a ∈ (set_dist F1 F2) → sInf (set_dist F1 F2) ≤ a
      intro a ha
      sorry
    change ∀ a, a ∈ (set_dist F1 F2) → sInf (set_dist F1 F2) ≤ a at h₄
    let ε := sInf (set_dist F1 F2)
    specialize h₄ (Dist.dist (2/ε, ε/2) (2/ε, 0))
    have h₅ : dist (2 / ε, ε / 2) (2 / ε, 0) ∈ set_dist F1 F2 := sorry
    specialize h₄ h₅
    change ε ≤ ((2/ε - 2/ε)^2 + (0 - ε/2)^2)^(1/2) at h₄
    sorry
  have h₄ := eq_of_le_of_not_lt h₂ h₃
  exact h₄.symm
