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

lemma dist_F1_F2_less_zero : distance F1 F2 ≤ 0 := by
  rw [distance, Real.sInf_le_iff]
  · intros ε hε
    use dist (2 / ε, ε / 2) (2 / ε, 0)
    refine ⟨?_, ?_⟩
    · use (2 / ε, ε / 2)
      refine ⟨?_, ?_⟩
      change (2/ε) * (ε/2) = 1
      norm_num
      exact div_self (ne_of_gt hε)
      use (2 / ε, 0)
      refine ⟨?_, rfl⟩
      change 0 = 0
      rfl
    · rw [zero_add]
      change ((2/ε - 2/ε)^2 + (0 - ε/2)^2)^(1/2) < ε
      rw [sub_self, zero_sub, Real.zero_rpow two_ne_zero, zero_add]
      simp only [Real.rpow_two, even_two, Even.neg_pow]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq]
      simp only [half_lt_self_iff]
      exact hε
      linarith
  · rw [BddBelow, lowerBounds, Set.Nonempty]
    use 0
    dsimp
    intros a ha
    obtain ⟨p, ⟨_, ⟨q, ⟨_, hdist⟩⟩⟩⟩ := ha
    rw [← hdist]
    change 0 ≤ ((q.1 - p.1)^(2 : ℝ) + (q.2 - p.2)^(2 : ℝ))^(1/(2 : ℝ))
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  · rw [Set.Nonempty]
    use dist ((2 : ℝ), (1 : ℝ) / (2 : ℝ)) ((2 : ℝ), (0 : ℝ))
    use (2, 1 / 2)
    refine ⟨?_, ?_⟩
    change 2 * (1/2) = 1
    norm_num
    use (2,0)
    refine ⟨?_, ?_⟩
    change 0 = 0
    rfl
    rfl

lemma zero_less_dist_F1_F2 : 0 ≤ distance F1 F2 := by
  apply le_csInf
  · rw [Set.Nonempty]
    use dist ((2 : ℝ), (1 : ℝ) / (2 : ℝ)) ((2 : ℝ), (0 : ℝ))
    use (2, 1 / 2)
    refine ⟨?_, ?_⟩
    change 2 * (1/2) = 1
    norm_num
    use (2,0)
    refine ⟨?_, ?_⟩
    change 0 = 0
    rfl
    rfl
  · intros a ha
    obtain ⟨p, ⟨_, ⟨q, ⟨_, hdist⟩⟩⟩⟩ := ha
    rw [← hdist]
    change 0 ≤ ((q.1 - p.1)^(2 : ℝ) + (q.2 - p.2)^(2 : ℝ))^(1/(2 : ℝ))
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _

lemma dist_F1_F2_eq_zero : distance F1 F2 = 0 :=
  ((LE.le.ge_iff_eq zero_less_dist_F1_F2).1 dist_F1_F2_less_zero).symm
