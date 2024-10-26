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
  cases' H with w H
  cases H with
  | inl h =>
      obtain ⟨⟨h, h'⟩, _⟩ := h
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

def set_dist (A B : Set (ℝ × ℝ)) : Set ℝ := setOf (∃ p ∈ A, ∃ q ∈ B, dist p q = ·)

noncomputable def distance (A B : Set (ℝ × ℝ)) := sInf (set_dist A B)

lemma set_dist_nonempty : (set_dist F1 F2).Nonempty := by
  refine ⟨dist (2, 1/2) ((2 : ℝ), (0 : ℝ)), ⟨(2, 1/2), ⟨?_, ⟨(2,0),
    ⟨(by rw [Set.mem_def]; rfl), rfl⟩⟩⟩⟩⟩
  change 2 * (1/2) = 1
  norm_num

lemma dist_on_prod_pos : ∀ d ∈ set_dist F1 F2, 0 ≤ d := by
  rintro a ⟨p, ⟨_, ⟨q, ⟨_, hdist⟩⟩⟩⟩
  rw [← hdist]
  change 0 ≤ ((q.1 - p.1)^2 + (q.2 - p.2)^2)^(1/2)
  rw [← Real.sqrt_eq_rpow]
  exact Real.sqrt_nonneg _

lemma distance_F1_F2_neg : distance F1 F2 ≤ 0 := by
  rw [distance, Real.sInf_le_iff ⟨0, dist_on_prod_pos⟩ set_dist_nonempty]
  refine fun ε hε ↦ ⟨dist (2 / ε, ε / 2) (2 / ε, 0), ⟨?_, ?_⟩⟩
  · refine ⟨(2 / ε, ε / 2), ⟨?_, ⟨(2 / ε, 0), ⟨(by rw [Set.mem_def]; rfl), rfl⟩⟩⟩⟩
    change (2/ε) * (ε/2) = 1
    norm_num
    exact div_self (ne_of_gt hε)
  · change ((2/ε - 2/ε)^2 + (0 - ε/2)^2)^(1/2) < 0 + ε
    rw [zero_add, sub_self, zero_sub, Real.zero_rpow two_ne_zero, zero_add, Real.rpow_two,
    Even.neg_pow even_two, ← Real.sqrt_eq_rpow, Real.sqrt_sq, half_lt_self_iff]
    exact hε
    linarith

lemma distance_F1_F2_pos : 0 ≤ distance F1 F2 :=
  le_csInf set_dist_nonempty dist_on_prod_pos

lemma distance_F1_F2_eq_zero : distance F1 F2 = 0 :=
  (LE.le.ge_iff_eq distance_F1_F2_neg).1 distance_F1_F2_pos
