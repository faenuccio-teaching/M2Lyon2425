import Mathlib.Data.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.EReal
import Mathlib.Topology.Sequences

/-- Goal of the project: formalize the counterexamples of the chapter 10
of the book "Counterexamples in Analysis" by Bernard R. Gelbaum and
John M. H. Olmsted -/

-- Counterexample 1: Two disjoint closed sets that are at
-- a zero distance

def F1 : Set (ℝ × ℝ) := setOf (fun (x,y) ↦ x*y = 1)

def F2 : Set (ℝ × ℝ) := setOf (fun (x,y) ↦ y=0)

lemma F1_disjoint_F2 : F1 ∩ F2 = ∅ := by
  by_contra H
  rw [Set.ext_iff] at H
  push_neg at H
  cases H with
  | intro w h =>
      cases h with
      | inl h =>
          cases' h with h₁ h₂
          cases' h₁ with h h'
          change w.2 = 0 at h'
          change w.1 * w.2 = 1 at h
          rw [h', mul_zero] at h
          exact zero_ne_one h
      | inr h => exact h.2

instance : TopologicalSpace (ℝ × ℝ) := by
  have : TopologicalSpace ℝ := by
    have := EReal.instTopologicalSpace
    exact TopologicalSpace.induced Real.toEReal this
  exact @instTopologicalSpaceProd ℝ ℝ this this
