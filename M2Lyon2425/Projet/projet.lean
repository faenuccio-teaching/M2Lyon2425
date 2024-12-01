import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Sylow
--import Mathlib.LinearAlgebra.Matrix
variable {p : ℕ }
variable (G : Type*)  [Group G]

#print Sylow
#check MulAction.QuotientAction
def conjugate  (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1, H.one_mem
    group
  inv_mem' := by
    dsimp
    intro x hx
    obtain ⟨h, mem, cond⟩ := hx
    use h⁻¹, H.inv_mem mem
    rw [cond]; group
  mul_mem' := by
    dsimp
    intro x y hx hy
    obtain ⟨h₁, mem₁, cond₁⟩ := hx
    obtain ⟨h₂, mem₂, cond₂⟩ := hy
    use h₁ * h₂, H.mul_mem mem₁ mem₂
    rw [cond₁, cond₂]; group

/-instance (H : Subgroup G) (S : Sylow  p G) : Sylow p H where
  carrier := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry
  one_mem' := by sorry
  isPGroup' := by sorry
  is_maximal' := by sorry


theorem sylow_of_subgroup (H : Subgroup G) (S : Sylow  p G) :
    H ∈   (Sylow p G).toSubgroup := by sorry

-/

theorem sylow_of_subgroup (H : Subgroup G) (S : Sylow  p G) :
    ∃ g : G , H ⊓ (conjugate g (Sylow.toSubgroup S)) ∈  (Sylow p H.toGroup) := by
