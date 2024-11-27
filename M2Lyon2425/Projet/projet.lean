import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Matrix
variable {p : ℕ }
variable (G : Type*) [Group G]

#print Sylow
example : GeneralLinearGroup
theorem sylow_of_subgroup (H : Subgroup G) (S : Sylow  p G) :
    ∃ g , (H  ∩ ) ∈  Sylow p H := by sorry
