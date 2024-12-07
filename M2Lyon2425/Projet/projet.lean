import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Data.Nat.Prime.Defs
#print IsPGroup
#print Sylow
#check MulAction
#print Subgroup.subgroupOf
variable (p:ℕ ) ( hp : Nat.Prime p)

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
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
structure IsSylow  (G : Type*)  [Group G] (H : Subgroup G): Prop where
  isPgroup : ∃ k : ℕ , Nat.card H = p^k
  isMaximal : ¬ (p ∣  H.index )


#print IsSylow



-- MulAction.mulLeftCosetsCompSubtypeVal (Sylow.toSubgroup S) H
#check  MulAction.mulLeftCosetsCompSubtypeVal
theorem stab {G : Type*} [Group G] (H : Subgroup G) (S : Sylow  p G)  (h : H) [MulAction H (G⧸(Sylow.toSubgroup S))]:
    MulAction.stabilizer H  h  =  Subgroup.subgroupOf (conjugate  (h : G) (Sylow.toSubgroup S)) H := by
  ext x
  simp


#check Nonempty
theorem sylow_of_subgroup {G : Type*} [Group G]  (H : Subgroup G) (S : Sylow  p G) :
  ∃ g : G , IsSylow p H ( Subgroup.subgroupOf  (conjugate g (Sylow.toSubgroup S)) H)  := by sorry




theorem exist_sylow_of_subgroup {G : Type*} [Group G] (H : Subgroup G) ( S : Sylow p G)  : Nonempty (Sylow p H) := by
  obtain ⟨ w , hw ⟩ := sylow_of_subgroup  ( p : ℕ ) (H : Subgroup G) (S : Sylow  p G)
  use Subgroup.subgroupOf  (conjugate w (Sylow.toSubgroup S)) H
  · rw[IsPGroup]
    intro g
    cases hw with
    | mk isPgroup isMaximal =>
      obtain ⟨ y ,hy ⟩ := isPgroup
      use y
      rw[← hy]
      exact pow_card_eq_one'
  · intro Q hQ h
    cases hw with
    | mk isPgroup isMaximal =>sorry
     -- have :∃ n, Subgroup.index H = p ^ n :=  IsPGroup.index hQ ((conjugate w ↑S).subgroupOf H : Subgroup Q)

#check Equiv.Perm.subgroupOfMulAction
#check Nat.Prime
 --theorem imbedd_to_gln {G : Type*} [Group G]
