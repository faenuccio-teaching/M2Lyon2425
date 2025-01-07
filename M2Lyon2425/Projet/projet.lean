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

variable (p:ℕ ) ( hp : Nat.Prime p)
/- j'ai repris des définitions données dans les cours sur les groupes-/
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
def Subgroup.Setoid {G : Type*} [Group G](B : Subgroup G) : Setoid G  where
  r := fun x y ↦ x*y⁻¹ ∈ B
  iseqv := {
    refl := by
      intro x
      rw[mul_inv_cancel]
      exact B.one_mem
    symm := by
      intro x y h1
      apply B.inv_mem at h1
      rw[mul_inv_rev x y⁻¹,inv_inv] at h1
      exact h1
    trans := by
      intro x y z h1 h2
      have h3 := B.mul_mem h1 h2
      rw[mul_assoc,← mul_assoc y⁻¹ y z⁻¹,inv_mul_cancel,one_mul] at h3
      exact h3


  }
/--une définition des sylow sous forme d'une prop-/
structure IsSylow  (G : Type*)  [Group G] (H : Subgroup G): Prop where
  isPgroup : ∃ k : ℕ , Nat.card H = p^k
  isMaximal : ¬ (p ∣  H.index )
noncomputable
instance {G : Type*} [Group G] (H : Subgroup G)(S : Sylow  p G) : MulAction H (Quotient (Sylow.toSubgroup S).Setoid ) where
  smul := fun x y => Quotient.mk (Sylow.toSubgroup S).Setoid (x * (Quot.out y))
  one_smul := by
    intro b
    dsimp [HSMul.hSMul]
    simp
    exact Quot.out_eq b
  mul_smul := by
    intro x y b
    dsimp [HSMul.hSMul]
    simp


    dsimp [HasEquiv.Equiv]
    sorry



/-- dans la prop 2.2 , le fait que le stabilisateurs des point de X sous l'action de H sont de la forme H ∩ gSg⁻¹-/
theorem stab {G : Type*} [Group G] (H : Subgroup G) (S : Sylow  p G)  (h : H) :
    MulAction.stabilizer H  (Quotient.mk   (Subgroup.Setoid (Sylow.toSubgroup S)) h)   =  Subgroup.subgroupOf (conjugate  (h : G) (Sylow.toSubgroup S)) H := by
    ext x
    simp
    constructor
    · intro h1
      sorry
    · intro h2
      sorry


/-- prop 2.2-/
theorem sylow_of_subgroup {G : Type*} [Group G]  (H : Subgroup G) (S : Sylow  p G) :
  ∃ g : G , IsSylow p H ( Subgroup.subgroupOf  (conjugate g (Sylow.toSubgroup S)) H)  := by sorry



/-- tout sous groupe d'un groupe admettant un p-sylow admet lui aussi un p-sylow (corollaire 2.3)-/
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
    | mk isPgroup isMaximal =>
     sorry
