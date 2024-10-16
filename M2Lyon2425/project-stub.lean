import Mathlib


/-
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Int
-/

def ARS_zero {α : Type*} : α → α → Prop := fun _ _ ↦ False

def PreKleene_nsmul {α : Type*} (n : ℕ) (f : α → α → Prop) : α → α → Prop := by -- nécessaire
  cases n with
  | zero => exact ARS_zero
  | succ m => exact f

def PreKleene_nsmul_succ_succ {α : Type*} (n : ℕ) (f : α → α → Prop) -- nécessaire
  : PreKleene_nsmul (Nat.succ n) f = f := by
    trivial

def PreKleene_addIdem {α : Type*} (f : α → α → Prop) -- nécessaire
  : (fun x y ↦ (f x y) ∨ (f x y)) = f := by
    ext x y
    constructor
    · intro h
      cases h with
      | inl left => exact left
      | inr right => exact right
    · intro h
      left
      exact h

def PreKleene_nsmul_succ_zero {α : Type*} (f : α → α → Prop) -- nécessaire
  : PreKleene_nsmul 0 f = ARS_zero := by
    trivial


def ARS_mul {α : Type*} (f g : α → α → Prop) : α → α → Prop := by
  exact fun u v ↦ (∃ w, f u w ∧ g w v)

def ARS_one {α : Type*} : α → α → Prop := (fun x y ↦ x = y)


#synth (AddMonoid (ℕ → ℕ → Prop)) -- il n'y a pas de struture de monoïde idempotent sur

instance PreKleene {α : Type} : AddMonoid (α → α → Prop) where
  add f g := fun x y ↦ (f x y ∨ g x y)
  zero := ARS_zero
  add_assoc f g h := by
    ext x y
    change (fun u v ↦ (f u v ∨ g u v) ∨ h u v) x y ↔ (fun u v ↦ f u v ∨ (g u v ∨ h u v)) x y
    simp
    rw [or_assoc]
  zero_add f := by
    ext x y
    change False ∨ f x y ↔ f x y
    simp
  add_zero f := by
    ext x y
    change f x y ∨ False ↔ f x y
    simp
  nsmul := PreKleene_nsmul
  nsmul_zero f := by
    trivial
  nsmul_succ n f := by
    rw [PreKleene_nsmul_succ_succ]
    cases n with
    | zero =>
      rw [PreKleene_nsmul_succ_zero]
      symm
      ext x y
      change (fun u v ↦ (False ∨ f u v)) x y ↔ f x y
      simp
    | succ m =>
      rw [PreKleene_nsmul_succ_succ]
      symm
      exact PreKleene_addIdem f

#synth (AddMonoid (ℕ → ℕ → Prop))

#check (@PreKleene ℕ).toZero

#print KleeneAlgebra

instance ARS {α : Type*} : KleeneAlgebra (α → α → Prop) where
  add f g := fun x y ↦ (f x y ∨ g x y)
  zero := ARS_zero
  add_assoc f g h := by
    ext x y
    change (fun u v ↦ (f u v ∨ g u v) ∨ h u v) x y ↔ (fun u v ↦ f u v ∨ (g u v ∨ h u v)) x y
    simp
    rw [or_assoc]
  zero_add f := by
    ext x y
    change False ∨ f x y ↔ f x y
    simp
  add_zero f := by
    ext x y
    change f x y ∨ False ↔ f x y
    simp
  nsmul := PreKleene_nsmul
  nsmul_zero f := by
    trivial
  nsmul_succ n f := by
    rw [PreKleene_nsmul_succ_succ]
    cases n with
    | zero =>
      rw [PreKleene_nsmul_succ_zero]
      symm
      ext x y
      change (fun u v ↦ (False ∨ f u v)) x y ↔ f x y
      simp
    | succ m =>
      rw [PreKleene_nsmul_succ_succ]
      symm
      exact PreKleene_addIdem f
  add_comm f g := by
    ext x y
    change (fun u v  ↦ f u v ∨ g u v) x y ↔ (fun u v  ↦ g u v ∨ f u v) x y
    exact or_comm
  mul f g := fun u v ↦ (∃ w, f u w ∧ g w v)
  left_distrib f g h := by
    ext x y
    change
      (fun u v ↦ ∃ w, f u w ∧ (g w v ∨ h w v)) x y
      ↔ (fun u v ↦ (∃ w, f u w ∧ g w v) ∨ (∃ w, f u w ∧ h w v)) x y
    simp
    constructor
    · intro hyp
      have w1 := hyp.choose
      have hw1 := hyp.choose_spec


      sorry
    · sorry
    --change
    --  (fun u v ↦ ∃ w, (f u w ∧ g w v) ∨ (f u w ∧ h w v)) x y
    --  ↔ (fun u v ↦ (∃ w, f u w ∧ g w v) ∨ (∃ w, f u w ∧ h w v)) x y
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  bot_le := sorry
  kstar := sorry
  one_le_kstar := sorry
  mul_kstar_le_kstar := sorry
  kstar_mul_le_kstar := sorry
  mul_kstar_le_self := sorry
  kstar_mul_le_self := sorry
