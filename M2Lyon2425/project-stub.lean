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

lemma PreKleene_nsmul_succ_succ {α : Type*} (n : ℕ) (f : α → α → Prop) -- nécessaire
  : PreKleene_nsmul (Nat.succ n) f = f := by
    trivial

lemma PreKleene_addIdem {α : Type*} (f : α → α → Prop) -- nécessaire
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

lemma PreKleene_nsmul_succ_zero {α : Type*} (f : α → α → Prop) -- nécessaire
  : PreKleene_nsmul 0 f = ARS_zero := by
    trivial


def ARS_mul {α : Type*} (f g : α → α → Prop) : α → α → Prop := fun u v ↦ (∃ w, f u w ∧ g w v)

def ARS_one {α : Type*} : α → α → Prop := (fun x y ↦ x = y)

lemma ARS_zero_mul {α : Type*} (f : α → α → Prop) : ARS_mul ARS_zero f = ARS_zero := by
  ext x y
  constructor
  · intro hyp
    rw [ARS_mul] at hyp
    have hw := hyp.choose_spec
    exact hw.left
  · intro absu
    exfalso
    exact absu

lemma ARS_mul_zero {α : Type*} (f : α → α → Prop) : ARS_mul f ARS_zero = ARS_zero := by
  ext x y
  constructor
  · intro hyp
    rw [ARS_mul] at hyp
    have hw := hyp.choose_spec
    exact hw.right
  · intro absu
    exfalso
    exact absu

lemma ARS_mul_assoc {α : Type*} (f g h : α → α → Prop) :
  ARS_mul f (ARS_mul g h) = ARS_mul (ARS_mul f g) h := by
    ext x y
    constructor
    · intro hyp
      rw [ARS_mul] at hyp
      rw [ARS_mul]
      let w1 := hyp.choose
      have ⟨hw1l, hw1r⟩ := hyp.choose_spec
      rw [ARS_mul] at hw1r
      let w2 := hw1r.choose
      have ⟨hw2l, hw2r⟩ := hw1r.choose_spec
      use w2
      rw [ARS_mul]
      constructor
      · use w1
      · exact hw2r
    · rw [ARS_mul, ARS_mul]
      intro hyp
      let w1 := hyp.choose
      have ⟨hw1l, hw1r⟩ := hyp.choose_spec
      rw [ARS_mul] at hw1l
      let w2 := hw1l.choose
      have ⟨hw2l, hw2r⟩ := hw1l.choose_spec
      use w2
      constructor
      · exact hw2l
      · rw [ARS_mul]
        use w1

-- #synth (AddMonoid (ℕ → ℕ → Prop))
-- il n'y a pas de struture de monoïde idempotent sur les relations binaires d'un type


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
  mul f g := ARS_mul f g
  left_distrib f g h := by
    ext x y
    change
      (fun u v ↦ ∃ w, f u w ∧ (g w v ∨ h w v)) x y
      ↔ (fun u v ↦ (∃ w, f u w ∧ g w v) ∨ (∃ w, f u w ∧ h w v)) x y
    simp
    constructor
    · intro hyp
      let we := hyp.choose
      have ⟨hw1, hw2⟩ := hyp.choose_spec
      cases hw2 with
      | inl hw3 =>
        left
        use we
      | inr hw3 =>
        right
        use we
    · intro hyp
      cases hyp with
      | inl hypl =>
        let we := hypl.choose
        have hw1 := hypl.choose_spec
        use we
        constructor
        · exact hw1.left
        · left
          exact hw1.right
      | inr hypr =>
        let we := hypr.choose
        have hw1 := hypr.choose_spec
        use we
        constructor
        · exact hw1.left
        · right
          exact hw1.right
  right_distrib f g h := by
    ext x y
    change
      (fun u v ↦ ∃ w, (f u w ∨ g u w) ∧ h w v) x y
      ↔ (fun u v ↦ (∃ w, f u w ∧ h w v) ∨ (∃ w, g u w ∧ h w v)) x y
    simp
    constructor
    · intro hyp
      let we := hyp.choose
      have ⟨hwl, hwr⟩ := hyp.choose_spec
      cases hwl with
      | inl hwll =>
        left
        use we
      | inr hwlr =>
        right
        use we
    · intro hyp
      cases hyp with
      | inl hypl =>
        let we := hypl.choose
        have ⟨hwl, hwr⟩ := hypl.choose_spec
        use we
        constructor
        · left
          exact hwl
        · exact hwr
      | inr hypr =>
        let we := hypr.choose
        have ⟨hwl, hwr⟩ := hypr.choose_spec
        use we
        constructor
        · right
          exact hwl
        · exact hwr
  zero_mul := ARS_zero_mul
  mul_zero := ARS_mul_zero
  mul_assoc f g h := by symm; exact ARS_mul_assoc f g h
  one := ARS_one
  one_mul := sorry
  mul_one := sorry
  bot_le := sorry
  kstar := sorry
  one_le_kstar := sorry
  mul_kstar_le_kstar := sorry
  kstar_mul_le_kstar := sorry
  mul_kstar_le_self := sorry
  kstar_mul_le_self := sorry
