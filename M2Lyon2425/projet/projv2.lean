import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Quotient
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Init.Data.Cast
import Mathlib.RingTheory.Ideal.Quotient

/-
J'ai commencé mon projet, sur la description de SO_2(F_q)
Pour q= 2^n, j'ai le cardinal de So2 et que les elements sont d'ordre au plus 2,
Je voudrais bien dire que le groupe est isomorphe à (Z/2Z)^n
Pour q non puissance de 2 je suis la preuve faite dans le nouvelles histoires hédonistes  de groupes et géométrie tome 2 de Calderos, p 53
En passant par F_q[X]/X^2+1 -/


/-Dans cette première partie je commence par définir SO(n) puis à lui exhiber des propriétés, dans la seconde partie je définis So2
comme sous groupe d'un groupe de matrices. -/

namespace Matrix

universe u v
open Matrix





variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]


def SpecialOrthogonalGroup :=
  { A : Matrix n n R // A.det = 1 ∧ A*A.transpose= 1 }



scoped[MatrixGroups] notation "SO(" n ", " R ")" => Matrix.SpecialOrthogonalGroup (Fin n) R

/-abbrev SO := SpecialOrthogonalGroup-/

namespace SpecialOrthogonalGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

instance hasCoeToMatrix : Coe (SpecialOrthogonalGroup n R) (Matrix n n R) :=
  ⟨fun A => A.val⟩

local notation:1024 "↑ₘ" A:1024 => ((A : SpecialOrthogonalGroup n R) : Matrix n n R)


theorem ext_iff (A B : SpecialOrthogonalGroup n R) : A = B ↔ ∀ i j, ↑ₘA i j = ↑ₘB i j :=
  Subtype.ext_iff.trans Matrix.ext_iff.symm

@[ext]
theorem ext (A B : SpecialOrthogonalGroup n R) : (∀ i j, ↑ₘA i j = ↑ₘB i j) → A = B :=
  (SpecialOrthogonalGroup.ext_iff A B).mpr

instance hasInv : Inv (SpecialOrthogonalGroup n R) :=
   ⟨fun A => ⟨transpose A , by
  constructor
  · simp[det_transpose ]
    simp[ A.prop.left ]
  · simp [transpose_transpose]
    have h := A.prop.right
    have h1 := (↑ₘA)^2
    rw[mul_eq_one_comm] at h
    exact h
    ⟩⟩

instance hasMul : Mul (SpecialOrthogonalGroup n R) :=
  ⟨fun A B => ⟨↑ₘA * ↑ₘB, by
  constructor
  · rw[det_mul, A.prop.left, B.prop.left ]
    simp
  · rw[transpose_mul,← mul_assoc]
    nth_rewrite 2 [mul_assoc]
    rw[B.prop.right, mul_one, A.prop.right]
   ⟩⟩

instance hasOne : One (SpecialOrthogonalGroup n R) :=
  ⟨⟨1, by
  constructor
  · exact det_one
  · rw[transpose_one,one_mul]⟩⟩

instance : Pow (SpecialOrthogonalGroup n R) ℕ where
  pow x n := ⟨↑ₘx ^ n, by
  constructor
  · rw[det_pow, x.prop.left, one_pow]
  · induction' n with n h
    · rw[pow_zero,transpose_one,one_mul]
    · rw[pow_succ, transpose_mul, ← mul_assoc]
      nth_rewrite 2 [mul_assoc]
      rw[x.prop.right, mul_one,h] ⟩

instance : Inhabited (SpecialOrthogonalGroup n R) :=
  ⟨1⟩
section CoeLemmas


variable (A B : SpecialOrthogonalGroup n R)
theorem coe_mk (A : Matrix n n R) (h : det A = 1 ∧ A*A.transpose= 1) : ↑(⟨A, h⟩ : SpecialOrthogonalGroup n R) = A :=
  rfl

@[simp]
theorem coe_inv : ↑ₘA⁻¹ = transpose A :=
  rfl
@[simp]
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA * ↑ₘB :=
  rfl

@[simp]
theorem coe_one : ↑ₘ(1 : SpecialOrthogonalGroup n R) = (1 : Matrix n n R) :=
  rfl
@[simp]
theorem det_coe : det ↑ₘA = 1 :=
  A.2.1

@[simp]
theorem coe_pow (m : ℕ) : ↑ₘ(A ^ m) = ↑ₘA ^ m :=
  rfl



theorem det_ne_zero [Nontrivial R] (g : SpecialOrthogonalGroup n R) : det ↑ₘg ≠ 0 := by
  rw [g.det_coe]
  norm_num

end CoeLemmas

instance monoid : Monoid (SpecialOrthogonalGroup n R) :=
  Function.Injective.monoid (↑) Subtype.coe_injective coe_one coe_mul coe_pow

#check (SpecialOrthogonalGroup)

instance : Group (SpecialOrthogonalGroup n R) :=
  {SpecialOrthogonalGroup.monoid, SpecialOrthogonalGroup.hasInv with
    inv_mul_cancel := fun A => by
      have ha := A.prop.right
      ext1 i j
      simp only [coe_mul, coe_inv, coe_one]
      rw[mul_eq_one_comm] at ha
      exact congrFun (congrFun ha i) j
      }


variable (K : Type v) [Field K] [Fintype K]

open scoped MatrixGroups


theorem SO2_inv_co (A : SpecialOrthogonalGroup (Fin 2) R) : A.1 1 0 = -A.1 0 1 ∧ A.1 0 0 = A.1 1 1 ∧ (A.1 0 0)^2 + (A.1 1 0)^2 = 1  := by
  have ⟨ ha1 ,ha2⟩   := A.2
  have h := mul_adjugate A.1
  rw[ ha1] at h
  simp only [one_smul] at h
  have h3 :  (A.1)ᵀ * ( A.1 * (A.1).adjugate)= (A.1)ᵀ  *  (A.1 * (A.1).adjugate)
  simp
  nth_rewrite 1 [ h ] at h3
  rw[← mul_assoc] at h3
  rw[mul_eq_one_comm] at ha2
  rw[ha2, one_mul, mul_one] at h3
  rw[← Matrix.ext_iff ] at h3
  have h5 := h3
  specialize h3 0 1
  rw[transpose_apply ] at h3
  have := Matrix.adjugate_fin_two A.1
  rw[this ] at h3 h5
  simp only [Fin.isValue, of_apply, cons_val', cons_val_one, head_cons, empty_val',
    cons_val_fin_one, cons_val_zero] at h3
  specialize h5 0 0
  simp only [Fin.isValue, transpose_apply, of_apply, cons_val', cons_val_zero, empty_val',
    cons_val_fin_one] at h5
  rw[Matrix.det_fin_two, ← h5 ] at ha1
  have h6 : A.1 0 0 ^ 2 + A.1 1 0 ^ 2 = 1 := by
    rw[pow_two,pow_two ]
    nth_rewrite 1[h3 ]
    rw[sub_eq_add_neg] at ha1
    simp only [Fin.isValue, neg_mul]
    exact ha1
  constructor
  exact h3
  constructor
  exact h5
  exact h6




variable {F : Type*} [Field F]
variable [Fintype F]

def make_So2 (a: F )( b: F )(h : a^2+b^2=1) : SO(2,F ) := by
  constructor
  swap
  · exact  !![a,-b ; b ,a]
  · constructor
    · rw[det_fin_two]
      change a*a - (-b)*b = 1
      simp
      repeat rw[← pow_two]
      exact h
    · have hT : (transpose !![a, -b; b, a])= !![a, b; -b, a] := by
        rw [← Matrix.ext_iff ]
        intro i j
        match i, j with
        |0, 0 => rfl
        |0,1 => rfl
        |1, 0 => rfl
        |1,1 => rfl
      rw [hT]
      rw[Matrix.mul_fin_two]
      rw [← Matrix.ext_iff ]
      intro i j
      match i, j with
      |0, 0 => simp; rw[← pow_two,← pow_two ]; exact h
      |0,1 => simp; rw[mul_comm]; simp
      |1, 0 => simp ;rw[mul_comm]; simp
      |1,1 => simp; rw[← pow_two,← pow_two, add_comm ]; exact h





-- Partie sur la charactéristique 2

/-Dans cette section je cherche à montrer que SO(2,F(2^n)) est isomorphe a (Z/2Z)^n
J'ai pas réussi à montrer exactement cela, mais j'ai que SO(2,F(2^n)) est un groupe dans lequel tout élément est son propre inverse et
qui est de cardinal 2^n; j'aurais voulu conclure en utilisant le théorème de structure des groupes abéliens finis. -/

section Char2

theorem square_char_2 (h : CharP F 2) (A : SO(2, F)) : (A.1= (A⁻¹).1) := by
  have ha := (SO2_inv_co A).left
  rw[CharTwo.neg_eq] at ha
  have haa : transpose A.1 = A.1
  rw[← Matrix.ext_iff ]
  intro i j
  rw[transpose_apply ]
  match i, j with
  |0, 0 => rfl
  |0,1 => exact ha
  |1, 0 => exact (symm ha)
  |1,1 => rfl
  simp only [coe_inv]
  exact(symm haa)

theorem auto_inv_char2 (h : CharP F 2) (A : SO(2, F)) : A= (A⁻¹) := by
  have ha := square_char_2 (h : CharP F 2) (A : SO(2, F))
  exact ext A A⁻¹ fun i ↦ congrFun (congrFun ha i)



def f (A:SO(2,F)) := A.1 0 0


variable {F_2_exp_n : Type*} [Field F_2_exp_n][Fintype F_2_exp_n][char2 :CharP F_2_exp_n 2]

noncomputable def m := Nat.card F_2_exp_n

theorem auto_inv_char2'  (A : SO(2, F_2_exp_n)) : A= (A⁻¹) := by
  have := auto_inv_char2 (char2) (A)
  exact this


instance commGroup : CommGroup (SO(2,F_2_exp_n))  where

  mul_comm (a:SO(2,F_2_exp_n)) b := by
    rw [ auto_inv_char2' (a*b)]
    simp
    nth_rewrite 2 [auto_inv_char2' b]
    nth_rewrite 2 [auto_inv_char2' a]
    rfl


-- AddCommGroup.equiv_directSum_zmod_of_fintype (Additive SO(2,F_2_exp_n))

theorem card_so2_char2  : (Nat.card SO(2,F_2_exp_n) = Nat.card F_2_exp_n) := by
refine Nat.card_eq_of_bijective f ?_
constructor
· intro A B h
  rw[ext_iff]
  intro i j
  repeat rw[f] at h
  have ha := SO2_inv_co A
  have hb := SO2_inv_co B
  have h1A : A.1 1 0 ^2 = 1+ A.1 0 0^2 :=  by
    have h2 :  A.1 0 0^2 + ( A.1 0 0^2 + A.1 1 0 ^2) = A.1 0 0^2 +  (A.1 0 0^2 + A.1 1 0 ^2 ):= by rfl
    nth_rewrite 2 [ha.right.right] at h2
    rw[← add_assoc] at h2
    rw[CharTwo.add_self_eq_zero] at h2
    rw[zero_add] at h2
    rw[add_comm]
    exact h2
  have  : A.1 1 0^2  =(frobenius F_2_exp_n 2) (A.1 1 0)  := by
    rfl
  rw[this] at h1A
  have h1B : B.1 1 0 ^2 = 1+ B.1 0 0^2 :=  by
    have h2 :  B.1 0 0^2 + ( B.1 0 0^2 + B.1 1 0 ^2) = B.1 0 0^2 +  (B.1 0 0^2 + B.1 1 0 ^2 ):= by rfl
    nth_rewrite 2 [hb.right.right] at h2
    rw[← add_assoc] at h2
    rw[CharTwo.add_self_eq_zero] at h2
    rw[zero_add] at h2
    rw[add_comm]
    exact h2
  have  : B.1 1 0^2  =(frobenius F_2_exp_n 2) (B.1 1 0)  := by
    rfl
  rw[this] at h1B
  have h11 := h
  rw[ha.right.left, hb.right.left] at h11
  rw[← h ] at h1B
  rw[← h1B] at h1A

  have h10 : A.1 1 0 = B.1 1 0 := by
    apply injective_frobenius F_2_exp_n 2
    exact h1A

  have h01 :  A.1 0 1 = B.1 0 1 := by
    have : A.1 1 0 = A.1 0 1 := by
      have hh : -A.1 0 1 = - A.1 0 1 := by rfl
      nth_rewrite 1 [CharTwo.neg_eq] at hh
      rw[← ha.left] at hh
      exact hh.symm
    rw[← this]
    rw[h10 ]
    have : B.1 1 0 = B.1 0 1 := by
      have hh : -B.1 0 1 = - B.1 0 1 := by rfl
      nth_rewrite 1 [CharTwo.neg_eq] at hh
      rw[← hb.left] at hh
      exact hh.symm
    exact this

  match i, j with
  |0, 0 => exact h
  |0,1 => exact h01
  |1, 0 => exact h10
  |1,1 =>  exact h11

· intro a
  have b:= bijective_frobenius F_2_exp_n 2
  have c := b.right
  specialize c (-a^2+1)
  obtain ⟨ b0, hb⟩ := c
  have hb0 : b0^2 =-a^2 +1 := by
    exact hb
  set A := !![a,-b0 ; b0 ,a]
  have hA : det A = 1 ∧ A*A.transpose= 1 := by
    constructor
    · rw[det_fin_two]
      change a * a - (-b0) * b0 = 1
      simp
      repeat rw[← pow_two]
      change a^2 + (frobenius F_2_exp_n 2) b0 = 1
      rw[hb]
      simp
    · have h : a^2 + b0^2 = 1 := by
        rw[hb0]
        simp
      have hT : (transpose !![a, -b0; b0, a])= !![a, b0; -b0, a] := by
        rw [← Matrix.ext_iff ]
        intro i j
        match i, j with
        |0, 0 => rfl
        |0,1 => rfl
        |1, 0 => rfl
        |1,1 => rfl
      rw [hT]
      rw[Matrix.mul_fin_two]
      rw [← Matrix.ext_iff ]
      intro i j
      match i, j with
      |0, 0 => simp; rw[← pow_two,← pow_two ]; exact h
      |0,1 => simp; rw[mul_comm]; simp
      |1, 0 => simp ;rw[mul_comm]; simp
      |1,1 => simp; rw[← pow_two,← pow_two, add_comm ]; exact h

  use ↑⟨A, hA⟩
  rw[f ]
  simp
  rfl


theorem structure_char2' : ((SO(2,F_2_exp_n)) ≃* ZMod (2) ^ n  ) := by
  sorry


end  Char2

end SpecialOrthogonalGroup


end Matrix


/-Dans cette section je considère l'ensemble D de matrices, pour étudier SO2-/



section char_sg_2

variable {F : Type*} [Field F]

def D (F : Type*) [Field F] := {A : Matrix (Fin 2) (Fin 2) F // A 0 0 = A 1 1 ∧ A 1 0 = -A 0 1}


instance hasCoeToMatrix : Coe (D F) (Matrix (Fin 2) (Fin 2) F) :=
  ⟨fun A => A.val⟩

local notation:1024 "↑ₘ" A:1024 => ((A : D F) : Matrix (Fin 2) (Fin 2) F)

theorem ext_iff (A B : D F) : A = B ↔ ∀ i j, ↑ₘA i j = ↑ₘB i j :=
  Subtype.ext_iff.trans Matrix.ext_iff.symm

@[ext]
theorem ext (A B : D F) : (∀ i j, ↑ₘA i j = ↑ₘB i j) → A = B :=
  (ext_iff A B).mpr


instance [Field F] : Zero (D F) :=
  ⟨⟨0, by simp [Matrix.zero_apply]⟩⟩

instance [Field F] : One (D F) :=
  ⟨⟨1, by simp [Matrix.one_apply]⟩⟩

instance [Field F] : Add (D F) :=
  ⟨fun A B => ⟨A.val + B.val, by
    simp [Matrix.add_apply, A.property.1, A.property.2, B.property.1, B.property.2]
    ring⟩⟩

instance [Field F] : Neg (D F) :=
  ⟨fun A => ⟨-A.val, by
    simp [Matrix.neg_apply, A.property.1, A.property.2]

    ⟩⟩
instance [Field F] : Sub (D F) := ⟨fun A B => ⟨A.val - B.val, by
  simp [Matrix.sub_apply, A.property.1, A.property.2, B.property.1, B.property.2]
  ring
  ⟩⟩


instance [Field F] : Mul (D F) :=
  ⟨fun A B => ⟨A.val * B.val, by
    simp [Matrix.mul_apply, A.property.1, A.property.2, B.property.1, B.property.2]
    ring
    ⟩⟩



instance [Field F] : SMul ℕ (D F) :=
  ⟨fun n A => ⟨n • A.val, by
    simp [Matrix.smul_apply, A.property.1, A.property.2]
    ⟩⟩

instance [Field F] : SMul ℤ (D F) :=
  ⟨fun n A => ⟨n • A.val, by
    simp [Matrix.smul_apply, A.property.1, A.property.2]
    ⟩⟩

instance [Field F] : Pow (D F) ℕ :=
  ⟨fun A n => ⟨A.val ^ n, by
    induction' n with n hn
    · simp
    · constructor
      · rw[pow_succ]
        simp [Matrix.mul_apply, A.property.1, A.property.2,hn]
        ring
      · rw[pow_succ]
        simp [Matrix.mul_apply, A.property.1, A.property.2,hn]
      ⟩⟩

instance [Field F] : NatCast (D F) :=
 ⟨fun n =>
⟨n • 1, by
    simp [Matrix.smul_apply]
  ⟩⟩



instance [Field F] : IntCast (D F) := ⟨fun n =>
⟨n • 1, by
    simp [Matrix.smul_apply]
  ⟩⟩

instance [Field F] : Inhabited (D F) := ⟨0⟩

section coe

-- coercion de D à Matrix (Fin 2) (Fin 2) F
instance [Field F] : Coe (D F) (Matrix (Fin 2) (Fin 2) F) :=
  ⟨λ A => A.val⟩

@[simp] lemma coe_D_val {A : D F} : (A : Matrix (Fin 2) (Fin 2) F) = A.val := rfl

variable (A B : D F)

theorem coe_mk (A : Matrix (Fin 2) (Fin 2) F) (h : A 0 0 = A 1 1 ∧ A 1 0 = -A 0 1) : ↑(⟨A, h⟩ : D F) = A :=
  rfl

@[simp]
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA * ↑ₘB :=
  rfl

@[simp]
theorem coe_one : ↑ₘ(1 : D F) = (1 : Matrix (Fin 2) (Fin 2) F) :=
  rfl

@[simp]
theorem coe_zero : ↑ₘ(0 : D F) = (0 : Matrix (Fin 2) (Fin 2) F) :=
  rfl

@[simp]
theorem coe_add (A B : D F) : ↑ₘ(A + B) = ↑ₘA + ↑ₘB :=
 rfl

@[simp]
theorem coe_neg : ↑ₘ(-A) = -↑ₘA := by
  rfl

@[simp]
theorem coe_sub : ↑ₘ(A - B) = ↑ₘA - ↑ₘB := by
  rfl

@[simp]
theorem coe_pow (n : ℕ) : ↑ₘ(A ^ n) = ↑ₘA ^ n := by
  rfl

@[simp]
theorem coe_nsmul (n : ℕ) (A : D F ): ↑ₘ(n • A) = n • ↑ₘA := by
  rfl

@[simp]
theorem coe_zsmul (n : ℤ)  (A : D F ) : ↑ₘ(n • A) = n • ↑ₘA := by
  rfl

@[simp] theorem coe_nat_cast (n : ℕ) : ↑ₘ(n : D F) = (n : Matrix (Fin 2) (Fin 2) F) := by
change ↑ₘ(n • 1) = (n : Matrix (Fin 2) (Fin 2) F)
rw [coe_nsmul, coe_one]
simp

@[simp] theorem coe_int_cast (n : ℤ) : ↑ₘ(n : D F) = (n : Matrix (Fin 2) (Fin 2) F) := by
change ↑ₘ(n • 1) = (n : Matrix (Fin 2) (Fin 2) F)
rw [coe_zsmul, coe_one]
simp

end coe

instance ringD : Ring (D F) :=
  Function.Injective.ring ( ↑ ) Subtype.coe_injective coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul coe_pow coe_nat_cast coe_int_cast


section poly

open Quotient
open Polynomial
open Ideal

def E (F : Type*) [Field F] := F[X]⧸Ideal.span ({Polynomial.X^2 + 1} : Set F[X])
-- Dans la suite je n'utilise pas E dans le code mais uniquement dans les notations.
-- Je n'ai pas réussi à montrer que E est un anneaux commutatif mais
-- (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) synth bien en anneau commutatif.

#check (E F)


/- This is proven in mathlib. -/
variable {R : Type*} [CommRing R]

instance commRing (I : Ideal R) : CommRing (R ⧸ I) where
  __ : AddCommGroup (R ⧸ I) := inferInstance
  __ : CommRing (Quotient.ringCon I).Quotient := inferInstance


#synth CommRing (E F)

#synth CommRing F[X]
#check Ideal.span ({Polynomial.X^2 + 1} : Set (Polynomial F))
#synth CommRing (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))


noncomputable def p' : D F →+ F[X] :=
{ toFun := λ A => C (A.val 0 0) + C (A.val 1 0) * X,
  map_zero' := by simp [Matrix.zero_apply],
  map_add' := by
    intros A B
    simp [Matrix.add_apply]
    ring }

-- Projection de F[X] vers E
noncomputable def proj_FX_to_E (F : Type*) [Field F] :
    F[X] →+* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) :=
  Ideal.Quotient.mk (Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))

#check proj_FX_to_E

/-Les lemmes et théorèmes suivants servirons à montrer que proj_FX_to_E ∘ p' est un isomorphisme d'anneaux -/

@[simp]
lemma proj_FX_to_E_Xsquare_eq_moins1 (F : Type*) [Field F] : proj_FX_to_E F (X^2) = -1 := by
  apply Ideal.Quotient.eq.2
  rw [sub_neg_eq_add]
  exact Ideal.subset_span (Set.mem_singleton _)

@[simp]
lemma proj_FX_to_quotient_Xsquare_eq_moins1 (F : Type*) [Field F] : (Ideal.Quotient.mk (span {(X:F[X]) ^ 2 + 1}) (X^2)) = -1 := by
  apply Ideal.Quotient.eq.2
  rw [sub_neg_eq_add]
  exact Ideal.subset_span (Set.mem_singleton _)

@[simp]
lemma deg_Xsquare_plus1 : ((X:F[X])^2 + 1).degree = 2 := by
  rw [degree_add_eq_left_of_degree_lt]
  rw [degree_X_pow]
  simp
  rw[degree_X_pow]
  simp

lemma deg_a_plusbX_le_one (a b : F) : (C a + C b * X).degree ≤ 1 := by
  refine ((C a + C b * X).degree_le_iff_coeff_zero 1).2 (fun m hm ↦ ?_)
  replace hm := Nat.one_lt_cast.1 hm
  have : b * X.coeff m = 0 := by
    refine mul_eq_zero.2 ?_
    right
    exact Polynomial.coeff_X_of_ne_one (ne_of_lt (Nat.one_lt_cast.1 hm)).symm
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_add, this, coeff_C_ne_zero (Nat.not_eq_zero_of_lt hm), zero_add]

lemma deg_c (c : F[X]) (hc : 2 + c.degree ≤ 1) : c.degree = ⊥ := by
  by_cases h : c = 0
  · rw [h]
    rfl
  · exfalso
    rw [degree_eq_natDegree h] at hc
    have := le_trans (Nat.add_le_add_left c.natDegree.zero_le 2) (WithBot.coe_le_one.1 hc)
    contradiction

@[simp]
theorem proj_FX_to_E_eq_id_on_deg1 (F : Type*) [Field F] a b : (proj_FX_to_E F (C a + C b * X) = 0) → a = 0 ∧ b =0 := by
  intro h
  have h' := Ideal.Quotient.eq.1 h
  simp only [Set.mem_singleton_iff, Ideal.mem_span_singleton, Polynomial.ext_iff] at h'
  choose c hc using h'
  simp at hc
  have deg_hc := congr_arg Polynomial.degree hc
  simp only [Polynomial.degree_mul, Polynomial.degree_X_pow, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_C] at deg_hc
  rw[deg_Xsquare_plus1] at deg_hc
  have : (C a + C b * X).degree ≤ 1 := by
    exact deg_a_plusbX_le_one a b
  rw[deg_hc] at this
  have  : c.degree = ⊥ := by
    exact deg_c c this
  simp at this
  rw[this] at hc
  simp only [mul_zero] at hc
  constructor
  · rw[Polynomial.ext_iff] at hc
    specialize hc 0
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at hc
    simp at hc
    exact hc
  · rw[Polynomial.ext_iff] at hc
    specialize hc 1
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at hc
    simp at hc
    exact hc

theorem desc_E  (F : Type*) [Field F] (f: F[X]) : (∃ g : F[X], g.degree ≤ 1 ∧ proj_FX_to_E F g = proj_FX_to_E F f) := by
  set g := f %ₘ (X^2 + 1)
  use g
  constructor
  · have h : (f %ₘ (X^2 + 1)).degree < (X^2 + 1:F[X]).degree := by
      refine degree_modByMonic_lt f ?_
      apply monic_X_pow_add_C
      exact Ne.symm (Nat.zero_ne_add_one 1)
    have h' : (X^2 + 1:F[X]).degree = 2 := by
      exact deg_Xsquare_plus1
    rw[h'] at h
    exact Order.le_of_lt_succ h
  · apply Ideal.Quotient.eq.2
    change f %ₘ (X ^ 2 + 1) - f ∈ span {X ^ 2 + 1}
    simp only [Set.mem_singleton_iff, Ideal.mem_span_singleton, Polynomial.ext_iff]
    use -(f / (X^2 + 1))
    have h_div :   (X^2 + 1) *  (f / (X^2 + 1))  + (f % (X^2 + 1))  = f:= by
      apply EuclideanDomain.div_add_mod
    have : f/ (X^2+1) = f/ₘ (X^2+1) := by
      refine Eq.symm (divByMonic_eq_div f ?hq)
      apply monic_X_pow_add_C
      exact Ne.symm (Nat.zero_ne_add_one 1)
    have : f %ₘ (X^2 + 1) = f % (X^2 + 1) := by
      refine modByMonic_eq_mod f ?hq
    rw[this.symm] at h_div
    nth_rewrite 2 [← h_div]
    ring

lemma p_deg_one_eq (F : Type*) [Field F] (g' : F[X]) (hg1 : g'.degree ≤ 1) : ( g' = C (g'.coeff 0) + C (g'.coeff 1) * X) := by
  rw[Polynomial.ext_iff]
  intro i
  if hi : i = 0 then
    rw[hi]
    change g'.coeff 0 = (C (g'.coeff 0) + C (g'.coeff 1) * X).coeff 0
    simp only [coeff_C, coeff_X, coeff_add, coeff_C_mul, zero_mul, add_zero]
    ring_nf
  else
  if hii : i = 1 then
    rw[hii]
    simp only [coeff_C, coeff_X, coeff_add, coeff_C_mul, zero_mul, add_zero]
    ring_nf
  else
  have hiii :  2 ≤ i := by
    refine (Nat.two_le_iff i).mpr ?_
    constructor
    exact hi
    exact hii
  simp only [coeff_C, coeff_X, coeff_add, coeff_C_mul, zero_mul, add_zero,hi, hii ]
  ring_nf
  rw [g'.degree_le_iff_coeff_zero 1] at hg1
  rw[hg1]
  have hiiii : (1=i)=False := by
    exact eq_false fun a ↦ hii (id (Eq.symm a))
  simp only [hiiii]
  ring_nf
  exact Nat.one_lt_cast.mpr hiii

noncomputable def pi  (F : Type*) [Field F] (a : (F ×  F)) := proj_FX_to_E F (C a.1 + C a.2 * X)

noncomputable def desc_E' (F : Type*) [Field F] :F × F ≃ (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
  refine Equiv.ofBijective (pi F) ?hf
  constructor
  · intro a b h
    replace h : proj_FX_to_E F (C a.1 + C a.2 * X) = proj_FX_to_E F (C b.1 + C b.2 * X) := by
      apply h
    have : proj_FX_to_E F (C a.1 + C a.2 * X - (C b.1 + C b.2 * X))  =0 := by
      change (Ideal.Quotient.mk (span {X ^ 2 + 1})) (C a.1 + C a.2 * X - (C b.1 + C b.2 * X))  =0
      rw[sub_eq_add_neg]
      rw[(Ideal.Quotient.mk (span {X ^ 2 + 1})).map_add]
      rw[proj_FX_to_E] at h
      rw[h]
      exact add_eq_zero_iff_neg_eq.mpr rfl
    rw[RingHom.map_add, RingHom.map_add] at h
    have : proj_FX_to_E F (C (a.1-b.1) + C (a.2-b.2) * X) = 0 := by
      simp only[RingHom.map_add, C_sub, C_sub, RingHom.map_sub]
      have : (C a.2 - C b.2) * X = (C a.2) *X  - (C b.2)*X := by
        exact sub_mul (C a.2) (C b.2) X
      rw [this, RingHom.map_sub]
      have : (proj_FX_to_E F) (C a.1) - (proj_FX_to_E F) (C b.1) + ((proj_FX_to_E F) (C a.2 * X) - (proj_FX_to_E F) (C b.2 * X)) = (proj_FX_to_E F) (C a.1) + (proj_FX_to_E F) (C a.2 * X) - ((proj_FX_to_E F) (C b.1) + (proj_FX_to_E F) (C b.2 * X)) := by
        ring_nf
      rw[this,h]
      ring_nf
    have : (a.1 - b.1) = 0 ∧   (a.2 - b.2) = 0 := by
      apply  proj_FX_to_E_eq_id_on_deg1
      exact this
    refine Prod.ext_iff.mpr ?hf.left.a
    constructor
    exact sub_eq_zero.1 this.1
    exact sub_eq_zero.1 this.2
  · intro f
    obtain ⟨g, hg⟩ := desc_E F (Quotient.out' f)
    use (g.coeff 0, g.coeff 1)
    have : g = C (g.coeff 0) + C (g.coeff 1) * X := by
      exact p_deg_one_eq F g hg.1
    change proj_FX_to_E F (C (g.coeff 0) + C (g.coeff 1) * X) = f
    rw [← this, hg.2]
    exact Quotient.out_eq' f


noncomputable def desc_F_quo_deg_1 (F : Type*) [Field F] (i : F) : F ≃ (F[X] ⧸ Ideal.span ({X - C i} : Set F[X])) := by
  sorry

-- Compose p' et la projection de F[X] dans E pour obtenir un morphisme d'anneaux

noncomputable def p : D F →+* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) :=
  {
  toFun := fun A ↦ (proj_FX_to_E F) (p' A)
  map_one' := by
    rw [proj_FX_to_E, p']
    dsimp
    change (Ideal.Quotient.mk (span {X ^ 2 + 1})) (C 1 + C 0 * X) = 1
    have : (Polynomial.C 0 : F[X]) = 0 := by
      exact Polynomial.C_eq_zero.2 (by rfl)
    have : (Ideal.Quotient.mk (span {X ^ 2 + 1})) (C 1 + C 0 * X: F[X]) = (Ideal.Quotient.mk (span {X ^ 2 + 1})) (1:F[X]) := by
      simp only [this, zero_mul, add_zero, Polynomial.C_1]
    rw [this, ← (Ideal.Quotient.mk (span {X ^ 2 + 1})).map_one]
  map_zero' := by
    change (fun A ↦ (proj_FX_to_E F) (p' A)) 0 = 0
    dsimp
    rw [p'.map_zero, proj_FX_to_E, ← (Ideal.Quotient.mk (span {X ^ 2 + 1})).map_zero]
  map_add' := by
    intros A B
    change (proj_FX_to_E F) (p' (A+B)) = (proj_FX_to_E F) (p' A + p' B)
    rw[p'.map_add, proj_FX_to_E]
  map_mul' := by
    intros A B
    dsimp
    rw [p']
    change (Ideal.Quotient.mk (span {X ^ 2 + 1})) (C ((A.val * B.val) 0 0) + C ((A.val * B.val) 1 0) * X) =
           (Ideal.Quotient.mk (span {X ^ 2 + 1})) ((C (A.val 0 0) + C (A.val 1 0) * X) * (C (B.val 0 0) + C (B.val 1 0) * X))
    ring_nf
    nth_rewrite 2 [ (Ideal.Quotient.mk (span {X ^ 2 + 1})).map_add]
    nth_rewrite 2 [ (Ideal.Quotient.mk (span {X ^ 2 + 1})).map_add]
    nth_rewrite 1 [ (Ideal.Quotient.mk (span {X ^ 2 + 1})).map_mul]
    nth_rewrite 1 [ (Ideal.Quotient.mk (span {X ^ 2 + 1})).map_mul]
    rw[proj_FX_to_quotient_Xsquare_eq_moins1]
    repeat rw[Matrix.mul_apply]
    have : (∑ j : Fin 2, A.val 0 j * B.val j 0) = A.val 0 0 * B.val 0 0 + A.val 0 1 * B.val 1 0 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one]
    rw[this]
    have : (∑ j : Fin 2, A.val 1 j * B.val j 0) = A.val 1 0 * B.val 0 0 + A.val 1 1 * B.val 1 0 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one]
    rw[this]
    rw[← A.property.1, A.property.2]
    ring_nf
    change (Ideal.Quotient.mk (span {X ^ 2 + 1})) (C (A.val 0 0 * B.val 0 0 + A.val 0 1 * B.val 1 0) + C (A.val 0 0 * B.val 1 0 -  B.val 0 0 * A.val 0 1 ) * X) =
               (Ideal.Quotient.mk (span {X ^ 2 + 1})) ((X * C (A.val 0 0) * C (B.val 1 0) + X * C (-A.val 0 1) * C (B.val 0 0)) -
               (C (-A.val 0 1)) *  (C (B.val 1 0)) +
                (C (A.val 0 0) * C (B.val 0 0)))
    have : (C (A.val 0 0 * B.val 0 0 + A.val 0 1 * B.val 1 0) + C (A.val 0 0 * B.val 1 0 -  B.val 0 0 * A.val 0 1 ) * X) = ((X * C (A.val 0 0) * C (B.val 1 0) + X * C (-A.val 0 1) * C (B.val 0 0)) -
               (C (-A.val 0 1)) *  (C (B.val 1 0)) +
                              (C (A.val 0 0) * C (B.val 0 0))) := by
                simp only [C_mul, C_add, C_neg, C_sub]
                ring
    rw [this]
  }


theorem p_inj (F : Type*) [Field F] :  Function.Injective (p : D F →+* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))) := by
  rw [injective_iff_map_eq_zero]
  intro A  h
  simp only [p,p'] at h
  dsimp at h
  have h' := proj_FX_to_E_eq_id_on_deg1 F (A.val 0 0) (A.val 1 0) h
  have h0 := h'.1
  have h1 := h'.2
  rw[A.property.2,neg_eq_zero] at h1
  rw[A.property.1] at h0
  ext i j
  match i, j with
  | 0, 0 => exact h'.1
  | 1, 0 => exact h'.2
  | 0, 1 => exact h1
  | 1, 1 => exact h0



theorem p_surj (F : Type*) [Field F] : Function.Surjective (p : D F →+* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))) := by
  intro f
  have h := @Ideal.Quotient.mk_surjective (R:=F[X]) (I :=Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))
  obtain ⟨g, hg⟩ := h f
  have hg := desc_E F g
  obtain ⟨g', hg'⟩ := hg
  have hg1 := hg'.1
  set a := g'.coeff 0
  set b := g'.coeff 1
  have : g' = C a + C b * X := by
    exact p_deg_one_eq F g' hg1
  set A : Matrix (Fin 2) (Fin 2) F := !![a, -b; b, a]
  set B : D F := ⟨ A , {
    left := by rfl
    right := by change b = - - b
                rw [neg_neg]    }  ⟩
  use B
  rw[p]
  dsimp
  rw[p']
  dsimp
  change proj_FX_to_E F (C a + C b * X) = f
  rw[← this, hg'.right]
  rw[proj_FX_to_E, hg]

theorem p_iso (F : Type*) [Field F ] : Function.Bijective (p : D F →+* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))) := by
  constructor
  apply p_inj
  apply p_surj

#check CommGroup (D F)ˣ

noncomputable def D_iso_E (F : Type*) [Field F ] : D F  ≃+* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) :=
  RingEquiv.ofBijective (p : D F →+* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))) (p_iso F)

noncomputable def D_star_iso_E_star (F : Type*) [Field F ] : (D F)ˣ  ≃* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ := by
  have :  D F  ≃+* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := D_iso_E F
  refine Units.mapEquiv ?h
  exact this.toMulEquiv

/-On définit q le déterminant qui réalise un morphisme de groupe entre les inversibles de D F et ceux de F-/

def q : (D F)ˣ →* Fˣ := {
  toFun := λ A => ⟨ Matrix.det (A.val.val), Matrix.det (A.2.val), by rw[← Matrix.det_mul, ← coe_mul , A.3,coe_one , Matrix.det_one]
   , by rw[← Matrix.det_mul, ← coe_mul , A.4 ,coe_one , Matrix.det_one]  ⟩
  map_one' := by
    simp only [Units.val_one, Subtype.coe_mk, coe_one, Matrix.det_one]
    exact Units.ext rfl
  map_mul' := by
    intros x y
    ext
    simp only [Units.val_mul, Subtype.coe_mk, coe_mul, Matrix.det_mul]}


#check q

end poly

section det


variable [Fintype F][hF : Fact (ringChar F ≠ 2)]

open Finset

/-Je souhaite montrer que le déterminant est surjectif,
Pour cela je voulais montrer que {a : F | ∃ d : F, (c - d^2) = a} et   {a : F | ∃ b : F, b^2 = a} sont de cardinal (Cardinal F +1)/2
tous les deux. Donc leur intersection est non vide.
Je n'ai pas réussi à le faire entièrement -/

def B  (F : Type*) [Field F ] [Fintype F ]  c := {a : F | ∃ d : F, (c - d^2) = a}
def sqq  (F : Type*) [Field F ] [Fintype F] : (Fˣ) →* Fˣ := MonoidHom.id (Fˣ) * MonoidHom.id (Fˣ)

def A   (F : Type*) [Field F ] [Fintype F ] := {a : F | ∃ b : F, b^2 = a}

/-a→ a^2 a un noyau de cardinal 2 -/

theorem kersqq (F : Type*) [Field F ] [Fintype F ](hF : ringChar F ≠ 2) :
    Nat.card (MonoidHom.ker (sqq F): Set Fˣ) =  2 := by

  have h : MonoidHom.ker (sqq F) = ({1 , -1 } : Set Fˣ) := by
    refine Set.Subset.antisymm ?h₁ ?h₂
    · intros x hx
      have hx2 : x ∈ (sqq F).ker := by
        exact hx
      rw [MonoidHom.mem_ker] at hx2
      change x * x = 1 at hx2
      rw[← pow_two ] at hx2
      have h : (x^2).val = 1 := by
        simp only [hx2]
        rfl
      have : x.val^2 =1 := by
        exact h
      have : x.val ∈ ({1 , -1 } : Set F) := by

        have ht : x.val = 1 ∨ x.val = -1 := by
          exact sq_eq_one_iff.mp h
        exact ht
      cases this with
      | inl h => refine Set.mem_insert_iff.mpr ?h₁.inl.a;  left; exact Units.ext h
      | inr h => refine Set.mem_insert_iff.mpr ?h₁.inr.a; right; exact Units.ext h
    · intro x hx
      refine SetLike.mem_coe.mpr ?h₂.a
      rw[Set.mem_insert_iff] at hx
      rw[sqq]
      change x*x=1
      cases hx with
      | inl h => rw[h,one_mul]
      | inr h => rw[h, ← pow_two, neg_one_sq]
  rw[h]
  rw[ Nat.card_eq_two_iff]
  use (⟨(1 : Fˣ), by exact Set.mem_insert 1 ({-1})⟩ : ({1, -1} : Set Fˣ))
  use (⟨(-1 : Fˣ), by exact Set.mem_insert_of_mem 1 rfl ⟩ : ({1, -1} : Set Fˣ))
  constructor
  have  : (1 : Fˣ) ≠ (-1 : Fˣ) := by
    have h_ne : (1:F) ≠ (-1 : F) := by exact Ne.symm (Ring.neg_one_ne_one_of_char_ne_two hF)

    by_contra h

    have : (1:F) = (-1 : F) := by
      rw[ Units.ext_iff] at h
      exact h
    exact h_ne this
  exact Subtype.ne_of_val_ne this
  refine Eq.symm (Set.Subset.antisymm ?h.right.h₁ fun ⦃a⦄ _ ↦ trivial)
  intro x hx
  simp only [Set.mem_def] at hx
  cases x with
  | mk val property =>
    have h : val = 1 ∨ val = -1 := by
      exact property
    cases h with
    | inl h => refine Set.mem_insert_iff.mpr ?h.left.a; left; exact Subtype.mk_eq_mk.mpr h
    | inr h => refine Set.mem_insert_iff.mpr ?h.right.a; right; refine
      Set.mem_singleton_of_eq ?h.right.a.h.H; exact Subtype.mk_eq_mk.mpr h



/-En utilisant les relations noyaux image on peut obtenir le cardinal de A et B-/

theorem number_of_squares (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2) :
    Nat.card (A F) = (Nat.card F +1)/2 := by
  have : A F = Set (MonoidHom.range (sqq))


theorem number_of_squares' (F : Type*) [Field F ] [Fintype F ] (hF : ringChar F ≠ 2) c : Nat.card (B F c) = (Nat.card F +1)/2 := by
   sorry

/-Outre le cardinal de A et B je n'ai pas montré que le cardinal d'un corps fini de caractéristique différente de 2 est impair.-/

theorem antecedent_det (F : Type*) [Field F ] [Fintype F ] [DecidableEq F] (hF : ringChar F ≠ 2) c :
    (∃ a b : F , a^2 = c - b^2 ) := by
  have hA := number_of_squares F hF
  have hB := number_of_squares' F hF c
  have hAA : Fintype (A F) := by
    exact Set.fintypeRange fun y ↦ y ^ 2
  have hBB : Fintype (B F c) := by
    exact Set.fintypeRange fun y ↦ c - y ^ 2
  have : (Set.toFinset (A F) ∩ Set.toFinset (B F c)).card ≥ 1 := by
    have h : (Set.toFinset (A F) ∩ Set.toFinset (B F c)).card +(Set.toFinset (A F) ∪ Set.toFinset (B F c)).card =
        Nat.card (A F) + Nat.card (B F c) :=  by
      rw[Nat.card_eq_card_toFinset (A F), Nat.card_eq_card_toFinset (B F c)]
      exact Finset.card_inter_add_card_union (Set.toFinset (A F)) (Set.toFinset (B F c))
    have h' : Nat.card ((A F ∩ B F c):Set F) + Nat.card (((A F) ∪ (B F c)):Set F) =  Nat.card (A F) + Nat.card (B F c) := by
      rw [← h]
      rw [← Set.toFinset_union,  ← Set.toFinset_inter, Set.toFinset_card, Set.toFinset_card]
      rw[Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
    rw[hA, hB] at h
    ring_nf at h
    have h_union : (Set.toFinset (A F) ∪ Set.toFinset (B F c)).card ≤ Nat.card ( F) := by
      have : Nat.card (((A F) ∪ (B F c)):Set F)  ≤ Nat.card F := by
        exact Finite.card_subtype_le fun x ↦ x ∈ A F ∪ B F c
      rw [← Set.toFinset_union, Set.toFinset_card]
      rw[← Nat.card_eq_fintype_card]
      exact this
    replace h :  (Set.toFinset (A F) ∩ Set.toFinset (B F c)).card =  (1 + Nat.card F) / 2 * 2  - ((A F).toFinset ∪ (B F c).toFinset).card := by
      exact Nat.eq_sub_of_add_eq h
    rw[h]
    refine Nat.le_sub_of_add_le ?h
    have : (1 + Nat.card F) / 2 * 2 = 1 + Nat.card F := by
      refine Nat.div_two_mul_two_of_even ?_
      sorry
    rw[this ]
    exact Nat.add_le_add_left h_union 1
  have : 0 < ((A F).toFinset ∩ (B F c).toFinset).card  := by
    exact this
  rw[Finset.card_pos] at this
  have : ((A F)∩ (B F c)).Nonempty := by
    rw[← Set.toFinset_inter] at this
    exact Set.toFinset_nonempty.mp this
  rw [Set.inter_nonempty] at this
  obtain ⟨a, ha⟩ := this
  obtain ⟨d, hc⟩ := ha.1
  obtain ⟨b, hb⟩ := ha.2
  use d
  use b
  rw[hc,hb]


/-Coertion de la matrice A inversible vers A element de D F inversible-/
instance coe_invertible (F : Type*)  [Field F ] [Fintype F ] [DecidableEq F]  (A : D F) [ Invertible A.val] : Invertible A :=
{
  invOf := ⟨⅟A, by
    have h := A.prop
    have h1 : Invertible (A.val).det := by
      exact (A.val).detInvertibleOfInvertible

    have : ⅟A.val = ⅟((A.val).det) • (A.val.adjugate)  := by
      exact Matrix.invOf_eq A.val
    rw[this]
    rw[Matrix.adjugate_fin_two]

    constructor
    change ⅟((A.val).det) * A.val 1 1 = ⅟((A.val).det) * A.val 0 0
    rw[h.1]
    change ⅟((A.val).det) *  (- (A.val 1 0)) =  - (⅟((A.val).det) * (- (A.val 0 1)))
    rw[h.2, neg_neg, ← neg_mul,neg_mul_neg]

    ⟩,
  invOf_mul_self := by
    have : ⅟A.val * A = 1 := by
      exact invOf_mul_self A.val

    sorry
  mul_invOf_self := by
    sorry
}

/-Je montre la surjectivité de det dans Fˣ -/
theorem q_surj (F : Type*) [Field F ] [Fintype F ][DecidableEq F]  (hF : ringChar F ≠ 2) :
    Function.Surjective (q : (D F)ˣ →* Fˣ) := by
  intro c
  have h := antecedent_det F hF c
  obtain ⟨ a, b , h ⟩  :=  h
  replace h : a^2 + b^2 = c.val := by
    rw [h]
    ring
  set A : D F := ⟨!![a, -b; b, a], ⟨rfl, by change b = - - b; rw[neg_neg] ⟩⟩
  have : Invertible A := by
    have : Invertible A.val := by
      have : Invertible (A.val).det := by
        simp only [Matrix.det_fin_two]
        change Invertible (a * a - (-b) * b)
        ring_nf
        rw[h]
        exact c.invertible
      apply Matrix.invertibleOfDetInvertible
    exact coe_invertible F A
  set B : (D F)ˣ := unitOfInvertible A
  use B
  rw[q]
  dsimp
  refine Units.eq_iff.mp ?h.a
  change Matrix.det (A.val) = c.val
  simp only [Matrix.det_fin_two]
  change a * a - (-b) * b = c.val
  ring_nf
  exact h

/-SO2 est le noyau du déterminant comme vu dans la première définition-/
def SO2  (F : Type*) [Field F ] [Fintype F ][DecidableEq F] := MonoidHom.ker (q : (D F)ˣ →* Fˣ)

open Polynomial

--Je montre que le cardinal de Fˣ est égal au cardinal de F moins 1
theorem card_field_inv (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Nat.card (Fˣ) = Nat.card (F) -1 := by
  have hF : Fˣ ≃ {x : F // x ≠ 0} := by
    exact unitsEquivNeZero
  have Nat_card_Fx : Nat.card (Fˣ) = Nat.card ({x : F // x ≠ 0}) := by
    exact Nat.card_congr hF
  rw[Nat_card_Fx]
  rw [← Fintype.card_eq_nat_card, Fintype.card_subtype_compl,← Fintype.card_eq_nat_card]
  have : Fintype.card { x // x = 0 } = 1 := by
    exact rfl
  rw[← this]
  rfl


--Je montre que le cardinal de SO2 est égal au cardinal de E divisé par le cardinal de F moins 1
theorem card_So2 (F : Type*) [Field F ] [hFin : Fintype F ][hDec : DecidableEq F] [Nonempty F]  (hF : ringChar F ≠ 2) :
    Nat.card (SO2 F) = Nat.card ((F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ) / (Nat.card (F) -1) := by
  have : (D F)ˣ  ≃* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ := D_star_iso_E_star F
  have : Nat.card ((D F)ˣ)  = Nat.card ((F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ) := by
    refine Nat.card_congr ?f
    exact this.toEquiv
  rw[← this]
  have : Nat.card (Fˣ) = Nat.card (F) -1 := card_field_inv F
  rw[← this]
  change   Nat.card  (MonoidHom.ker (q : (D F)ˣ →* Fˣ)) = Nat.card (D F)ˣ / Nat.card Fˣ
  have :  (D F)ˣ ⧸ (MonoidHom.ker (q : (D F)ˣ →* Fˣ))  ≃* MonoidHom.range (q : (D F)ˣ →* Fˣ) := by
    exact QuotientGroup.quotientKerEquivRange q
  have h : Nat.card ((D F)ˣ)  = Nat.card (MonoidHom.range (q : (D F)ˣ →* Fˣ))  * Nat.card (MonoidHom.ker (q : (D F)ˣ →* Fˣ)):= by
    have h : Nat.card ( (D F)ˣ ⧸ (MonoidHom.ker (q : (D F)ˣ →* Fˣ))) = Nat.card (MonoidHom.range (q : (D F)ˣ →* Fˣ)):= by
      refine Nat.card_congr ?g
      exact this.toEquiv
    have :Nat.card ( (D F)ˣ ⧸ (MonoidHom.ker (q : (D F)ˣ →* Fˣ))) * Nat.card (MonoidHom.ker (q : (D F)ˣ →* Fˣ)) = Nat.card ((D F)ˣ)  := by
      exact Eq.symm (Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker)
    rw [← this, h ]
  have : MonoidHom.range (q : (D F)ˣ →* Fˣ) ≃ Fˣ := by
    have : Function.Surjective (q : (D F)ˣ →* Fˣ) := q_surj F hF
    exact Equiv.subtypeUnivEquiv this
  have : Nat.card (MonoidHom.range (q : (D F)ˣ →* Fˣ)) = Nat.card (Fˣ) := Eq.symm (Nat.card_congr (id this.symm))
  rw[← this]
  refine Nat.eq_div_of_mul_eq_right ?hc (id (Eq.symm h))
  rw[this]
  refine Nat.card_ne_zero.mpr ?hc.a
  constructor
  · exact instNonemptyOfInhabited
  · exact instFiniteUnits





noncomputable def q' (F : Type*) [Field F ] [Fintype F ][DecidableEq F] := Nat.card F

def quo_fint (F : Type*) [Field F ] [Fintype F ][DecidableEq F] : Fintype (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
  exact Fintype.ofEquiv (F × F) (desc_E' F)

-- Je montre que le cardinal des inversibles de E est  le cardinal de F au carré moins 1 lorsque -1 n'est pas un carré dans F
-- Je suis très confus de pourquoi je n'arrive pas à montrer ce résultat car hF est le résultat



set_option maxHeartbeats 300000
theorem cardE_Xsq_irr (F : Type*) [Field F ] [Fintype F ][DecidableEq F](h_sq : Irreducible (X^2+1:F[X])) :
    Nat.card ((F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ) = (q' F)^2 -1 := by
  have : Ideal.IsMaximal (Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
    exact PrincipalIdealRing.isMaximal_of_irreducible h_sq
  have hField : IsField (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient (Ideal.span {X ^ 2 + 1})).mp this
  have hField' : Field (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) :=  by
    exact Ideal.Quotient.field (Ideal.span {X ^ 2 + 1})
  have hDec : DecidableEq (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
    exact Classical.typeDecidableEq (F[X] ⧸ Ideal.span {X ^ 2 + 1})
  have hFin : Fintype (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
    exact Fintype.ofEquiv (F × F) (desc_E' F)

  have : Nat.card (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) = q' F ^2 := by
    have : F × F ≃ (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := desc_E' F
    have h : Nat.card (F × F) = Nat.card  F * Nat.card  F := by
      exact Nat.card_prod F F
    have : Nat.card (F × F) = Nat.card (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
      exact Nat.card_congr this
    rw[← this, h]
    exact Eq.symm (Nat.pow_two (q' F))

  have hF : Nat.card (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ =
      Nat.card (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) - 1 :=
    card_field_inv ((F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])))
  rw [this] at hF

  exact hF
  sorry

-- Je montre que le cardinal des inversibles de E est  le cardinal de (F au moins 1) au carré lorsque -1 est un carré dans F
-- A nouveau j'ai le meme problème qui viens de card_field_inv je crois
theorem cardE_Xsq_red (F:Type*) [Field F ] [Fintype F ][DecidableEq F]  (hF : ringChar F ≠ 2) (h_sq : (∃ i: F, X^2 +1 = (X - C i)*(X+ C i))) :
    Nat.card ((F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ) = ((q' F)-1)^2 := by
  obtain ⟨i, hi⟩ := h_sq

  have : (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) ≃+* (F[X] ⧸ Ideal.span ({X - C i } : Set F[X])) ×  (F[X] ⧸ Ideal.span ({X+ C i} : Set F[X])) := by
    rw[hi ]
    have : Ideal.span ({(X - C i )*  (X+C i)} : Set F[X]) = Ideal.span ({X - C i } : Set F[X]) * Ideal.span ({X + C i} : Set F[X]) := by
      exact Eq.symm (Ideal.span_singleton_mul_span_singleton (X - C i) (X + C i))
    rw[this]
    have coprime : IsCoprime (Ideal.span {X - C i}) (Ideal.span {X + C i})  := by
      sorry

    exact (Ideal.span {X - C i}).quotientMulEquivQuotientProd (Ideal.span {X + C i}) coprime
  have : ((F[X] ⧸ Ideal.span {X - C i}) × F[X] ⧸ Ideal.span {X + C i})ˣ ≃* (F[X] ⧸Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ := by
    refine Units.mapEquiv ?h
    exact this.toMulEquiv.symm
  have : Nat.card (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ  = Nat.card ((F[X] ⧸ Ideal.span ({X - C i} : Set F[X])) × (F[X] ⧸ Ideal.span ({X + C i} : Set F[X])))ˣ  := by
    exact Nat.card_congr this.toEquiv.symm
  rw[this]
  have :  Nat.card (F[X] ⧸ Ideal.span ({X - C i}: Set F[X]))ˣ = q' F - 1 := by

    haveI : Field (F[X] ⧸ Ideal.span ({X - C i}: Set F[X])) := by
      have : Irreducible (X - C i) := by
        exact irreducible_X_sub_C i
      have : Ideal.IsMaximal ( Ideal.span ({X - C i}: Set F[X])) := by
        exact PrincipalIdealRing.isMaximal_of_irreducible this
      exact Ideal.Quotient.field (Ideal.span {X - C i})
    haveI : Fintype  (F[X] ⧸ Ideal.span ({X - C i}: Set F[X])) := by
      exact Fintype.ofEquiv (F ) (desc_F_quo_deg_1 F ( i))
    haveI : DecidableEq (F[X] ⧸ Ideal.span ({X - C i}: Set F[X])) := by
      exact Classical.typeDecidableEq (F[X] ⧸ Ideal.span {X - C i})


    have := card_field_inv (F[X] ⧸ Ideal.span ({X - C i}: Set F[X]))
    rw[this]
  sorry

--Un corps fini (de caractéristique différente de 2) a au moins deux éléments
theorem card_F_ge_two (F : Type*) [Field F ] [Fintype F ][DecidableEq F] [Nonempty F] (hF : ringChar F ≠ 2) : Nat.card F > 1 := by
  have h := Fintype.card_pos_iff.mpr (by infer_instance : Nonempty F)
  sorry


/-Cardinal de SO2 dans le cas -1 non carré-/
theorem card_So2_Xsq_irr  (F : Type*) [Field F ] [Fintype F ][DecidableEq F](h_sq : Irreducible (X^2+1:F[X])) (hF : ringChar F ≠ 2)   :
    Nat.card (SO2 F) = (q' F) +1 := by
  have h := cardE_Xsq_irr F h_sq
  have h' := card_So2 F hF
  rw[h',h]
  change (q' F ^ 2 - 1^2) / (q' F - 1) = q' F + 1
  rw[Nat.sq_sub_sq]
  refine Nat.div_eq_of_eq_mul_left ?H1 rfl
  refine Nat.zero_lt_sub_of_lt ?H1.h
  exact card_F_ge_two F hF

/-cardinal de SO si -1 est carré-/
theorem card_So2_Xsq_red  (F : Type*) [Field F ] [Fintype F ][DecidableEq F] (h_sq : (∃ i: F, X^2 +1 = (X - C i)*(X+ C i))) (hF : ringChar F ≠ 2)   : Nat.card (SO2 F) = (q' F) - 1 := by
  have h := cardE_Xsq_red F hF h_sq
  have h' := card_So2 F hF
  rw[h',h]
  change ((q' F - 1)^2) / (q' F - 1) = q' F - 1
  refine Nat.div_eq_of_eq_mul_right ?H1 ?H2
  refine Nat.zero_lt_sub_of_lt ?H1.h
  exact card_F_ge_two F hF
  ring

theorem invertibles_of_field_is_cyclic (F : Type*) [Field F ] [Fintype F ][DecidableEq F] : IsCyclic (Fˣ) := by
  exact instIsCyclicUnitsOfFinite

-- Here I show cyclicity of SO2 when -1 is not a square in F,
-- I instance IsCylcic (Fˣ) but lean fails to see it as an instance
theorem So2_cyclic0 (F : Type*) [Field F ] [Fintype F ][DecidableEq F] [Nonempty F] (hF : ringChar F ≠ 2) (h_sq : Irreducible (X^2+1:F[X])):
    IsCyclic (SO2 F) := by
  have hField : IsField (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient (Ideal.span {X ^ 2 + 1})).mp (PrincipalIdealRing.isMaximal_of_irreducible h_sq)
  have : (D F)  ≃* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := D_iso_E F
  have : IsField (D F):= by
    exact MulEquiv.isField (F[X] ⧸ Ideal.span {X ^ 2 + 1}) hField this
  haveI : Field (D F) := by
    exact this.toField
  have : F × F ≃ D F := by
    have := desc_E' F
    have h := (D_iso_E F).toEquiv
    exact (h.trans (id this.symm)).symm
  haveI : Fintype (D F) := by
    exact Fintype.ofEquiv (F × F) this
  haveI : DecidableEq (D F) := by
    exact Classical.typeDecidableEq (D F)

  haveI : IsCyclic (D F)ˣ := by
    exact instIsCyclicUnitsOfFinite

  exact Subgroup.isCyclic (SO2 F)

noncomputable def So2_iso (F : Type*) [Field F ] [Fintype F ][DecidableEq F] [Nonempty F] (hF : ringChar F ≠ 2) (h_sq : Irreducible (X^2+1:F[X])) : SO2 F ≃* ZMod (q' F +1) := by
  have hcard :  Nat.card (SO2 F) = (q' F) +1 := card_So2_Xsq_irr F h_sq hF
  have hcycle := So2_cyclic0 F hF h_sq
  have :   ∃ g: SO2 F, ∀ (x : SO2 F), x ∈ Subgroup.zpowers g := IsCyclic.exists_zpow_surjective
  --obtain ⟨g, hg⟩ := this
  sorry
