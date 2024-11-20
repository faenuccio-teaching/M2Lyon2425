/-
J'ai commencé mon projet, sur la description de SO_2(F_q)
Pour l'instant j'ai montré que c'est un groupe, et je suis pas loin d'avoir son cardinal lorsque q est une puissance de 2

Pour q non puissance de 2 je suis la preuve faite dans le nouvelles histoires hédonistes  de groupes et géométrie tome 2 de Calderos, p 53
En passant par F_q[X/X^2+1],  mais cela me semble un peu compliqué
Pour l'instant j'essaie de finir la charactéristique 2 et j'avise. -/



import Mathlib


namespace Matrix

universe u v

open Matrix

open LinearMap

section

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]


def SpecialOrthogonalGroup :=
  { A : Matrix n n R // A.det = 1 ∧ A*A.transpose= 1 }

end

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

theorem row_ne_zero [Nontrivial R] (g : SpecialOrthogonalGroup n R) (i : n) : ↑ₘg i ≠ 0 := fun h =>
  g.det_ne_zero <| det_eq_zero_of_row_eq_zero i <| by simp [h]

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



theorem SO2_inv_co (A : SO(2, R)) : A.1 1 0 = -A.1 0 1 ∧ A.1 0 0 = A.1 1 1 ∧ (A.1 0 0)^2 + (A.1 1 0)^2 = 1  := by
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

def f (A:SO(2,F)) := A.1 0 0

variable {F_2 : Type*} [Field F_2][Fintype F_2][CharP F_2 2]

theorem card_so2_char2 (h : ringChar F_2 = 2) : (Nat.card SO(2,F_2) = Nat.card F_2) := by
have q := Nat.card F_2
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
  have  : A.1 1 0^2  =(frobenius F_2 2) (A.1 1 0)  := by
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
  have  : B.1 1 0^2  =(frobenius F_2 2) (B.1 1 0)  := by
    rfl
  rw[this] at h1B
  have h11 := h
  rw[ha.right.left, hb.right.left] at h11
  rw[← h ] at h1B
  rw[← h1B] at h1A

  have h10 : A.1 1 0 = B.1 1 0 := by
    apply injective_frobenius F_2 2
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
  have b:= bijective_frobenius F_2 2
  have c := b.right
  specialize c (-a^2+1)
  have a0  := c.choose_spec
  have b0 := c.choose






  sorry



















def sphere := { (a, b) : ℕ ×  ℕ | a * b = 12 }

def caree := { (a, b) : F × F | a^2+ b^2 =1 }






noncomputable def iso_so2 : SO(2,F) ≃* caree := by
sorry


theorem desc_so_char2 (h : ringChar F = 2) : (SO(2,F) ≃* F) := by

    sorry




theorem bij  (h : ringChar F = 2) (f) : Function.bijective f


sorry
