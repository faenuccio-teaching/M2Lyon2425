/-
J'ai commencé mon projet, sur la description de SO_2(F_q)
Pour l'instant j'ai montré que c'est un groupe,
Pour q= 2^n, j'ai le cardinal de So2 et que les elements sont d'ordre au plus 2,
Je voudrais bien dire que le groupe est isomorphe à (Z/2Z)^n
Pour q non puissance de 2 je suis la preuve faite dans le nouvelles histoires hédonistes  de groupes et géométrie tome 2 de Calderos, p 53
En passant par F_q[X]/X^2+1,  mais cela me semble un peu compliqué
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







/-theorem is_So2 (A:(Matrix (Fin 2) (Fin 2) F)) (hA : A 1 0 = -A 0 1 ∧ A 0 0 = A 1 1 ∧ (A 0 0)^2 + (A 1 0)^2 = 1 )
  : ( A∈ SO(2,F).val ) := by-/


-- Part on char 2

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


variable {F_2n : Type*} [Field F_2n][Fintype F_2n][char2 :CharP F_2n 2]

noncomputable def m := Nat.card F_2n

theorem auto_inv_char2'  (A : SO(2, F_2n)) : A= (A⁻¹) := by
  have := auto_inv_char2 (char2) (A)
  exact this


instance commGroup : CommGroup (SO(2,F_2n))  where

  mul_comm (a:SO(2,F_2n)) b := by
    rw [ auto_inv_char2' (a*b)]
    simp
    nth_rewrite 2 [auto_inv_char2' b]
    nth_rewrite 2 [auto_inv_char2' a]
    rfl
#check Additive SO(2,F_2n)

-- AddCommGroup.equiv_directSum_zmod_of_fintype (Additive SO(2,F_2n))

theorem card_so2_char2  : (Nat.card SO(2,F_2n) = Nat.card F_2n) := by
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
  have  : A.1 1 0^2  =(frobenius F_2n 2) (A.1 1 0)  := by
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
  have  : B.1 1 0^2  =(frobenius F_2n 2) (B.1 1 0)  := by
    rfl
  rw[this] at h1B
  have h11 := h
  rw[ha.right.left, hb.right.left] at h11
  rw[← h ] at h1B
  rw[← h1B] at h1A

  have h10 : A.1 1 0 = B.1 1 0 := by
    apply injective_frobenius F_2n 2
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
  have b:= bijective_frobenius F_2n 2
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
      change a^2 + (frobenius F_2n 2) b0 = 1
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


theorem structure_char2' : ((SO(2,F_2n)) ≃* ZMod (Nat.card F_2n) ) := by

  sorry


theorem structure_char2 : ((Additive SO(2,F_2n)) ≃+ ZMod (Nat.card F_2n) ) := by
  sorry

end  Char2


def couple := (F × F)
def uni := Set.univ (α:=(F×F))
#check uni


def g ( a : F× F):=  !![a.1, -a.2 ; a.2,a.1]
#check g

def g' := fun ( a : F× F) ↦   Matrix.of (fun (i:Fin 2) ↦ (fun (j : Fin 2) ↦  match i,j with
  |0, 0 => a.1
  |0,1 => -a.2
  |1, 0 => a.2
  |1,1 => a.1
 ))


def C := Set.range (g : F × F → Matrix (Fin 2) (Fin 2) F)
def C' (F : Type*) [Field F] := {A : Matrix (Fin 2) (Fin 2) F // A 0 0 = A 1 1 ∧ A 1 0 = -A 0 1}



#print C
#check C
--def C' := { A  : Matrix (Fin 2) (Fin 2) F // (a,b) ∈  F × F ∧   A = !![a, -b ; b,a] }


theorem injg : (Function.Injective (g : F × F → Matrix (Fin 2) (Fin 2) F) ) := by
  intro a b hab
  ext
  · rw[← Matrix.ext_iff] at hab
    specialize hab 0 0
    exact hab

  · rw[← Matrix.ext_iff] at hab
    specialize hab 1 0
    exact hab


def caree := { (a, b) : F × F | a^2+ b^2 =1 }

open Polynomial


def E := F[X]⧸Ideal.span ({Polynomial.X^2+1}: Set F[X])



instance : Monoid E := by
  refine Function.Injective.monoid (Quotient.mk)


def p' := fun (A : C' F) ↦ C (A.val 0 0) + (C (A.val 0 1) * X) : F[X]

def p := fun ( A : C ) ↦  C.{u_1} ( A.1 0 0 )  + ( ( A.1 0 1 ) * X ) : F[X]

#check E


def det (A:C^x)
/--/
def E':= F[X]⧸ ⟨ X^2+1⟩
noncomputable def P := (@Polynomial.X (R:=F))
def Q := @Polynomial.X (R:=F) + 1

def EE := Ideal ((@Polynomial.X (R:=F)) + 1 )
def J:= E⧸( (@Polynomial.X (R:=F) )^2+1)
#check E






def sphere := { (a, b) : ℕ ×  ℕ | a * b = 12 }







noncomputable def iso_so2 : SO(2,F) ≃* caree := by
sorry


theorem desc_so_char2 (h : ringChar F = 2) : (SO(2,F) ≃* F) := by

    sorry




theorem bij  (h : ringChar F = 2) (f) : Function.bijective f


sorry
