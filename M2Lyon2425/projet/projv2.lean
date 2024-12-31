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

-- Prove that D F is a subring of Matrix (Fin 2) (Fin 2) F

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

-- Define coercion from D to Matrix (Fin 2) (Fin 2) F
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

#check (E F)


/- This is proven in mathlib. -/
variable {R : Type*} [CommRing R]

instance commRing (I : Ideal R) : CommRing (R ⧸ I) where
  __ : AddCommGroup (R ⧸ I) := inferInstance
  __ : CommRing (Quotient.ringCon I).Quotient := inferInstance

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

-- Define the projection map from F[X] to E
noncomputable def proj_FX_to_E (F : Type*) [Field F] :
    F[X] →+* (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) :=
  Ideal.Quotient.mk (Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))

#check proj_FX_to_E

@[simp]
theorem proj_FX_to_E_Xsquare_eq_moins1 (F : Type*) [Field F] : proj_FX_to_E F (X^2) = -1 := by
  apply Ideal.Quotient.eq.2
  rw [sub_neg_eq_add]
  exact Ideal.subset_span (Set.mem_singleton _)

@[simp]
theorem proj_FX_to_quotient_Xsquare_eq_moins1 (F : Type*) [Field F] : (Ideal.Quotient.mk (span {(X:F[X]) ^ 2 + 1}) (X^2)) = -1 := by
  apply Ideal.Quotient.eq.2
  rw [sub_neg_eq_add]
  exact Ideal.subset_span (Set.mem_singleton _)

@[simp]
theorem deg_Xsquare_plus1 : ((X:F[X])^2 + 1).degree = 2 := by
  rw [degree_add_eq_left_of_degree_lt]
  rw [degree_X_pow]
  simp
  rw[degree_X_pow]
  simp

theorem deg_a_plusbX_le_one (a b : F) : (C a + C b * X).degree ≤ 1 := by
  refine ((C a + C b * X).degree_le_iff_coeff_zero 1).2 (fun m hm ↦ ?_)
  replace hm := Nat.one_lt_cast.1 hm
  have : b * X.coeff m = 0 := by
    refine mul_eq_zero.2 ?_
    right
    exact Polynomial.coeff_X_of_ne_one (ne_of_lt (Nat.one_lt_cast.1 hm)).symm
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_add, this, coeff_C_ne_zero (Nat.not_eq_zero_of_lt hm), zero_add]

theorem deg_c (c : F[X]) (hc : 2 + c.degree ≤ 1) : c.degree = ⊥ := by
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

--def pi : F × F  → (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) :=
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
      sorry
    change proj_FX_to_E F (C (g.coeff 0) + C (g.coeff 1) * X) = f
    rw [← this, hg.2]
    exact Quotient.out_eq' f


-- Compose p' with the projection map
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
  rw [g'.degree_le_iff_coeff_zero 1] at hg1
  set a := g'.coeff 0
  set b := g'.coeff 1
  have : g' = C a + C b * X := by
    rw[Polynomial.ext_iff]
    intro i
    if hi : i = 0 then
      rw[hi]
      change g'.coeff 0 = (C (g'.coeff 0) + C b * X).coeff 0
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
    rw[hg1]
    have hiiii : (1=i)=False := by
      exact eq_false fun a ↦ hii (id (Eq.symm a))

    simp only [hiiii]
    ring_nf
    exact Nat.one_lt_cast.mpr hiii
  set A : Matrix (Fin 2) (Fin 2) F := !![a, -b; b, a]
  set B : D F := ⟨ A , {
    left := by rfl
    right := by change b = - - b
                rw [neg_neg]
            }  ⟩
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

variable { p : Nat  }[Fact (Nat.Prime p)][hp3 : Fact (p ≥ 3)]

variable [Fintype F][hF : Fact (ringChar F ≠ 2)]



def A   (F : Type*) [Field F ] [Fintype F ] := {a : F | ∃ b : F, b^2 = a}
def B  (F : Type*) [Field F ] [Fintype F ]  c := {a : F | ∃ d : F, (c - d^2) = a}



theorem number_of_squares (F : Type*) [Field F ] [Fintype F ] (hF : ringChar F ≠ 2)  : Nat.card (A F) = (Nat.card F +1)/2 := by
   sorry
theorem number_of_squares' (F : Type*) [Field F ] [Fintype F ] (hF : ringChar F ≠ 2) c : Nat.card (B F c) = (Nat.card F +1)/2 := by
   sorry

theorem antecedent_det (F : Type*) [Field F ] [Fintype F ] [DecidableEq F] (hF : ringChar F ≠ 2) c : (∃ a b : F , a^2 = c - b^2 ) := by
  have hA := number_of_squares F hF
  have hB := number_of_squares' F hF c
  have hAA : Fintype (A F) := by
    exact Set.fintypeRange fun y ↦ y ^ 2
  have hBB : Fintype (B F c) := by
    exact Set.fintypeRange fun y ↦ c - y ^ 2

  have : (Set.toFinset (A F) ∩ Set.toFinset (B F c)).card ≥ 1 := by
    have h : (Set.toFinset (A F) ∩ Set.toFinset (B F c)).card +(Set.toFinset (A F) ∪ Set.toFinset (B F c)).card = Nat.card (A F) + Nat.card (B F c) :=  by
      rw[Nat.card_eq_card_toFinset (A F), Nat.card_eq_card_toFinset (B F c)]
      exact Finset.card_inter_add_card_union (Set.toFinset (A F)) (Set.toFinset (B F c))
    rw[hA, hB] at h
    ring_nf at h

    sorry


  sorry


instance coe_invertible (F : Type*)  [Field F ] [Fintype F ] [DecidableEq F]  (A : D F) [ Invertible A.val] : Invertible A :=
{
  invOf := ⟨⅟A, by

    have h := Matrix.mul_adjugate A.val
    have h1 : Invertible (A.val).det := by
      exact (A.val).detInvertibleOfInvertible
    have h2 : A.val * (A.val.adjugate) * (⅟((A.val).det)• 1) = 1 := by
      rw[h]
      rw[smul_mul_assoc, mul_smul_comm]
      rw[smul_smul]
      rw[mul_invOf_self]
      rw[one_smul, one_mul]

    sorry



  ⟩,
  invOf_mul_self := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.invOf_apply, Matrix.invOf_mul_self, A.property.1, A.property.2]

  mul_invOf_self := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.invOf_apply, Matrix.invOf_mul_self, A.property.1, A.property.2]
}




theorem q_surj (F : Type*) [Field F ] [Fintype F ][DecidableEq F]  (hF : ringChar F ≠ 2) : Function.Surjective (q : (D F)ˣ →* Fˣ) := by
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

  have A_unit : (D F)ˣ := ⟨A, ⟨A^-1, by , by simp⟩, by simp, by simp⟩


  sorry

def SO2  (F : Type*) [Field F ] [Fintype F ][DecidableEq F] := MonoidHom.ker (q : (D F)ˣ →* Fˣ)

open Polynomial

theorem card_field_inv (F : Type*) [Field F ] [Fintype F ][DecidableEq F]  : Nat.card (Fˣ) = Nat.card (F) -1 := by
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



theorem card_So2 (F : Type*) [Field F ] [Fintype F ][DecidableEq F] [Nonempty F]  (hF : ringChar F ≠ 2) : Nat.card (SO2 F) = Nat.card ((F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ) / (Nat.card (F) -1) := by
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

theorem formE_Xsq_irr (F : Type*) [Field F ] [Fintype F ][DecidableEq F](h_sq : Irreducible (X^2+1:F[X])) : Nat.card ((F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X]))ˣ) = (q' F)^2 -1 := by
  have : Ideal.IsMaximal (Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
    exact PrincipalIdealRing.isMaximal_of_irreducible h_sq
  have : IsField (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient (Ideal.span {X ^ 2 + 1})).mp this
  let q := q' F

  have : Nat.card (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) = q^2 := by
    have : F × F ≃ (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := desc_E' F
    have h : Nat.card (F × F) = Nat.card  F * Nat.card  F := by
      exact Nat.card_prod F F
    have : Nat.card (F × F) = Nat.card (F[X] ⧸ Ideal.span ({Polynomial.X^2 + 1} : Set F[X])) := by
      exact Nat.card_congr this
    rw[← this, h]
    exact Eq.symm (Nat.pow_two q)
  change  Nat.card (F[X] ⧸ Ideal.span {X ^ 2 + 1})ˣ = q ^ 2 - 1
  apply?
