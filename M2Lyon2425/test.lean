import Mathlib

variable (d:ℤ)




/--Projet LEAN :

1) Définir l'anneau Z[sqrt(d)] avec ses opérations
2) Montrer que Z[sqrt(d)] est un anneau commutatif
3) Pour quels d (d<0) est-ce que Z[sqrt(d)] est euclidien ?

-/







--Etape 1 : On définit l'anneau Z[sqrt(d)] avec ses opérations

@[ext]
structure MonAnneau (d : ℤ) where
  re : ℤ
  im : ℤ

instance : Zero (MonAnneau d) :=
  ⟨ ⟨ 0,0 ⟩ ⟩

instance : One (MonAnneau d) :=
  ⟨ ⟨ 1, 0⟩ ⟩

instance : Add (MonAnneau d) :=
  ⟨ fun x y ↦ ⟨ x.re + y.re, x.im + y.im⟩ ⟩

instance : Neg (MonAnneau d) :=
  ⟨ fun x ↦ ⟨ -x.re, -x.im⟩ ⟩

instance : Mul (MonAnneau d) where
  mul := fun x y ↦  ⟨ x.re * y.re - d* x.im * y.im, x.re * y.im + x.im * y.re⟩





--defs

theorem zero_def : (0 : (MonAnneau d)) = ⟨0, 0⟩  :=
  rfl
theorem one_def : (1 : (MonAnneau d)) = ⟨1, 0⟩  :=
  rfl
theorem add_def (x y : (MonAnneau d)) : x + y = ⟨ x.re + y.re, x.im + y.im⟩  :=
  rfl
theorem neg_def (x : (MonAnneau d)) : -x = ⟨ -x.re, -x.im ⟩  :=
  rfl
theorem mul_def (x y : (MonAnneau d)) :
  x * y = ⟨ x.re * y.re - d * x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl







-- Etape 2 : On montre que Z[sqrt(d)] est un anneau commutatif


@[simp]
theorem zero_re : (0 : (MonAnneau d)).re = 0 := by
  rfl
@[simp]
theorem zero_im : (0 : (MonAnneau d)).im = 0 := by
  rfl
@[simp]
theorem one_re : (1 : (MonAnneau d)).re = 1 := by
  rfl
@[simp]
theorem one_im : (1 : (MonAnneau d)).im = 0 := by
  rfl
@[simp]
theorem add_re (x y : (MonAnneau d)) : (x + y).re = x.re + y.re := by
  rfl
@[simp]
theorem add_im (x y : (MonAnneau d)) : (x + y).im = x.im + y.im := by
  rfl
@[simp]
theorem neg_re (x : (MonAnneau d)) : (-x).re = -x.re := by
  rfl
@[simp]
theorem neg_im (x : (MonAnneau d)) : (-x).im = -x.im := by
  rfl
@[simp]
theorem mul_re (x y : (MonAnneau d)) : (x * y).re = x.re * y.re - d*x.im * y.im := by
  rw[mul_def]
@[simp]
theorem mul_im (x y : (MonAnneau d)) : (x * y).im = x.re * y.im + x.im * y.re := by
  rfl


instance instCommRing_MonAnneau : CommRing (MonAnneau d) where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro a b c
    ext
    · rw[add_re]
      rw[add_re]
      rw[add_re]
      rw[add_re]
      ring
    · rw[add_im]
      rw[add_im]
      rw[add_im]
      rw[add_im]
      ring
  zero_add := by
    intro a
    ext
    · rw[add_re]
      rw[zero_re]
      rw[zero_add]
    · rw[add_im]
      rw[zero_im]
      rw[zero_add]
  add_zero := by
    intro a
    ext
    · rw[add_re]
      rw[zero_re]
      rw[add_zero]
    · rw[add_im]
      rw[zero_im]
      rw[add_zero]
  neg_add_cancel := by
    intro a
    ext
    · simp only [add_re]
      simp only [neg_re]
      simp only [neg_add_cancel]
      rw[zero_re]
    · simp only [add_im]
      simp only [neg_im]
      simp only [neg_add_cancel]
      rw[zero_im]
  add_comm := by
    intro a b
    ext
    · rw[add_re]
      rw[add_re]
      ring
    · rw[add_im]
      rw[add_im]
      ring
  mul_assoc := by
    intro a b c
    ext
    · simp
      ring
    · simp
      ring
  one_mul := by
    intro a
    ext
    · simp
      --simp only [mul_re, one_re, one_mul, one_im, mul_zero, zero_mul, sub_zero]
    · simp
      --simp only [mul_im, one_re, one_mul, one_im, zero_mul, add_zero]
  mul_one := by
    intro a
    ext
    · simp
--      simp only [mul_re, one_re, mul_one, one_im, mul_zero, sub_zero]
    · simp
--      simp only [mul_im, one_im, mul_zero, one_re, mul_one, zero_add]
  left_distrib := by
    intro a b c
    ext
    · simp
      ring
      --simp only [mul_re, add_re, add_im]
    · simp
      ring
--      simp only [mul_im, add_im, add_re]
  right_distrib := by
    intro a b c
    ext
    · rw[mul_re]
      rw[add_re]
      rw[add_im]
      simp
      ring
    · rw[mul_im]
      rw[add_re]
      rw [add_im]
      simp
      ring
  mul_comm := by
    intro a b
    ext
    · simp
      ring
    · simp
      ring
  zero_mul := by
    intro a
    ext
    · simp
    · simp
/--
      rw[mul_re]
      rw[zero_re]
      rw[zero_mul]
      rw[zero_im]
      rw[mul_zero]
      rw[sub_self]


      rw[mul_im]
      rw[zero_re]
      rw[zero_mul]
      rw[zero_im]
      rw[add_zero]
-/
  mul_zero:=by
    intro a
    ext
    · simp
    · simp
