import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
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

section char_sg_2



variable {F : Type*} [Field F]
variable [Fintype F]

def C (F : Type*) [Field F] := {A : Matrix (Fin 2) (Fin 2) F // A 0 0 = A 1 1 ∧ A 1 0 = -A 0 1}

instance [Field F] : Zero (C F) :=
  ⟨⟨0, by
    simp [Matrix.zero_apply]⟩⟩

instance [Field F] : One (C F) :=
  ⟨⟨1, by
    simp [Matrix.one_apply]⟩⟩

instance [Field F] : Add (C F) :=
  ⟨fun A B => ⟨A.val + B.val, by
    simp [Matrix.add_apply, A.property.1, A.property.2, B.property.1, B.property.2]
    ring⟩⟩

instance [Field F] : Neg (C F) :=
  ⟨fun A => ⟨-A.val, by
    simp [Matrix.neg_apply, A.property.1, A.property.2]⟩⟩

instance [Field F] : Mul (C F) :=
  ⟨fun A B => ⟨A.val * B.val, by
    simp [Matrix.mul_apply, A.property.1, A.property.2, B.property.1, B.property.2]
    ring⟩⟩


@[ext] lemma C.ext {A B : C F} (h : A.val = B.val) : A = B :=
  Subtype.ext h

```
instance [Field F] : Ring (C F) where
  zero := 0
  one := 1
  add := (+)
  neg := Neg.neg
  mul := (*)
  nsmul := fun n x => ⟨n • x.val, by
    induction n with
    | zero => simp
    | succ n ih => simp [Nat.succ_eq_add_one, ih, Matrix.add_smul]⟩
  zsmul := fun n x => ⟨n • x.val, by
    induction n with
    | ofNat n => simp [nsmul, Matrix.add_smul]
    | negSucc n => simp [Matrix.neg_smul, nsmul]⟩
  add_assoc := by
    intros a b c
    apply C.ext
    simp [Matrix.add_assoc]
  zero_add := by
    intros a
    apply C.ext
    simp [Matrix.zero_add]
  add_zero := by
    intros a
    apply C.ext
    simp [Matrix.add_zero]
  add_left_neg := by
    intros a
    apply C.ext
    simp [Matrix.add_left_neg]
  add_comm := by
    intros a b
    apply C.ext
    simp [Matrix.add_comm]
  mul_assoc := by
    intros a b c
    apply C.ext
    simp [Matrix.mul_assoc]
  one_mul := by
    intros a
    apply C.ext
    simp [Matrix.one_mul]
  mul_one := by
    intros a
    apply C.ext
    simp [Matrix.mul_one]
  left_distrib := by
    intros a b c
    apply C.ext
    simp [Matrix.left_distrib]
  right_distrib := by
    intros a b c
    apply C.ext
    simp [Matrix.right_distrib]
