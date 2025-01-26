import Init.Data.List.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.Interval

section AncillarySyntax

open scoped NNReal

/- ## The anonymous variable
(typed `\. = ·` and not `\cdot = ⬝`). -/

def f₁ : ℝ → ℝ≥0 := fun a ↦ ‖ a ‖₊
def f₂ : ℝ → ℝ≥0 := (‖ · ‖₊)

def g₁ : ℕ → ℕ := (· + 1)
def g₂ : ℕ → ℕ := fun x ↦ x + 1
def g₃ : ℕ → ℕ := fun x ↦ Nat.succ x

example : f₁ = f₂ := rfl
example : g₁ = g₂ := rfl
example : g₂ = g₃ := rfl

def L₁ : Type _ → Type _ := (List ·) --
def L₂ : Type* → Type _ := (List ·)
-- def L₃ : Type* → Type* := (List ·)

-- example (X : Type) (v : L₁ X) : X := by
--   let L : L₁ (Type → Type) := sorry


end AncillarySyntax
section FunnyBracket

open Real

-- Some examples of the interest of ⦃
open Function

def f : ℕ → ℕ := (· + 5) -- say something about `⬝`

def myInjective (f : ℕ → ℕ) : Prop :=
  ∀ {a b : ℕ}, f a = f b → a = b

lemma myInjective.comp {f g : ℕ → ℕ} (hf : myInjective f) (hg : myInjective g) :
    myInjective (f ∘ g) := by
  intro a b H
  apply hg
  apply hf
  exact H

lemma Inj_f : f.Injective := by
  intro _ _ h
  rwa [f, f, add_left_inj] at h

lemma myInj_f : myInjective f := by
  intro _ _ h
  rwa [f, f, add_left_inj] at h

lemma Inj_f_comp : Function.Injective (fun n ↦ f (f n)) := by
  -- show Injective (fun n ↦ (f ∘ f) n)
  apply Inj_f.comp
  exact Inj_f

lemma myInj_f_comp : myInjective (fun n ↦ f (f n)) := by
  apply myInj_f.comp
  -- sorry
  -- have := Inj_f
  have := Inj_f
  rw [Injective] at this
  sorry
  -- exact @Inj_f
  -- apply Inj_f


/- The `..` syntax for exact and its interaction with `⦃` (if they're not used there might be
several remaining variables to discharge, albeit perhaps automatically). -/

end FunnyBracket

/- ## Exercice
* Define structures for stations, lines, trips (insisting on connections being reasonable, i.e.
if one changes line there must be a *connection* (a type on its own?)
* Prove the following theorems:
0. Perhaps, do not assume that the graph is path-connected and add the def of a "good trip".
1. If there is a trip from `a` to `b` with `n` changes, there is also a trip from `b` to `a` with
`n` changes
2. If there is a trip from `a` to `b` with `n` changes and one from `b` to `c` with `m` changes, there
is a trip from `a` to `c` with at `n+m` changes.
3. Define the type of trips with at most `n` changes and state the above results here?
4. Define a "circle line" that touches all terminus and prove that, assuming this exists, there is
a trip from `a` to `b` with at most two changes for every `a` and `b` (go to the terminus of a line
through `a`, pick the circle line to a terminus of a line through `b`, use this last line till `b`).


-/

inductive Stations : Type*
  | PartDieu : Stations
  | Perrache : Stations

structure Line where
  stops : List Stations
  not_empty : stops ≠ []
  nodup : stops.Nodup

structure Trip where
  n : ℕ+ -- the number of stops
  select : Fin n → Stations
  inj : select.Injective


-- -- #check Line.notempty
-- def Start (L : Line) : Stations := by
--   exact (L.stops).head (L.not_empty)

-- def End (L : Line) : Stations := by
--   exact (L.stops).length-- (L.not_empty)

-- inductive Terminus (L : Line) : Type*
--   | Start M : Terminus L
--   -- | (stops L).head (not_empty L) : Terminus

namespace LaurentPolynomials

noncomputable section

open Finset Finsupp Classical


def LaurentPol (R : Type*) [CommRing R] := AddMonoidAlgebra R ℤ-- ℤ →₀ R
  -- coeff : ℤ →₀ R

variable  (R : Type*) [CommRing R]

scoped notation:2000 R "{X}" => LaurentPol R

instance (R : Type*) [CommRing R] : CommRing R {X} :=
  inferInstanceAs (CommRing (AddMonoidAlgebra R ℤ))

instance (R : Type*) [CommRing R]: Module R R{X} :=
  inferInstanceAs (Module R (AddMonoidAlgebra R ℤ))

@[class, ext]
structure bddLaurentSubmodule /- (M : Type*) [AddCommGroup M] extends Module R M  -/where
  -- extends Submodule R{X} R{X} where
-- structure bddLaurent (M : Submodule R{X} R{X}) where
  carrier : Set R{X}
  UB : ℤ
  LB : ℤ
  mem_iff : ∀ f : R{X}, f ∈ carrier ↔ (f.support) ⊆ Finset.Icc UB LB

-- export bddLaurentSubmodule (mem_iff)

attribute [simp] bddLaurentSubmodule.mem_iff

-- @[ext]
-- lemma ext (x y : R{X}) (H : ∀ n, x.2 n = y.2 n) : x = y := Finsupp.ext H


-- instance :  CoeSort (bddLaurentSubmodule R) (Type _) := ⟨CoeSort.coe ∘ bddLaurentSubmodule.carrier⟩
instance :  CoeSort (bddLaurentSubmodule R) (Type _) := ⟨fun M ↦ ↥M.carrier⟩

variable (M : bddLaurentSubmodule R)

@[ext]
lemma bddext (M : bddLaurentSubmodule R) (x y : (M : Type _)) (H : ∀ n, x.1.toFun n = y.1.toFun n):
  x = y := by--Finsupp.ext H
  ext
  exact Finsupp.ext H

instance bddLaurentAdd (M : bddLaurentSubmodule R) : Add M where
  add := by
    rintro ⟨x.val, x.prop⟩ ⟨y.val, y.prop⟩
    use x.val + y.val
    rw [bddLaurentSubmodule.mem_iff]
    apply subset_trans (Finsupp.support_add)
    apply Finset.union_subset
    · simpa using x.prop
    · simpa using y.prop

@[simp]
lemma add_apply {M : bddLaurentSubmodule R} (x y : (M : Type _)) (n : ℤ) :
  (x + y).1.toFun n = x.1.toFun n + y.1.toFun n := rfl

@[simp]
instance (M : bddLaurentSubmodule R) : Zero M where
  zero := by
    use 0
    simp only [bddLaurentSubmodule.mem_iff, support_zero, empty_subset]

@[simp]
instance : Neg M where
neg := by
  rintro ⟨a.val, a.prop⟩
  use -a.val
  simp
  rw [support_neg]
  simp at a.prop
  exact a.prop

@[simp]
lemma neg_apply (a : M) (n : ℤ) : (-a.1).toFun n = - (a.1.toFun n) := by rfl


lemma neg_add : ∀ a : M, -a + a = 0 := by
  intro
  ext
  simp
  rfl

lemma add_neg : ∀ a : M, a + - a = 0 := by
  intro
  ext
  simp
  rfl

lemma zero_add : ∀ a : M, 0 + a = a := by
  intro a
  ext
  simp
  rfl

lemma add_zero : ∀ a : M, a + 0 = a := by
    intro
    ext
    simp
    rfl


instance (M : bddLaurentSubmodule R) : SubNegMonoid M where
  add_assoc := by
    intro x y z
    ext n
    exact add_assoc ..
  zero_add := zero_add R M
  add_zero := add_zero R M
  nsmul := by
    intro d x
    fconstructor
    by_cases hd : d = 0
    · refine ⟨∅, fun n ↦ d * (x.1.toFun n), ?_⟩
      simp [hd, zero_mul]
    · refine ⟨{y ∈ x.1.support | d * (x.1.2 y) ≠ 0}, fun n ↦ d * (x.1.toFun n), ?_⟩
      intro a
      simp only [mem_support_iff]
      constructor
      · intro ha
        simp at ha
        exact ha.2
      · intro hd
        simp
        constructor
        · by_contra habs
          apply hd
          have : x.1.2 a = 0 := by
            exact habs
          rw [this]
          rw [mul_zero]
        · exact hd
    · by_cases hd : d = 0
      · rw [hd]
        simp
      · simp [hd]
        apply subset_trans
        apply Finset.filter_subset
        have := x.2
        rw [bddLaurentSubmodule.mem_iff] at this
        exact this
  neg := _
  zsmul := _


#exit
instance (M : bddLaurentSubmodule R) : AddCommGroup M where
  add_assoc := by
    intro x y z
    ext n
    exact add_assoc ..
  zero := by
    use 0
    simp
  zero_add := by
    intro
    ext
    simp
    rfl
  add_zero := by
    intro
    ext
    simp
    rfl
  nsmul := by
    intro d x
    fconstructor
    by_cases hd : d = 0
    · refine ⟨∅, fun n ↦ d * (x.1.toFun n), ?_⟩
      simp [hd, zero_mul]
    · refine ⟨{y ∈ x.1.support | d * (x.1.2 y) ≠ 0}, fun n ↦ d * (x.1.toFun n), ?_⟩
      intro a
      simp only [mem_support_iff]
      constructor
      · intro ha
        simp at ha
        exact ha.2
      · intro hd
        simp
        constructor
        · by_contra habs
          apply hd
          have : x.1.2 a = 0 := by
            exact habs
          rw [this]
          rw [mul_zero]
        · exact hd
    · by_cases hd : d = 0
      · rw [hd]
        simp
      · simp [hd]
        apply subset_trans
        apply Finset.filter_subset
        have := x.2
        rw [bddLaurentSubmodule.mem_iff] at this
        exact this
  neg := by
    rintro ⟨x.val, x.prop⟩
    use -x.val
    simp
    rw [support_neg]
    simp at x.prop
    exact x.prop
  zsmul := by
    intro d x
    fconstructor
    by_cases hd : d = 0
    · refine ⟨∅, fun n ↦ d * (x.1.toFun n), ?_⟩
      simp [hd, zero_mul]
    · refine ⟨{y ∈ x.1.support | d * (x.1.2 y) ≠ 0}, fun n ↦ d * (x.1.toFun n), ?_⟩
      intro a
      simp only [mem_support_iff]
      constructor
      · intro ha
        simp at ha
        exact ha.2
      · intro hd
        simp
        constructor
        · by_contra habs
          apply hd
          have : x.1.2 a = 0 := by
            exact habs
          rw [this]
          rw [mul_zero]
        · exact hd
    · by_cases hd : d = 0
      · rw [hd]
        simp
      · simp [hd]
        apply subset_trans
        apply Finset.filter_subset
        have := x.2
        rw [bddLaurentSubmodule.mem_iff] at this
        exact this
  neg_add_cancel := by
    rintro ⟨x.val, x.prop⟩
    ext d
    simp
    -- rw [M.neg]
  add_comm := sorry


end LaurentPolynomials
