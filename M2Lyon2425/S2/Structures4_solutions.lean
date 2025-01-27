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
  mem_iff : ∀ f : R{X}, f ∈ carrier ↔ (f.support) ⊆ Finset.Icc LB UB

-- export bddLaurentSubmodule (mem_iff)

attribute [simp] bddLaurentSubmodule.mem_iff

-- @[ext]
-- lemma ext (x y : R{X}) (H : ∀ n, x.2 n = y.2 n) : x = y := Finsupp.ext H


-- instance :  CoeSort (bddLaurentSubmodule R) (Type _) := ⟨CoeSort.coe ∘ bddLaurentSubmodule.carrier⟩
instance :  CoeSort (bddLaurentSubmodule R) (Type _) := ⟨fun M ↦ ↥M.carrier⟩

variable (M : bddLaurentSubmodule R)

-- instance : CoeFun R{X} (fun _ ↦ ℤ →₀ R) := inferInstance
  -- coe := fun m ↦ m.toFun

instance : FunLike R{X} ℤ R := inferInstanceAs (FunLike (ℤ →₀ R) ℤ R)

instance : CoeFun M (fun _ ↦ ℤ → R) where
  coe := fun m ↦ m.1.toFun

-- @[simp]
-- lemma fun_apply {x : M} {n : ℤ} : x.1.toFun n = x n := by
--   rfl

-- @[simp]?
-- lemma fun_apply' {x : R{X}} {n : ℤ} : x n = x.toFun n := rfl

@[ext]
lemma bddext (M : bddLaurentSubmodule R) ⦃x y : M⦄ (H : ∀ n, x n = y n):
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
  (x + y) n = x n + y n := rfl

instance (M : bddLaurentSubmodule R) : Zero M where
  zero := by
    use 0
    simp only [bddLaurentSubmodule.mem_iff, support_zero, empty_subset]

instance : Neg M where
neg := by
  rintro ⟨a.val, a.prop⟩
  use -a.val
  simp
  rw [support_neg]
  simp at a.prop
  exact a.prop


-- @[simp]
-- lemma neg_apply (a : M) (n : ℤ) : (-a.1).toFun n = - (a.1.toFun n) := by rfl

-- @[simp]
-- lemma neg_apply' (a : M) (n : ℤ) : (-a.1).toFun n = - (a.1.toFun n) := by rfl

@[simp]
lemma neg_apply (a : M) (n : ℤ) : (-a : M) n = - (a n : R) := by rfl

lemma neg_add : ∀ a : M, -a + a = 0 := by
  intro a
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


instance (M : bddLaurentSubmodule R) : AddMonoid M where
  add_assoc := by
    intro x y z
    ext n
    exact add_assoc ..
  zero_add := zero_add R M
  add_zero := add_zero R M
  nsmul := by
    intro d x
    fconstructor
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
    simp only [ne_eq, bddLaurentSubmodule.mem_iff]
    apply (Finset.filter_subset _ _).trans
    simp [← bddLaurentSubmodule.mem_iff, x.2]
  nsmul_zero := by
    intro
    ext
    simp
    rfl
  nsmul_succ := by
    intro n x
    ext m
    simp
    ring


instance (M : bddLaurentSubmodule R) : AddCommGroup M where
  zsmul := by
    intro d x
    fconstructor
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
    simp only [ne_eq, bddLaurentSubmodule.mem_iff]
    apply (Finset.filter_subset _ _).trans
    simp [← bddLaurentSubmodule.mem_iff, x.2]
  zsmul_zero' := by
    intro
    ext
    simp
    rfl
  zsmul_succ' := by
    intro n x
    ext m
    simp
    ring
  zsmul_neg' := by
    rintro n ⟨x.val, x.prop⟩
    ext m
    simp
    ring
  neg_add_cancel := by
    intro
    ext m
    simp
    rfl
  add_comm := by
    intro n x
    ext m
    simp
    ring

instance : Module R M where
  smul := by
    rintro r ⟨m.val, v.prop⟩
    use r • m.val
    simp only [bddLaurentSubmodule.mem_iff] at v.prop ⊢
    exact (support_smul (b := r) (g := m.val)).trans v.prop
  one_smul := by
    intro
    ext
    apply one_smul
  mul_smul := by
    intros
    ext
    apply mul_smul
  smul_zero := by
    intro
    ext
    exact smul_zero ..
  smul_add := by
    intros
    ext
    exact smul_add ..
  add_smul := by
    intros
    ext
    exact add_smul ..
  zero_smul := by
    intro
    ext
    exact zero_smul ..

#synth CommRing R{X}

@[simp]
lemma smul_apply (f : R{X}) (r : R) (n : ℤ) : (r • f) n = r • (f n) := by
  rfl

@[simp]
lemma smul_apply' {f : M} {r : R} {n : ℤ} : (r • f) n = r • (f n) := rfl

instance : Lattice (bddLaurentSubmodule R) where
  sup := by
    intro M N
    use Submodule.span R (M.carrier ∪ N.carrier)
    use min M.UB N.UB
    use max M.LB N.LB
    intro f
    simp
    refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
    · obtain ⟨T, hT, hfT⟩ := Submodule.mem_span_finite_of_mem_span hf
      obtain ⟨g, hg⟩ := mem_span_finset.mp hfT
      intro n hn
      simp at hn
      obtain ⟨t, ht, ht_nz⟩ : ∃ t ∈ T, t.toFun n ≠ 0 := by
        by_contra!
        -- apply_fun (fun l : R{X} ↦ l.toFun) at hg
        -- rw [funext_iff] at hg
        -- specialize hg n
        -- -- simp at hg
        have uno := @Finsupp.finset_sum_apply (S := T) (α := ℤ) (N := R)
          (f := fun x ↦ g x • x)
        rw [Finsupp.ext_iff] at hg
        -- specialize this n
        -- have := @sum_smul
        specialize hg n
        rw [uno] at hg
        have htsmul (t : R{X}) (ht : t ∈ T) := smul_apply R t (g t) n
        have due := @Finset.sum_congr (s₁ := T) (s₂ := T)
          (f := fun x : R{X} ↦ (g x • x) n)
          (g := fun x : R{X} ↦ g x • (x n))
          _ (rfl) htsmul
        have tre := @Finset.sum_congr (s₁ := T) (s₂ := T)
          (f := fun x : R{X} ↦ g x • (x n))
          (g := 0) _ (rfl) ?_
        rw [due, tre] at hg
        simp only [Pi.zero_apply, sum_const_zero] at hg
        exact hn hg.symm
        · intro t ht
          simp
          apply mul_eq_zero_of_right
          apply this
          exact ht


          -- apply this


          -- specialize this ⟨
          -- simp


        -- simp_rw [this] at hg

        -- have htsmul (t : T) : (((g t.1) • t.1) : ℤ → R) n = (g t) • (t.1 n) := sorry
        -- have := @Finsupp.sum_apply
        --  [fae_smul_apply] at hg
        -- simp at hg
        -- rw [Finsupp.smul] at hg
        -- simp_rw [smul_apply]
        -- simp_rw [this] at hg
        -- erw [this]
        -- rw [← this]
      have : t.support ⊆ Icc (max M.LB N.LB) (min M.UB N.UB) := by
        specialize hT ht
        rw [Set.mem_union] at hT
        sorry
      apply this-- t ht-- ⟨t, ht⟩
      simp
      exact ht_nz


      -- rw [← hg]
      -- -- have fss := @Finsupp.support_filter-- (f := g)
      -- -- apply fss
      -- have := @Finset.support_sum (s := T) (α := R{X})
      --   (f := fun i j ↦ ((g i : R) • i)) _
      -- -- simp only [Function.support_subset_iff, ne_eq, Set.mem_iUnion, /- Function.mem_support, -/
      -- --   /- exists_prop, forall_const -/] at this
      -- -- apply subset_trans
      -- -- simp
      -- have fs : (Function.support fun x ↦ ∑ i ∈ T, g i • i) = (↑(∑ i ∈ T, g i • i).support : Set ℤ) := by
      --   norm_cast
      --   -- simp

      --specialize hf (Submodule.span R M.carrier)


    · rw [Submodule.mem_span]
      rintro p hp
      apply Set.mem_of_subset_of_mem hp
      rw [Set.mem_union]
      left
      simp
      apply hf.trans
      apply Icc_subset_Icc
      exact Int.le_max_left M.LB N.LB
      exact Int.min_le_left M.UB N.UB



  le := sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
  inf := sorry
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry

end

end LaurentPolynomials
