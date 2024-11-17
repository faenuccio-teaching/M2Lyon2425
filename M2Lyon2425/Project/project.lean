import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.RepresentationTheory.Rep

/-!
# Tannaka duality for finite groups

Given a field `k` and a finite group `G`, Tannaka duality expresses the fact
that one can recover `G` from the monoidial category `FinRep k G`
of finite dimensional representations of `G` over `k`.

More specifically, we consider the (monoidal) forgetful functor
`F k G : FinRep k G ⥤ ModuleCat k` to the category of vector spaces over `k`,
and `Aut (F k G)` its group of automorphisms, i.e. the group of monoidal
natural isomorphisms `(F k G) ⟹ (F k G)`. We further construct
the group homomorphism `T : G →* Aut (F k G)` defined by `T g ⟨V, ρ⟩ := ρ g`.

The theorem `TannakaDuality` states that `T` is an isomorphism.

The proof revolves around one particular representation called `finrep_r k G`
here, which is the representation `τᵣ` on `G → k` (or `kᴳ`) induced by multiplication
on the right in `G`. We denote by `π s` the evaluation map at `s` on `G → k` and
by `α` the projection map from `Aut (F k G)` to the `finrep_r k G` component.

## Reference

<https://math.leidenuniv.nl/scripties/1bachCommelin.pdf>
-/


suppress_compilation

open CategoryTheory
open MonoidalCategory

universe u

variable (k G : Type u) [Field k] [Group G]

section Defs

/-- Property of a representation being finite dimensional -/
def P (X : Rep k G) := FiniteDimensional k X.V

instance : MonoidalPredicate (P k G) where
  prop_id := Module.Finite.self _
  prop_tensor := by
    intro X Y _ _
    rw [P] at *
    exact Module.Finite.tensorProduct _ ↑X.V ↑Y.V

/-- The monoidal category of finite dimensional representation of `G` over `k` -/
abbrev FinRep := FullSubcategory (P k G)

variable {k G}
variable (X : FinRep k G)

namespace FinRep

def ρ := X.1.ρ
def V := X.1.V
def toRep := X.1
def findim : FiniteDimensional k X.V := X.2

def toRepHom {X Y : FinRep k G} (f : X ⟶ Y) : X.obj ⟶ Y.obj := f

def toModHom {X Y : FinRep k G} (f : X ⟶ Y) : X.obj.V ⟶ Y.obj.V := f.hom

def toLin {X Y : FinRep k G} (f : X ⟶ Y) : X.V →ₗ[k] Y.V := f.hom

def toFun {X Y : FinRep k G} (f : X ⟶ Y) : X.V → Y.V := f.hom

end FinRep

variable (k G)

def Fmon :
    MonoidalFunctor (FinRep k G) (ModuleCat k) :=
  (fullMonoidalSubcategoryInclusion _).comp (Action.forgetMonoidal _ _)

/-- The (monoidal) forgetful functor from `FinRep k G` to `ModuleCat k` -/
def F := (Fmon k G).toLaxMonoidalFunctor

@[simp]
lemma F_μ {X Y : FinRep k G} : (F k G).μ X Y = 𝟙 _ := rfl
@[simp]
lemma F_ε : (F k G).ε = 𝟙 _ := rfl
@[simp]
lemma F_obj {X : FinRep k G} : (F k G).obj X = X.V := rfl
-- @[simp]
-- lemma F_map {f} : (F k G).map f = f.hom := rfl

/-- Type of (monoidal) automorphisms of `F k G` -/
abbrev AutF := Aut (F k G)

variable (η : AutF k G)

instance : DFunLike (AutF k G) (FinRep k G) (fun X ↦ X.V ⟶ X.V) where
  coe η X := η.hom.app X
  coe_injective' := by
    intro _ _ _
    ext
    simp_all only


variable {k G}

namespace AutF

def toAutFmon : Aut (Fmon k G) where
  hom := η.hom
  inv := η.inv
  hom_inv_id := η.hom_inv_id
  inv_hom_id := η.inv_hom_id


def nat {X Y : FinRep k G} (f : X ⟶ Y) :
    (η Y).comp f.hom = f.hom.comp (η X) := by
  rw [← @ModuleCat.comp_def, ← @ModuleCat.comp_def]
  exact η.hom.naturality f

-- @[reducible]
-- def autf_eval := η X
-- @[simp]
lemma apply : η X = η.hom.app X := rfl

-- @[simp]
lemma mul_def (x y : AutF k G) : x * y = Iso.trans y x := rfl


lemma tensor {X Y : FinRep k G} : η (X ⊗ Y) = (η X) ⊗ (η Y) := by
  rw [apply, apply, apply]
  have := η.hom.tensor X Y
  simp only [F_μ, Category.id_comp, Category.comp_id] at this
  exact this

end AutF

/-- Definition of `T g : AutF k G` by its components -/
def Tapp (g : G) (X : FinRep k G) : (F k G).obj X ≅ (F k G).obj X where
  hom := {
    toFun := X.ρ g
    map_add' := fun _ _ ↦ LinearMap.map_add _ _ _
    map_smul' := fun _ _ ↦ LinearMap.CompatibleSMul.map_smul _ _ _
  }
  inv := {
    toFun := X.ρ g⁻¹
    map_add' := fun _ _ ↦ LinearMap.map_add _ _ _
    map_smul' := fun _ _ ↦ LinearMap.CompatibleSMul.map_smul _ _ _
  }
  hom_inv_id := ModuleCat.ext _ fun _ ↦ Rep.ρ_inv_self_apply _ _ _
  inv_hom_id := ModuleCat.ext _ fun _ ↦ Rep.ρ_self_inv_apply _ _

@[simp]
lemma Tapp_hom (g : G) (X : FinRep k G) :
  (Tapp g X).hom = X.ρ g := rfl

@[simp]
lemma Tapp_inv (g : G) (X : FinRep k G) :
  (Tapp g X).inv = X.ρ g⁻¹ := rfl

/-- The function defining `T` -/
def T_app : G → AutF k G := by
  intro g
  apply MonoidalNatIso.ofComponents (Tapp g) ?_
  intro _ _ f
  exact (f.comm _).symm

@[simp]
lemma T_apply (g : G) (X : FinRep k G) :
  (T_app g).hom.app X = X.ρ g := rfl

variable (k G) in
/-- The group homomorphism `G →* AutF k G` involved in the main theorem -/
def T : G →* AutF k G where
  toFun := T_app
  map_one' := by
    ext
    simp only [T_apply, Tapp_hom, map_one]
    exact rfl
  map_mul' := by
    intros
    ext
    simp only [T_apply, Tapp_hom, map_mul]
    exact rfl

end Defs

variable {k G}

section Indicator

variable {G : Type u} [DecidableEq G]

/-- Indicator function of `s : G` -/
@[reducible]
def e (s : G) : (G → k) := fun g ↦ if g = s then 1 else 0

lemma e_eq_single {G : Type u} [DecidableEq G] (s : G) : e s = Pi.single s (1 : k) := by
  ext _
  exact (Pi.single_apply _ _ _).symm

@[simp]
lemma e_self (s : G) :
    e s s = (1 : k) := if_pos rfl

@[simp]
lemma e_not_self {s t : G} (h : s ≠ t) :
   e s t = (0 : k) := if_neg h.symm

@[simp]
lemma e_eq_one {s t : G} (h : e s t = (1 : k)) :
  s = t := by simp_all only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]

lemma e_mul (s : G) (f : G → k) : (e s) * f = f s • (e s) := by
    ext t
    rw [e_eq_single]
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : s = t
    · rw [h]
      exact mul_comm _ _
    · rwa [← e_eq_single, e_not_self, zero_mul, mul_zero]

@[simp]
lemma e_mul_self (s : G) : (e s) * (e s) = ((e s) : G → k) := by
  ext
  rw [e_mul, e_self, one_smul]

lemma e_eq {s t u v : G} (h : e s t = (e u v : k)) : s = t → u = v  := by
  intro h'
  rw [h', e_self] at h
  exact e_eq_one h.symm

lemma e_eq_iff (s t u v : G) : (e s t = (e u v : k)) ↔ (s = t ↔ u = v)  := by
  constructor
  · intro h
    exact ⟨e_eq h, e_eq h.symm⟩
  · intro h
    by_cases h' : s = t
    · rw [h', e_self, h.mp h', e_self]
    · rw [e_not_self h', e_not_self (h' ∘ h.mpr)]

lemma e_mul₁_eq_mul₂ [Group G] (s t u : G) : e t (u * s) = (e (t * s⁻¹) u : k) := by
  rw [e_eq_iff]
  exact mul_inv_eq_iff_eq_mul.symm

lemma e_mul₁_eq_mul₂' [Group G] (s t u : G) : e t (s⁻¹ * u) = (e (s * t) u : k) := by
  rw [e_eq_iff]
  exact eq_inv_mul_iff_mul_eq


lemma e_fun_eq {s t : G} (h : e s = (e t : G → k)) : s = t :=
  (e_eq (congrFun h s) rfl).symm

end Indicator

section finrep_r

/-- `π s` is the evaluation map at `s : G` as an algebra homomorphism -/
def π (s : G) : (G → k) →ₐ[k] k where
  toFun f := f s
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
lemma π_apply (G : Type u) (s : G) (f : G → k) : (π s) f = f s := rfl


/-- Multiplication map on `G` on the right -/
def r (s : G) (g : G) : G := g * s
/-- Multiplication map on `G`on the left -/
def l (s : G) (g : G) : G := s * g
/-- `τᵣ` as a function -/
def τᵣ_app (s : G) (f : G → k) : (G → k) := f ∘ (r s)
/-- `τₗ` as a function -/
def τₗ_app (s : G) (f : G → k) : (G → k) := f ∘ (l s⁻¹)

attribute [reducible] r l -- τᵣ_app τₗ_app

lemma e_r [DecidableEq G] (s t : G) : (e s) ∘ (r t) = (e (s * t⁻¹) : G → k) := by
  ext u
  rw [Function.comp_apply]
  exact e_mul₁_eq_mul₂ t s u


/-- `τᵣ` as a `LinearMap` -/
def τᵣ_applin (s : G) : (G → k) →ₗ[k] (G → k) where
  toFun := τᵣ_app s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `τₗ` as a `LinearMap` -/
def τₗ_applin (s : G) : (G → k) →ₗ[k] (G → k) where
  toFun := τₗ_app s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (k G) in
/-- The representation on `G → k` induced by multiplication on the right in `G` -/
def τᵣ : Representation k G (G → k) where
  toFun := τᵣ_applin
  map_one' := by
    ext
    simp only [LinearMap.one_apply, LinearMap.coe_mk,
    AddHom.coe_mk, τᵣ_app, τᵣ_applin, Function.comp_apply, r, mul_one]
  map_mul' _ _ := by
    ext
    simp only [LinearMap.one_apply, LinearMap.coe_mk,
    AddHom.coe_mk, τᵣ_app, τᵣ_applin, Function.comp_apply, r, LinearMap.mul_apply]
    rw [mul_assoc]

-- @[simp]
lemma τᵣ_def (s : G) (f : G → k) : τᵣ k G s f = f ∘ (r s) := rfl

@[simp]
lemma τᵣ_apply (s : G) (f : G → k) (t : G) : ((τᵣ k G) s) f t = f (t * s) := rfl

@[simp]
lemma τᵣ_e [DecidableEq G] (s t : G) : (τᵣ k G s) (e t) = e (t * s⁻¹) := by
  ext u
  simp_all only [τᵣ_apply]
  exact e_mul₁_eq_mul₂ s t u

variable (k G) in
/-- The representation on `G → k` induced by multiplication on the left in `G` -/
def τₗ : Representation k G (G → k) where
  toFun := τₗ_applin
  map_one' := by
    ext
    simp only [LinearMap.one_apply, LinearMap.coe_mk,
    AddHom.coe_mk, τₗ_app, τₗ_applin, Function.comp_apply, one_mul, inv_one]
  map_mul' _ _ := by
    ext
    simp only [LinearMap.one_apply, LinearMap.coe_mk,
    AddHom.coe_mk, τₗ_app, τₗ_applin, Function.comp_apply, l, LinearMap.mul_apply]
    rw [mul_inv_rev, mul_assoc]

-- @[simp]
lemma τₗ_def (s : G) (f : G → k) : τₗ k G s f = f ∘ (l s⁻¹) := rfl

@[simp]
lemma τₗ_apply (s : G) (f : G → k) (t : G) : ((τₗ k G) s) f t = f (s⁻¹ * t) := rfl

@[simp]
lemma τₗ_e [DecidableEq G] (s t : G) : (τₗ k G s) (e t) = e (s * t) := by
  ext u
  simp_all only [τₗ_apply]
  exact e_mul₁_eq_mul₂' _ _ _


variable (k G) in
/-- The representation `(G → k, τᵣ)` induced by multiplication on the right in `G` as a `FinRep k G` -/
def rep_r : Rep k G where
  V := ModuleCat.mk (G → k)
  ρ := τᵣ k G

@[simp]
lemma rep_r_V : (rep_r k G).V = (G → k) := rfl
@[simp]
lemma rep_r_ρ : (rep_r k G).ρ = τᵣ k G := rfl

variable [Fintype G]

variable (k G) in
/-- The representation `(G → k, τᵣ)` induced by multiplication on the right in `G` as a `FinRep k G` -/
def finrep_r : FinRep k G where
  obj := rep_r k G
  property := FiniteDimensional.finiteDimensional_pi k

@[simp]
lemma finrep_r_obj : (finrep_r k G).obj = rep_r k G := rfl
@[simp]
lemma finrep_r_ρ : (finrep_r k G).ρ = τᵣ k G := rfl
@[simp]
lemma finrep_r_V : (finrep_r k G).V = (G → k) := rfl

@[simp]
lemma finrep_r_obj_ρ : (finrep_r k G).obj.ρ = τᵣ k G := rfl
@[simp]
lemma finrep_r_obj_V : (finrep_r k G).obj.V = (G → k) := rfl

variable (k G) in
/-- The representation `(G → k, τₗ)` induced by multiplication on the left in `G` as a `FinRep k G` -/
def finrep_l : FinRep k G where
  obj := {
    V := ModuleCat.mk (G → k)
    ρ := τₗ k G
  }
  property := FiniteDimensional.finiteDimensional_pi k

@[simp]
lemma finrep_l_ρ: (finrep_l k G).ρ = τₗ k G := rfl
@[simp]
lemma finrep_l_V : (finrep_l k G).V = (G → k) := rfl

/-- Evaluation function of `η : AutF k G` at `finrep_r k G` -/
@[reducible]
def α (η : AutF k G) := η (finrep_r k G)

/-- Evaluation function of `η : AutF k G` at `finrep_r k G` -/
def α_map (η : AutF k G) : (G → k) → (G → k) := α η

lemma α_map_def (η : AutF k G) : α_map η = α η := rfl

end finrep_r

variable [DecidableEq G] [Fintype G]

section lemma4

-- *lemma 4.4*
lemma T_inj : Function.Injective (T k G) := by
  rw [injective_iff_map_eq_one]
  intro s h
  apply_fun α at h
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, AutF.apply,
  T_apply, finrep_r_ρ] at h
  replace h := congrFun (congrFun (congrArg DFunLike.coe h) (e 1)) 1
  change (e 1) (1 * s) = e 1 1 at h
  rw [e_self, one_mul] at h
  exact (e_eq_one h).symm

end lemma4

section lemma5

lemma one_eq_sum_e {k G : Type u} [Field k] [DecidableEq G] [Fintype G] :
    ∑ (s : G), e s = (1 : G → k) := by
  ext1 x
  simp_all only [Finset.sum_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.one_apply]


-- *lemma 4.5*
lemma lem5 {G : Type u} [DecidableEq G] [Fintype G] (φ : ((G → k)) →ₐ[k] k) :
    ∃ (s : G), φ = π s := by
  have h1 : φ 1 = 1 := map_one φ
  obtain ⟨s, hs⟩ : ∃ (s : G), φ (e s) ≠ 0 := by
    rw [← one_eq_sum_e] at h1
    by_contra
    simp_all only [map_sum, ne_eq, not_exists, not_not, Finset.sum_const_zero, zero_ne_one]
  have h2 : φ (1 - (e s)) = 0 := by
    suffices h : ((1 : G → k) - (e s)) * (e s) = 0 by
      apply_fun φ at h
      rw [map_mul, map_zero] at h
      exact eq_zero_of_ne_zero_of_mul_right_eq_zero hs h
    rw [mul_sub_right_distrib, one_mul, e_mul_self, sub_self]
  have h3 : φ (e s) = 1 := by
    rw [map_sub, h1, sub_eq_zero] at h2
    exact h2.symm
  use s
  ext f
  conv_lhs => rw [← one_mul (φ f), ← h3, ← map_mul]
  rw [π_apply, e_mul, map_smul, smul_eq_mul, h3, mul_one]

lemma lem5_unique {G : Type u} [DecidableEq G] [Fintype G] (φ : ((G → k)) →ₐ[k] k) :
    ∃! (s : G), φ = π s := by
  obtain ⟨s, hs⟩ := lem5 φ
  refine ExistsUnique.intro s hs ?_
  intro y h
  replace hs := congrFun (congrArg DFunLike.coe hs) (e y)
  rw [h, π_apply, π_apply, e_self] at hs
  exact e_eq_one hs.symm

end lemma5

section lemma6

/-- The LinearMap induced by multiplication on `G → k` -/
def μ_lin : TensorProduct k (G → k) (G → k) →ₗ[k] (G → k) := by
  refine TensorProduct.lift ?_
  apply LinearMap.mk₂ k (fun (f g : G → k) ↦ f * g)
  exact fun m₁ m₂ n ↦ right_distrib m₁ m₂ n
  exact fun c m n ↦ smul_mul_assoc c m n
  exact fun m n₁ n₂ ↦ left_distrib m n₁ n₂
  exact fun c m n ↦ mul_smul_comm c m n

lemma μ_def {G : Type u} (f g : G → k) : μ_lin (f ⊗ₜ[k] g) = f * g := rfl

/-- μ is a representation morphism -/
def μ_rep_hom : (finrep_r k G).obj ⊗ (finrep_r k G).obj ⟶ (finrep_r k G).obj where
  hom := μ_lin
  comm := by
    intro s
    rw [Action.tensor_rho]
    ext u
    change TensorProduct k (G → k) (G → k) at u
    refine TensorProduct.induction_on u ?_ ?_ ?_
    · exact rfl
    · exact fun x y ↦ rfl
    · intro x y hx hy
      rw [map_add, hx, map_add, hy]

/-- The `FinRep k G` morphism induced by multiplication -/
def μ : finrep_r k G ⊗ finrep_r k G ⟶ finrep_r k G := μ_rep_hom

def lem6_mul (η : AutF k G) :
    ∀ (x y : G → k), (α η) (x * y) = ((α_map η) x) * ((α_map η) y) := by
  have := η.nat μ
  rw [AutF.tensor] at this
  intro f g
  exact (congrFun (congrArg DFunLike.coe this) (f ⊗ₜ[k] g))

-- *lemma 4.6*
def lem6_toAlgHom (η : AutF k G) : ((G → k)) →ₐ[k] ((G → k)) := by
  refine AlgHom.ofLinearMap (α η) ?_ (lem6_mul η)
  let α_inv : (G → k) → (G → k) := η.inv.app (finrep_r k G)
  have := η.inv_hom_id
  replace : (η.inv ≫ η.hom).app (finrep_r k G) = (MonoidalNatTrans.id (F k G)).app (finrep_r k G) :=
    congrFun (congrArg _ (congrArg _ this)) _
  rw [@MonoidalNatTrans.comp_toNatTrans_lax,
      @NatTrans.comp_app,
      @MonoidalNatTrans.id_toNatTrans_app] at this
  replace : (η.inv.app (finrep_r k G) ≫ η.hom.app (finrep_r k G)) (1 : G → k) = (1 : G → k) := by
    rw [this]
    exact rfl
  change (α η) (α_inv (1 : G → k)) = (1 : G → k) at this
  have h := this
  rwa [← one_mul (α_inv 1), lem6_mul, α_map_def, h, mul_one] at this

lemma lem6_def {G : Type u} [Group G] [Fintype G] (η : AutF k G) :
    (lem6_toAlgHom η).toLinearMap = α η := rfl

end lemma6

section lemma7

-- *lemma 4.7*
lemma lem7 (η : AutF k G) :
    ∃ (s : G), α η = (τᵣ k G) s := sorry

lemma lem7_unique (η : AutF k G) :
    ∃! (s : G), α η = (τᵣ k G) s := by
  obtain ⟨s, hs⟩ := lem7 η
  refine ⟨s, hs, ?_⟩
  intro t h
  replace hs := congrFun (congrArg DFunLike.coe hs) (e t)
  rw [h] at hs
  change (e t) ∘ (r t) = (e t) ∘ (r s) at hs
  rw [e_r, e_r, mul_inv_cancel] at hs
  replace hs := e_fun_eq hs
  apply Eq.symm
  rwa [eq_mul_inv_iff_mul_eq, one_mul] at hs

end lemma7

section lemma8

-- *lemma 4.8*
lemma lem8 (η₁ η₂ : AutF k G)
    (h : α η₁ = α η₂) : η₁ = η₂ := sorry

end lemma8

lemma T_surj : Function.Surjective (T k G) := by
  intro η
  obtain ⟨s, h⟩ := lem7 η
  use s
  apply lem8
  exact h.symm

theorem TannakaDuality : Function.Bijective (T k G) :=
  ⟨T_inj, T_surj⟩

example : G ≃* AutF k G :=
  MulEquiv.ofBijective (T k G) TannakaDuality
