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
here, which is the representation `τᵣ` on `G → k` (or `kᴳ`) induced by
multiplication on the right in `G`. We denote by `π s` the evaluation map
at `s` on `G → k` and by `α` the projection map from `Aut (F k G)` to the
`finrep_r k G` component.

## Reference

<https://math.leidenuniv.nl/scripties/1bachCommelin.pdf>
-/

noncomputable section

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

/-- The monoidal category of finite dimensional
representations of `G` over `k` -/
abbrev FinRep := FullSubcategory (P k G)

variable {k G}
variable (X : FinRep k G)

namespace FinRep

def ρ := X.1.ρ
def V := X.1.V

end FinRep

variable (k G)

noncomputable def Fmon : MonoidalFunctor (FinRep k G) (ModuleCat k) :=
  (fullMonoidalSubcategoryInclusion _).comp (Action.forgetMonoidal _ _)

/-- The (monoidal) forgetful functor from `FinRep k G` to `ModuleCat k` -/
def F := (Fmon k G).toLaxMonoidalFunctor

lemma F_μ {X Y : FinRep k G} : (F k G).μ X Y = 𝟙 _ := rfl

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

def nat {X Y : FinRep k G} (f : X ⟶ Y) :
    (η Y).comp f.hom = f.hom.comp (η X) := η.hom.naturality f

lemma apply : η X = η.hom.app X := rfl

lemma tensor {X Y : FinRep k G} : η (X ⊗ Y) = (η X) ⊗ (η Y) := by
  simp only [apply]
  have := η.hom.tensor X Y
  simp only [F_μ, Category.id_comp, Category.comp_id] at this
  exact this

end AutF

/-- Definition of `T g : AutF k G` by its components -/
def T_app (g : G) (X : FinRep k G) : X.V ≅ X.V where
  hom := X.ρ g
  inv := X.ρ g⁻¹
  hom_inv_id := ModuleCat.ext k fun x ↦ Rep.ρ_inv_self_apply X.obj g x
  inv_hom_id := ModuleCat.ext k fun x ↦ Rep.ρ_self_inv_apply g x

/-- The function defining `T` -/
def T_fun : G → AutF k G := by
  intro g
  apply MonoidalNatIso.ofComponents (T_app g) ?_
  intro _ _ f
  exact (f.comm g).symm

lemma T_apply (g : G) (X : FinRep k G) :
    (T_fun g).hom.app X = X.ρ g := rfl

variable (k G) in
/-- The group homomorphism `G →* AutF k G` involved in the main theorem -/
def T : G →* AutF k G where
  toFun := T_fun
  map_one' := by
    ext
    simp only [T_apply, map_one]
    exact rfl
  map_mul' := by
    intros
    ext
    simp only [T_apply, map_mul]
    exact rfl

end Defs

variable {k G}

section Indicator

variable {G : Type u} [DecidableEq G]

/-- Indicator function of `s : G` -/
@[reducible]
def e (s : G) : (G → k) := fun g ↦ if g = s then 1 else 0

lemma e_eq_single {G : Type u} [DecidableEq G] (s : G) :
    e s = Pi.single s (1 : k) := by
  ext _
  exact (Pi.single_apply _ _ _).symm

lemma e_self (s : G) :
    e s s = (1 : k) := if_pos rfl

lemma e_not_self {s t : G} (h : s ≠ t) :
    e s t = (0 : k) := if_neg h.symm

lemma e_eq_one {s t : G} (h : e s t = (1 : k)) : s = t := by
  simp_all only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]

lemma e_mul (s : G) (f : G → k) : (e s) * f = f s • (e s) := by
    ext t
    rw [e_eq_single]
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : s = t
    · rw [h]
      exact mul_comm _ _
    · rwa [← e_eq_single, e_not_self, zero_mul, mul_zero]

lemma e_mul_self (s : G) : (e s) * (e s) = ((e s) : G → k) := by
  ext
  rw [e_mul, e_self, one_smul]

lemma e_eq {s t u v : G} (h : e s t = (e u v : k)) : s = t → u = v := by
  intro h'
  rw [h', e_self] at h
  exact e_eq_one h.symm

lemma e_eq_iff (s t u v : G) : (e s t = (e u v : k)) ↔ (s = t ↔ u = v) := by
  constructor
  · intro h
    exact ⟨e_eq h, e_eq h.symm⟩
  · intro h
    by_cases h' : s = t
    · rw [h', e_self, h.mp h', e_self]
    · rw [e_not_self h', e_not_self (h' ∘ h.mpr)]

lemma e_right_mul [Group G] (s t u : G) :
    e t (u * s) = (e (t * s⁻¹) u : k) := by
  rw [e_eq_iff]
  exact mul_inv_eq_iff_eq_mul.symm

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

lemma π_apply (G : Type u) (s : G) (f : G → k) : (π s) f = f s := rfl


/-- Multiplication map on `G` on the right -/
def r (s : G) (g : G) : G := g * s
/-- Multiplication map on `G` on the left -/
def l (s : G) (g : G) : G := s * g
/-- `τᵣ` as a function -/
def τᵣ_fun (s : G) (f : G → k) : (G → k) := f ∘ (r s)
/-- `τₗ` as a function -/
def τₗ_fun (s : G) (f : G → k) : (G → k) := f ∘ (l s⁻¹)

lemma e_r [DecidableEq G] (s t : G) :
    (e s) ∘ (r t) = (e (s * t⁻¹) : G → k) := by
  ext u
  rw [Function.comp_apply]
  exact e_right_mul t s u

/-- `τᵣ` as a `LinearMap` -/
def τᵣ_linmap (s : G) : (G → k) →ₗ[k] (G → k) where
  toFun := τᵣ_fun s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `τₗ` as a `LinearMap` -/
def τₗ_linmap (s : G) : (G → k) →ₗ[k] (G → k) where
  toFun := τₗ_fun s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The representation on `G → k` induced by
multiplication on the right in `G` -/
def τᵣ : Representation k G (G → k) where
  toFun := τᵣ_linmap
  map_one' := by
    ext
    simp only [LinearMap.one_apply, LinearMap.coe_mk, AddHom.coe_mk,
    τᵣ_fun, τᵣ_linmap, Function.comp_apply, r, mul_one]
  map_mul' _ _ := by
    ext
    simp only [LinearMap.one_apply, LinearMap.coe_mk, AddHom.coe_mk,
    τᵣ_fun, τᵣ_linmap, Function.comp_apply, r, LinearMap.mul_apply]
    rw [mul_assoc]

lemma τᵣ_apply (s : G) (f : G → k) (t : G) :
    τᵣ s f t = f (t * s) := rfl

lemma τᵣ_e [DecidableEq G] (s t : G) : (τᵣ s (e t) : G → k) = e (t * s⁻¹) := by
  ext u
  simp_all only [τᵣ_apply]
  exact e_right_mul s t u

/-- The representation on `G → k` induced by
multiplication on the left in `G` -/
def τₗ : Representation k G (G → k) where
  toFun := τₗ_linmap
  map_one' := by
    ext
    simp only [LinearMap.one_apply, LinearMap.coe_mk, AddHom.coe_mk,
    τₗ_fun, τₗ_linmap, Function.comp_apply, l, one_mul, inv_one]
  map_mul' _ _ := by
    ext
    simp only [LinearMap.one_apply, LinearMap.coe_mk, AddHom.coe_mk,
    τₗ_fun, τₗ_linmap, Function.comp_apply, l, LinearMap.mul_apply]
    rw [mul_inv_rev, mul_assoc]

lemma τₗ_apply (s : G) (f : G → k) (t : G) :
    τₗ s f t = f (s⁻¹ * t) := rfl

variable (k G) in
/-- The representation `⟨G → k, τᵣ⟩` induced by multiplication
on the right in `G` as a `Rep k G` -/
def rep_r : Rep k G where
  V := ModuleCat.mk (G → k)
  ρ := τᵣ

variable [Fintype G]

variable (k G) in
/-- The representation `⟨G → k, τᵣ⟩` induced by multiplication on
the right in `G` as a `FinRep k G` -/
def finrep_r : FinRep k G where
  obj := rep_r k G
  property := FiniteDimensional.finiteDimensional_pi k

lemma finrep_r_ρ : (finrep_r k G).ρ = τᵣ := rfl

variable (k G) in
/-- The representation `⟨G → k, τₗ⟩` induced by multiplication on
the left in `G` as a `FinRep k G` -/
def finrep_l : FinRep k G where
  obj := {
    V := ModuleCat.mk (G → k)
    ρ := τₗ
  }
  property := FiniteDimensional.finiteDimensional_pi k

/-- Component of `η : AutF k G` at `finrep_r k G` as a linear map -/
def α (η : AutF k G) : (G → k) →ₗ[k] G → k := η (finrep_r k G)

end finrep_r

variable [DecidableEq G] [Fintype G]

section lemma4

-- *lemma 4.4*
lemma T_inj : Function.Injective (T k G) := by
  rw [injective_iff_map_eq_one]
  intro s h
  apply_fun α at h
  simp only [AutF.apply, α] at h
  replace h : (e 1) (1 * s) = e 1 1 :=
    congrFun (congrFun (congrArg DFunLike.coe h) (e 1)) 1
  rw [e_self, one_mul] at h
  exact (e_eq_one h).symm

end lemma4

section lemma5

lemma one_eq_sum_e {k G : Type u} [Field k] [DecidableEq G] [Fintype G] :
    ∑ (s : G), e s = (1 : G → k) := by
  ext1 x
  simp_all only [Finset.sum_apply, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Pi.one_apply]


-- *lemma 4.5*
lemma lem5 {G : Type u} [DecidableEq G] [Fintype G]
    (φ : ((G → k)) →ₐ[k] k) :
    ∃ (s : G), φ = π s := by
  have h1 := map_one φ
  obtain ⟨s, hs⟩ : ∃ (s : G), φ (e s) ≠ 0 := by
    rw [← one_eq_sum_e] at h1
    by_contra
    simp_all only [map_sum, ne_eq, not_exists, not_not,
      Finset.sum_const_zero, zero_ne_one]
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

lemma lem5_unique {G : Type u} [DecidableEq G] [Fintype G]
    (φ : ((G → k)) →ₐ[k] k) :
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
def μ_linmap : TensorProduct k (G → k) (G → k) →ₗ[k] (G → k) := by
  apply TensorProduct.lift
  apply LinearMap.mk₂ k (fun (f g : G → k) ↦ f * g)
  exact right_distrib
  exact smul_mul_assoc
  exact left_distrib
  exact mul_smul_comm

lemma μ_def {G : Type u} (f g : G → k) : μ_linmap (f ⊗ₜ[k] g) = f * g := rfl

/-- μ is a representation morphism -/
def μ_rep_hom : rep_r k G ⊗ rep_r k G ⟶ rep_r k G where
  hom := μ_linmap
  comm := by
    intro (_ : G)
    rw [Action.tensor_rho]
    ext (u : TensorProduct k (G → k) (G → k))
    refine TensorProduct.induction_on u ?_ ?_ ?_
    · exact rfl
    · exact fun _ _ ↦ rfl
    · intro _ _ hx hy
      simp only [map_add, hx, hy]

/-- The `FinRep k G` morphism induced by multiplication -/
def μ : finrep_r k G ⊗ finrep_r k G ⟶ finrep_r k G := μ_rep_hom

def lem6_mul (η : AutF k G) :
    ∀ (x y : G → k), (α η) (x * y) = ((α η) x) * ((α η) y) := by
  have := η.nat μ
  rw [AutF.tensor] at this
  intro f g
  exact (congrFun (congrArg DFunLike.coe this) (f ⊗ₜ[k] g))

-- *lemma 4.6*
def lem6_toAlgHom (η : AutF k G) : ((G → k)) →ₐ[k] ((G → k)) := by
  refine AlgHom.ofLinearMap (α η) ?_ (lem6_mul η)
  let α_inv : (G → k) → (G → k) := η.inv.app (finrep_r k G)
  have : NatTrans.app _ _ = (MonoidalNatTrans.id _).app _ :=
    congrFun (congrArg _ (congrArg _ η.inv_hom_id)) (finrep_r k G)
  rw [MonoidalNatTrans.comp_toNatTrans_lax,
      NatTrans.comp_app, MonoidalNatTrans.id_toNatTrans_app] at this
  replace : (α η) (α_inv _) = (1 : G → k) :=
    congrFun (congrArg DFunLike.coe this) (1 : G → k)
  have h := this
  rwa [← one_mul (α_inv _), lem6_mul, h, mul_one] at this

lemma lem6_def {G : Type u} [Group G] [Fintype G] (η : AutF k G) :
    (lem6_toAlgHom η).toLinearMap = α η := AlgHom.toLinearMap_ofLinearMap _ _ _

end lemma6

section lemma7

def τₗ_rep_hom (s : G) : (finrep_r k G) ⟶ (finrep_r k G) where
  hom := τₗ s
  comm := by
    intro (t : G)
    ext (f : G → k)
    simp only [@ModuleCat.coe_comp, @Function.comp_apply]
    rw [@Function.funext_iff]
    intro u
    change (τₗ s) ((τᵣ t) f) u = (τᵣ t) ((τₗ s) f) u
    simp only [τₗ_apply, τᵣ_apply, mul_assoc]

-- *lemma 4.7*
lemma lem7 (η : AutF k G) :
    ∃ (s : G), α η = τᵣ s := by
  have hnat (t : G) := η.nat (τₗ_rep_hom t)
  let α_hom := lem6_toAlgHom η
  obtain ⟨s, hs⟩ := lem5 ((π (1 : G)).comp α_hom)
  use s
  have (u t : G) : α_hom (e u) t = e (t⁻¹ * u) s := by
    calc
      _ = α_hom (e u) ((t⁻¹)⁻¹ * 1) := by
        rw [mul_one, inv_inv]
      _ = τₗ t⁻¹ (α_hom (e u)) 1 := rfl
      _ = α_hom (τₗ t⁻¹ (e u)) 1 :=
        congrFun (congrFun (congrArg DFunLike.coe (hnat t⁻¹)) (e u)).symm 1
      _ = (π 1).comp α_hom (τₗ t⁻¹ (e u)) := rfl
      _ = π s (τₗ t⁻¹ (e u)) :=
        congrFun (congrArg DFunLike.coe hs) _
      _ = _ := by
        rw [π_apply, τₗ_apply, e_eq_iff]
        exact eq_inv_mul_iff_mul_eq
  apply Basis.ext (Pi.basisFun k G)
  intro u
  simp only [Pi.basisFun_apply, ← e_eq_single, Function.funext_iff]
  intro t
  change α_hom _ _ = τᵣ _ _ _
  rw [τᵣ_apply, this, e_eq_iff]
  exact inv_mul_eq_iff_eq_mul

lemma lem7_unique (η : AutF k G) :
    ∃! (s : G), α η = τᵣ s := by
  obtain ⟨s, hs⟩ := lem7 η
  refine ⟨s, hs, ?_⟩
  intro t h
  replace hs := h ▸ congrFun (congrArg DFunLike.coe hs) (e t)
  change (e t) ∘ (r t) = (e t) ∘ (r s) at hs
  rw [e_r, e_r, mul_inv_cancel] at hs
  replace hs := e_fun_eq hs
  apply Eq.symm
  rwa [eq_mul_inv_iff_mul_eq, one_mul] at hs

end lemma7

section lemma8

def φ_term (X : FinRep k G) (v : X.V) (f : G → k) (s : G) : X.V :=
  (f s) • (X.ρ s⁻¹ v)

lemma φ_term_def  {G : Type u} [Group G] [Fintype G]
    (X : FinRep k G) (v : X.V) (f : G → k) (s : G) :
    φ_term X v f s = (f s) • (X.ρ s⁻¹ v) := rfl

def φ (X : FinRep k G) (v : X.V) : (G → k) →ₗ[k] X.V where
  toFun := fun f ↦ ∑ s : G, (f s) • (X.ρ s⁻¹ v)
  map_add' := by
    intros
    simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intros
    simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul]
    rw [RingHom.id_apply, Finset.smul_sum]

lemma φ_def {G : Type u} [Group G] [Fintype G]
    {X : FinRep k G} {v : X.V} {f : G → k} :
    (φ X v) f = ∑ s : G, (f s) • (X.ρ s⁻¹ v) := rfl

lemma φ_e_one_eq_id {X : FinRep k G} {v : X.V} : (φ X v) (e 1) = v := by
  rw [φ_def]
  let a (s : G) : X.V := (e (1 : G) s : k) • (X.ρ s⁻¹) v
  calc
    _ = (∑ s ∈ {1}ᶜ, a s) + a 1 :=
      Fintype.sum_eq_sum_compl_add _ _
    _ = 0 + a 1 := by
      apply add_right_cancel_iff.mpr
      apply Finset.sum_eq_zero
      intro _ h
      rw [Finset.mem_compl, Finset.not_mem_singleton] at h
      change _ • _ = _
      rw [e_not_self h.symm, zero_smul]
    _ = _ := by
      rw [zero_add]
      change _ • _ = _
      rw [e_self, one_smul]
      simp only [inv_one, map_one, LinearMap.one_apply]

def r_inj (t : G) : G ↪ G where
  toFun := r t
  inj' := mul_left_injective t

lemma r_inj_def {G : Type u} [Group G] [Fintype G]
    (t : G) (s : G) : (r_inj t) s = s * t := rfl

def φ_rep_mor (X : FinRep k G) (v : X.V) : (finrep_r k G) ⟶ X where
  hom := φ X v
  comm := by
    intro (t : G)
    ext (f : G → k)
    change (φ X v) (τᵣ t f) = X.ρ t (φ X v f)
    simp only [φ_def, map_sum]
    have := Finset.sum_map Finset.univ (r_inj t⁻¹) (φ_term X v (τᵣ t f))
    simp only [φ_term_def, Finset.univ_map_embedding] at this
    rw [this]
    apply Finset.sum_congr rfl
    intros
    simp only [τᵣ_apply, r_inj_def, mul_assoc, inv_mul_cancel, mul_one,
      mul_inv_rev, inv_inv, map_smul, map_mul, LinearMap.mul_apply]

-- *lemma 4.8*
lemma lem8 (η₁ η₂ : AutF k G)
    (h : α η₁ = α η₂) : η₁ = η₂ := by
  ext X (v : X.V)
  have h1 : _ ∘ₗ (φ X v) = (φ X v) ∘ₗ (α η₁) := η₁.nat (φ_rep_mor X v)
  rw [h] at h1
  have h2 : _ ∘ₗ (φ X v) = (φ X v) ∘ₗ (α η₂) := η₂.nat (φ_rep_mor X v)
  rw [← h2] at h1
  replace h1 := congrFun (congrArg DFunLike.coe h1) (e 1)
  rwa [LinearMap.comp_apply, φ_e_one_eq_id,
       LinearMap.comp_apply, φ_e_one_eq_id] at h1

end lemma8

section prop11

-- *proposition 4.11*
lemma T_surj : Function.Surjective (T k G) := by
  intro η
  obtain ⟨s, h⟩ := lem7 η
  use s
  apply lem8
  exact h.symm

end prop11

section thm

-- *theorem 4.3*
theorem TannakaDuality : Function.Bijective (T k G) :=
  ⟨T_inj, T_surj⟩

example : G ≃* AutF k G :=
  MulEquiv.ofBijective (T k G) TannakaDuality

end thm
