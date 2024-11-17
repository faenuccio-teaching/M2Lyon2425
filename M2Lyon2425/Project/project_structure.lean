import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.RepresentationTheory.Rep

/- This file contains only the statement of the lemmas in section 4 of the
reference and the basic definitions required to state them to highlight
the structure of the project. -/

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

instance : MonoidalPredicate (P k G) := sorry

/-- The monoidal category of finite dimensional representation of `G` over `k` -/
abbrev FinRep := FullSubcategory (P k G)

variable {k G}
variable (X : FinRep k G)

namespace FinRep

def ρ := X.1.ρ
def V := X.1.V

end FinRep

variable (k G)

/-- The monoidal forgetful functor from `FinRep k G` to `ModuleCat k` -/
def F_monoidal :
    MonoidalFunctor (FinRep k G) (ModuleCat k) :=
  (fullMonoidalSubcategoryInclusion _).comp (Action.forgetMonoidal _ _)

/-- The (lax) monoidal forgetful functor from `FinRep k G` to `ModuleCat k` -/
def F := (F_monoidal k G).toLaxMonoidalFunctor


/-- An automorphism of `F k G` is a monoidal natural isomorphism `F k G ⟹ F k G` -/
abbrev AutF := Aut (F k G)

variable (η : AutF k G)

/-- Coercion of `AutF k G` to have the notation `η X` for the component `X` of
 the natural transformation `η` -/
instance : DFunLike (AutF k G) (FinRep k G) (fun X ↦ X.V ⟶ X.V) where
  coe η X := η.hom.app X
  coe_injective' := sorry

variable {k G}

/-- Definition of `T g : AutF k G` by its components -/
def Tapp (g : G) (X : FinRep k G) : (F k G).obj X ≅ (F k G).obj X where
  hom := {
    toFun := X.ρ g
    map_add' := sorry
    map_smul' := sorry
  }
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

-- Note: *lemma 4.2* would appear here but Lean proves it automatically
/-- The function defining `T` -/
def T_app : G → AutF k G := by
  intro g
  apply MonoidalNatIso.ofComponents (Tapp g) sorry

variable (k G) in

-- *lemma 4.1*
/-- The group homomorphism `G →* AutF k G` involved in the main theorem -/
def T : G →* AutF k G where
  toFun := T_app
  map_one' := sorry
  map_mul' := sorry

end Defs

variable {k G}

/-- `π s` is the evaluation map at `s` as an algebra homomorphism -/
def π (s : G) : (G → k) →ₐ[k] k where
  toFun f := f s
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Multiplication map on `G` on the right -/
def r (s : G) := fun g ↦ g * s

variable (k G) in
/-- The representation on `G → k` induced by multiplication on the right in `G` -/
def τᵣ : Representation k G (G → k) where
  toFun s := {
    toFun := fun f ↦ f ∘ (r s)
    map_add' := sorry
    map_smul' := sorry
  }
  map_one' := sorry
  map_mul' := sorry

variable [Fintype G]

variable (k G) in
/-- The representation `(G → k, τᵣ)` induced by multiplication on the right in
`G` as a `FinRep k G` -/
def finrep_r : FinRep k G where
  obj := {
    V := ModuleCat.mk (G → k)
    ρ := τᵣ k G
  }
  property := FiniteDimensional.finiteDimensional_pi k

/-- Evaluation function of `η : AutF k G` at `finrep_r k G` -/
def α (η : AutF k G) := η (finrep_r k G)

-- *lemma 4.4*
lemma T_inj : Function.Injective (T k G) := sorry

-- *lemma 4.5*
lemma lem5 {G : Type u} (φ : ((G → k)) →ₐ[k] k) :
    ∃! (s : G), φ = π s := sorry

-- *lemma 4.6*
def lem6 (η : AutF k G) : ((G → k)) →ₐ[k] ((G → k)) :=
  AlgHom.ofLinearMap (α η) sorry sorry

-- *lemma 4.7*
lemma lem7 (η : AutF k G) :
    ∃! (s : G), α η = (τᵣ k G) s := sorry

-- *lemma 4.8*
lemma lem8 (η₁ η₂ : AutF k G)
    (h : α η₁ = α η₂) : η₁ = η₂ := sorry

-- *proposition 4.11*
lemma T_surj : Function.Surjective (T k G) := sorry

-- *theorem 4.3*
theorem TannakaDuality : Function.Bijective (T k G) := ⟨T_inj, T_surj⟩

example : G ≃* AutF k G :=
  MulEquiv.ofBijective (T k G) TannakaDuality
