import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Subobject.Comma

open CategoryTheory Category

universe u u' v v' w w'

variable {C : Type u} [Category.{v} C]

variable {J : Type w} [Category.{w'} J]

section Generalities
/-
Limits and colimits.

Let `K : J ⥤ C` be a functor. We say that an object `X` of `C` is a limit
of `F` if:
(1) We have morphisms `f j : X ⟶ F.obj j` for every `j : J`.
(2) For every morphism `u : j ⟶ k` in `J`, we have `f j ≫ F.map u = f k`.
(3) Every time we have the data of an object `Y` of `C` and of morphisms
`g j : Y ⟶ F.obj j` such that `g j ≫ F.map u = g k` for every morphism
`u : j ⟶ k` in `J`, there exists a unique `α : Y ⟶ X` such that
`g j = α ≫ f j` for every `j : J`

It will be convenient to package all the information given in (1) and (2)
into something that we will call a `Cone` of `F`. We can make cones into
a category in the "obvious" way, and a limit will be a terminal cone.

Before we do that, let's look at a few examples:

* Terminal objects:
A terminal object of `C` is a limit of the unique functor from the
empty category to `C`. The data of (1) and (2) then collapses to
just "an object `X` of `C`", and condition (3) says: for every
`Y : C`, there exists a unique morphism `Y ⟶ X`.

For example, in `Type u` every one-point type is a terminal object.
-/

#check Limits.isTerminalEquivUnique
#check Limits.IsTerminal.ofUnique

/-
* Products (cf. Mathlib.CategoryTheory.Limits.Shapes.Products):
This is the case where `J` is a discrete category. Giving `F` is
equivalent to giving the function `F.obj : J → C`. The data of (1)
and (2) becomes "an object `X` of `C` and a morphism `p j : X ⟶ F.obj j`
for every `j : J`".

Property (3) says: every time we have an object `Y` and morphisms
`q j : Y ⟶ F.obj j`, there exists a unique `α : X ⟶ Y` such that
`q j = α ≫ p j`.

In the category `Type u` (and algebraic categories like
`Grp`, `AddCommGrp`, `ModuleCat` etc), the usual products are
categorical products.

* A special case of products is that of binary products. This is
when `J` has exactly two objects an dis discrete.
The data of `F` is equivalent
to that of two objects `A, B : C`. The data of (1) and (2)
is equivalent to that of `X : C` and of two maps
`p : X ⟶ A` and `q : X ⟶ B`. Condition (3) says that, if
we have `Y : C` and two maps `p' : Y ⟶ A` and `q' : Y ⟶ B`,
then there exists a unique `α : Y ⟶ X` such that `p' = α ≫ p`
and `q' = α ≫ q`.

In `Type u` (and algebraic categories like
`Grp`, `AddCommGrp`, `ModuleCat` etc),
Cartesian products are binary products.

In mathlib, the type with two elements used for binary products
(and binary coproducts) is called `WalkingPair`, its two
elements are called `left` and `right`.
-/
#print Limits.WalkingPair

/-
So the category `J` will be `Discrete (WalkingPair)` (if we opened
the `Limits` namespace).
-/

/-
* Fiber products:
This is the case where `J` is a preordered type with three elements
`left, right, none` such that `left < none`, `right < none` and
`left, right` are not comparable. This category is called
`WalkingCospan` in mathlib.
-/
#print Limits.WalkingCospan

/-
Giving a functor `K : J ⥤ C` is equivalent to giving two morphisms
`f : A ⟶ C`, `g : B ⟶ C` with the same target. The data of
(1) and (2) is equivalent to that of `X : C` and two morphisms
`p : X ⟶ A`, `q : X ⟶ B` such that `p >> f = q >> g`.

Condition (3) says that, if
we have `Y : C` and two maps `p' : Y ⟶ A` and `q' : Y ⟶ B`
such that `p' ≫ f = q' ≫ g`,
then there exists a unique `α : Y ⟶ X` such that `p' = α ≫ p`
and `q' = α ≫ q`.

In `Type u` (and algebraic categories like
`Grp`, `AddCommGrp`, `ModuleCat` etc), the usual fiber
products are categorical fiber
products: if `f : A ⟶ C` and `g : B ⟶ C`, their usual fiber
product if `{(x, y) : A × B | f x = g y}`.


* Equalizers:
This is the special case of fiber products where the
morphisms `f, g` have the same source. So the category
`J` has two distinct objects `zero` and `one`, and two
distinct morphisms from `zero` to `one`.

This category is called `WalkingParallelPair` in mathlib,
and we can construct functors from it using
`parallelPair`. (Note that this the first example
where `J` is not a preorder.)
-/
#print Limits.WalkingParallelPair

#synth Category Limits.WalkingParallelPair

example {A B : C} (f g : A ⟶ B) : Limits.WalkingParallelPair ⥤ C :=
  Limits.parallelPair f g

/-
In `Type u` (and algebraic categories like
`Grp`, `AddCommGrp`, `ModuleCat` etc), the equalizer of
`f, g : A ⟶ B` is given by `{x : A | f x = g x}`.

* Kernels

If `C` has a notion of zero morphisms, then the kernel of
`f : A ⟶ B` is the equalizer of `f` and of the zero morphism
`0 : A ⟶ B`.

For example, in `AddCommGrp`, the kernel of `f : A ⟶ B` is
`{x : A | f x = 0}`.
-/

/-
There are other special cases, you can find them in
`Mathlib.CategoryTheory.Limits.Shapes`.
-/

/-
Coming back to the general definition of limits, we first
introduce cones over `F`: a term of type `Cone F` is
equivalent to the data of points (1) and (2) above.
The object `X` of (1) is called the *point* of the cone.
-/

#print Limits.Cone

/-
A `c : Cone F` is:
* an object `c.pt` and
* a natural transformation `c.π : c.pt ⟶ F` from the constant `c.pt`
functor to `F`.

So the data required to make a term of type `Cone F` is morphisms
`πⱼ : c.pt ⟶ K j` for all `j : J` such that, for every morphism
`u : j ⟶ k` in `J`, we have`πᵢ ≫ F.map u = πⱼ`.

structure Cone (K : J ⥤ C) where
  /-- An object of `C` -/
  pt : C
  /-- A natural transformation from the constant functor at `X` to `F` -/
  π : (const J).obj pt ⟶ F
-/

example (K : J ⥤ C) (c: Limits.Cone K) {j k : J} (u : j ⟶ k) : 0 = 0 := by
  have := c.pt
  have := c.π
  have := c.π.app j
  have := c.w u
  rfl

/-
A morphism of cones `c ⟶ c'` is a morphism between their points that makes
all the obvious diagrams commute, i.e. a `f : c.pt ⟶ c'.pt` such that,
for every `j : J`, we have `f ≫ c'.π.app j = c.π.app j`.
-/

example (K : J ⥤ C) (c c' : Limits.Cone K) (f : c ⟶ c') : 0 = 0 := by
  have := f.hom
  have := f.w
  rfl

/-
We cannot talk about *the* limit of a functor, because the limits is
only unique up to unique isomorphism (it satisfies a universal property);
also, being a limit is a property of the cone, not just its point.
So we define a structure `IsLimit` that says that a cone is a limit cone.
-/
#check Limits.IsLimit

/-
/-- A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
cone morphism to `t`. -/

structure IsLimit (t : Cone F) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : ∀ s : Cone F, s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations
  commute -/
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by aesop_cat
  /-- It is the unique such map to do this -/
  uniq : ∀ (s : Cone F) (m : s.pt ⟶ t.pt)
      (_ : ∀ j : J, m ≫ t.π.app j = s.π.app j), m = lift s := by aesop_cat
-/

/-
Then we have theorems saying that a limit cone is unique up to
(unique) isomorphism.
-/

#check Limits.IsLimit.uniqueUpToIso

/-
Colimits are "the same" except that you revert the direction of
every morphism. So we get a categorical definition of initial objects
(the empty type for types, the trivial group/abelian group/module, etc),
coproducts (also called "disjoint union" for types, "free products"
for groups, and "direct sums" for modules), binary coproducts, pushouts,
coequalizers, cokernels etc.

Unlike limits, colimits generally have different definitions in
the various algebraic categories.
-/

end Generalities

/- Let's do some exercises to learn to manipulate (co)limits, and
let's open the namespace `Limits` to shorten the declarations.
-/

open Limits

variable {D : Type u'} [Category.{v'} D] (G : D ⥤ C)

section Preserves
/- Here we prove that a right adjoint functor preserves all limits.
We also want to show this for big limits, so we use different universes
for the indexing category of the limits.
-/
#check J
#synth Category J

#check Functor.leftAdjoint
#check Adjunction.ofIsRightAdjoint
#check Cones.postcompose
#check Functor.mapCone
#check whiskerLeft
#check IsLimit.hom_ext

noncomputable def RightAdjointPreservesLimit [G.IsRightAdjoint]
    {J : Type w} [Category.{w'} J] (K : J ⥤ D) : PreservesLimit K G where
  preserves {c} (hc) := by
    set adj := Adjunction.ofIsRightAdjoint G
    refine IsLimit.mk (fun s ↦ ?_) (fun s j ↦ ?_) (fun s m eq ↦ ?_)
    · dsimp
      sorry
    · sorry
    · sorry

end Preserves

-- This is a lemma from `Categories1`, useful in the next two sections.
lemma IsRightAdjointIffInitial :
    G.IsRightAdjoint ↔ ∀ (X : C),
    HasInitial (StructuredArrow X G) := sorry


section GeneralAdjointFunctorTheorem

/-
The general adjoint functor theorem says that, if `D` has all small
limits, `G` commutes with these limits, and `G` satisfies the
solutions set condition, then `G` has a left adjoint.

Here a small limit means a limit indexed by a category
`J` such that the object type and hom types of `J`
are `v'`-small, where `v'` is the universe level of the
hom types of `C`, and "`v'`-small" means "in bijection with
a type in `Type v'`".

(Handling the size conditions is somewhat of a pain, since
in informal mathematics both categories in the adjoint
functor theorem live in the same universe, but here they
don't. But we manage.)
-/
#print Small

/-
The solution set condition is the following condition on
`G`: for every `X : C`, there exists a `v'`-small type
`I` and a function `y : I → StructuredArrow X G`
(remember that `y i` is a morphism
`(y i).hom : X ⟶ G.obj (y i).right`) such
that, for every `f : X ⟶ G.obj Y` in `StructuredArrow X G`,
there exists `i : I`, `g : (y i).right ⟶ Y` with
`f = (y i).hom ≫ G.map g`.

The idea of the proof is that, under the conditions
of the theorem, every category `StructuredArrow X G`
will have an initial object.
-/

#check hasInitial_of_unique

/-
If a category `C` with hom types in `Type v` has small limits
and admits a family
of objects `x : I → C` with `I` a `v`-small type such that
every `X : C` admits at least one morphism from one of the
`x i`, then `C` has an initial object.

(We will later apply this to the categories `StructuredArrow X G`.)

Useful lemmas and defs:
-/
#check Limits.hasInitial_of_unique
#check Unique.mk'
#check Inhabited.mk
#check Subsingleton.intro
#check limit
#check wideEqualizer
#check WalkingParallelFamily
#check parallelFamily
#check equalizer
#check WalkingParallelPair
#check parallelPair
#check Limits.Pi.π
#check Mono
#check cancel_mono
#check Epi
#check epi_of_epi_fac
#check eq_of_epi_equalizer

/-
In the next proof, we use the notion of "monomorphism". This is a
categorical version of injectivity for a morphism: a morphism
`f : X ⟶ Y` is called a monomorphism (`Mono` in lean) if, for
every object `Z` and all `g, h : Z ⟶ X`, if `g ≫ f = h ≫ f`, then
`g = h`.

The dual notion, which generalizes surjectivity, is that of an
epimorphism (`Epi` in lean) : a morphism `f : X ⟶ Y` is called an
epimorphism every object `Z` and all `g, h : Y ⟶ Z`,
if `f ≫ g = f ≫ h`, then `g = h`.
-/

lemma InitialOfFamily [HasLimits C] {I : Type*} (x : I → C)
    (wi : ∀ (X : C), ∃ (i : I), Nonempty (x i ⟶ X)) [Small.{v} I] :
    HasInitial C := by
  have := Discrete.essentiallySmallOfSmall (α := I)
  have := hasLimitsOfShape_of_essentiallySmall (Discrete I) C
  -- We first establish that limits indexed by `I` exist in `C`. As `I`
  -- is not in `Type v` but only `v`-small, this takes a couple of
  -- lemmas.
  set X := ∏ᶜ x -- this is the notation for the product of a family
  set Y := wideEqualizer (fun (u : X ⟶ X) ↦ u)
  -- The idea is to take as initial object the equalizer of all the
  -- endomorphisms of `X`, where `X` is the product of the family `x`.
  -- Here we use `wideEqualizer`, which is similar to `equalizer`
  -- but for an arbitrary family of morphisms (`equalizer` is just the
  -- equalizer of two morphisms). Wide equalizers are limits indexed by
  -- the category `WalkingParallelFamily`.
  have IX : ∀ (A : C), Inhabited (X ⟶ A) := by
    intro A
  -- First we show that every `A : C` admits a morphism from `X`.
  -- This is because `A` admits a morphism from some `x i`, and we
  -- have projection morphisms from `X` to all the `x i`.
    sorry
  have : ∀ (A : C), Unique (Y ⟶ A) := by
    intro A
    refine @Unique.mk' _ ?_ ?_
  -- Then we prove that each `A : C` admits a unique morphism from `Y`.
    · sorry
  -- For the existence, we use tha fact that there exists a morphism
  -- `i : Y ⟶ X`.
    · refine Subsingleton.intro (fun f g ↦ ?_)
      sorry
  -- For the uniqueness, suppose that we have `f, g : Y ⟶ A`.
  -- We take `j : Z ⟶ Y` the equalizer of `f` and `g`.
  -- Then `i ≫ k ≫ j ≫ i = i` because `Y` is the (wide) equalizer of
  -- all the morphisms `X ⟶ X`, so `(i ≫ k) ≫ j = 𝟙 Y` because `i`
  -- is a monomorphism (see `Mono`), so `j` is an epimorphism (`Epi`),
  -- which implies that `f = g` because `j` is the equalizer of `f` and `g`.
  exact hasInitial_of_unique Y

/-- The solution set condition : for every `X : C`, there exists a
small familly `y : I → D` and morphisms `f i : X ⟶ G.obj (y i)` such that
each morphism `X ⟶ G.obj Y` factors as `f i ≫ G.map g` for some `i` and
some `g : y i ⟶ Y`.
-/
def SolutionSetCondition := ∀ (X : C), ∃ (I : Type u) (_ : Small.{v'} I)
  (y : I → D) (f : (i : I) → (X ⟶ G.obj (y i))), ∀ (Y : D) (h : X ⟶ G.obj Y),
  ∃ (i : I) (g : y i ⟶ Y), h = f i ≫ G.map g

/--
The general adjoint functor theorem: if `G` satisfies the solution set
condition and preserves small limits, and if `C` and `D` have all small
limits, then `G` has a left adjoint.
-/
theorem GeneralAdjointFunctor [HasLimits D]
    [PreservesLimitsOfSize.{v', v'} G]
    (h : SolutionSetCondition G) : G.IsRightAdjoint := by
  rw [IsRightAdjointIffInitial]
  intro X
  sorry
  -- We also the previous lemma to show that `StructuredArrow X G`
  -- has an initial object.

end GeneralAdjointFunctorTheorem


section SpecialAdjointFunctorTheorem

/-
The special adjoint functor theorem says that, if
`D` has small limits, `G` commutes with small limits,
`D` is well-powered for `v'` and has a `v'`-small
cogenerating family, and `C` has `v'`-small hom types,
then `G` has a left adjoint.

A cogenerating family for `D` is a family `y : I → D`
such that, for all `Y, Y' : D` and `f,g : Y ⟶ Y'`,
if `f ≫ h = g ≫ h` for every `i : I` and every
`h : Y ⟶ y i`, then `f = g`.
We say that it is `v'`-small if `I` is 'v'`-small.
-/

/-
To explain the "well-powered" condition, we need a few definitions.

Let `X : C`. We have the category `MonoOver X` of monomorphisms `Y ⟶ X`.
Note that `i : Y ⟶ X` and `i' : Y' ⟶ X` are isomorphic in `MonoOver X`
if and only if there exists an isomorphism `u : Y ⟶ Y'`
such that `i = u ≫ i'`.

The category of subobjects of `X` is a skeleton of `MonoOver X`, i.e.
it is a subcategory that contains exactly one object in each isomorphism
class.
-/

#print Subobject

/- A category `C` is well-powered relative to a
universe `w` if it is `w`-locally small (i.e. its hom types are
`w`-small) and `Subobject X` is `w`-small for every `X`.
-/

/- If `C` has small limits and `X : C` is such that `Subobject X` is
`v`-small (where `v` is the universe level of the hom types of `C`),
then we can form a "minimal subobject" of `X` by taking the limit of
all subobjects of `X`. We will actually take the limit over `MonOver X`
(which is equivalent to `Subobject X`), as this is easier.
-/

local instance [HasLimits C] (X : C) [Small.{v} (Subobject X)] :
    EssentiallySmall.{v} (MonoOver X) :=
  (essentiallySmall_monoOver_iff_small_subobject X).mpr inferInstance
-- If `Subobject X` is `v`-small, then `MonoOver X` is
-- essentially small, i.e. equivalent to a `v`-small category.
-- (This holds because `Subobject X` and `MonoOver X` are equivalent
-- categories.)

local instance [HasLimits C] (X : C) [Small.{v} (Subobject X)] :
    HasLimitsOfShape (MonoOver X) C :=
  hasLimitsOfShape_of_essentiallySmall (MonoOver X) C
-- If `Subobject X` is `v`-small and `C` has `v`-small limits, then
-- it has limits indexed by `MonoOver X`.

noncomputable def MinimalSubobject [HasLimits C] (X : C)
    [Small.{v} (Subobject X)] : C :=
  limit (MonoOver.forget X ⋙ Over.forget X)
-- The "minimal subobject" of `X` is the limit ("intersection") of
-- all subobjects of `X`.

/--
The canonical monomorphism `MinimalSubobject X ⟶ X`.
-/
noncomputable def MinimalSubobjectTo [HasLimits C] (X : C)
    [Small.{v} (Subobject X)] : MinimalSubobject X ⟶ X :=
  limit.π (MonoOver.forget X ⋙ Over.forget X) (MonoOver.mk' (𝟙 X))

-- The morphism `MinimalSubobject X ⟶ X` is a monomorphism.
#print Mono
#print cancel_mono
#print limit.hom_ext

local instance [HasLimits C] (X : C)
    [Small.{v} (Subobject X)] : Mono (MinimalSubobjectTo X) where
  right_cancellation {Y} f g eq := by
    dsimp [MinimalSubobject]
    sorry

/-- The minimality property: every monomorphism into `MinimalSubobject X`
is an isomorphism. Indeed, if `u : Y ⟶ MinimalSubobject X` is a
monormorphism, then we get a subobject of `X` by taking the composition
`Y ⟶ MinimalSubobject X ⟶ X`. So we have a "projection" morphism
`MinimalSubobject X ⟶ Y`, which will be the inverse of `u`.
-/
lemma MinimalSubobjectIsMinimal [HasLimits C] (X : C)
    [Small.{v} (Subobject X)] {Y : C} (u : Y ⟶ MinimalSubobject X)
    [Mono u] : IsIso u := by
  set j := MonoOver.mk' (u ≫ MinimalSubobjectTo X)
  set v : MinimalSubobject X ⟶ Y :=
    limit.π (MonoOver.forget X ⋙ Over.forget X) j
  have eq : u ≫ v = 𝟙 Y := by
    sorry
  have eq' : v ≫ u = 𝟙 (MinimalSubobject X) := by
    sorry
  exact {out := ⟨v, eq, eq'⟩}

/--
A cogenerating family is a family `x : I → C` of objects of `C` such that,
for all `X,Y : C` and `f,g : X ⟶ Y`, if `f ≫ h = g ≫ h` for every `i : I`
and every `h : Y ⟶ x i`, then `f = g`.
-/
def IsCogenerating {I : Type*} (x : I → C) := ∀ {X Y : C} (f g : X ⟶ Y),
  f = g ↔ ∀ (i : I) (h : Y ⟶ x i), f ≫ h = g ≫ h

variable {I : Type*} (x : I → C)

local instance [Small.{v} I] [HasLimits C] :
    HasLimitsOfShape (Discrete I) C :=
  letI := Discrete.essentiallySmallOfSmall (α := I)
  hasLimitsOfShape_of_essentiallySmall (Discrete I) C
-- If `I` is `v`-small and `C` has limits indexed by
-- categories in `Type v`, then `C` has limits indexed
-- by `I`.

-- If `x : I → C` and `X : C`, this is the "obvious" morphism
-- from `X` to the product `P` of the `(x i)^(X ⟶ x i)` (where this
-- last notation denotes the product of the constant family
-- `x i` indexed by `X ⟶ x i`).
-- If we were in `Type`, it would send each `x : X` to the
-- family whose `i`th coordinate is `(f x)_{f : X ⟶ x i}`.
-- Here we construct it using the universal property of products:
-- giving a morphism `X ⟶ P` is equivalent (via `Pi.lift`) to
-- giving a morphism `X ⟶ (x i)^(X ⟶ x i)` for every `i`.
-- Giving a morphism `X ⟶ (x i)^(X ⟶ x i)` is equivalent
-- (again by `Pi.lift`) to giving a morphism `X ⟶ x i` for
-- every `f : X ⟶ x i`, and there is an obvious choice : `f` itself.

#check Pi.lift

noncomputable abbrev CogeneratingMono [Small.{v} I] [HasLimits C] (X : C) :
    X ⟶ ∏ᶜ (fun (i : I) ↦ (∏ᶜ fun (_ : X ⟶ x i) ↦ x i)) :=
  Pi.lift (fun _ ↦ (Pi.lift (fun u ↦ u)))

-- If `x : I → C` is cogenerating, then the morphism of the previous
-- definition is a monomorphism.
lemma CogeneratingMonoIsMono [Small.{v} I] (h : IsCogenerating x)
    [HasLimits C] (X : C) : Mono (CogeneratingMono x X) where
  right_cancellation {Y} f g eq := by
    sorry

/--
We prove that if `C` is well-powered relative to `v` (the universe
level of its hom types) and has all `v`-small limits and a small
cogenerating family, then it admits an initial object.
(We will later apply this to comma categories `StructuredArrow X G`).

The idea is to take the minimal subobject (`MinimalSubobject`) of
the product of the family `x`.
Let `A : C`.
If we have two morphisms `f, g : e ⟶ A`, then
their equalizer is a subobject of `e`, hence isomorphic to
`e` by a previous lemma, hence `f = g`.
Now we construct a morphism `e ⟶ A`. First we consider the "diagonal map"
`u : ∏ᶜ x ⟶ ∏ᶜ (fun (i : I) ↦ (∏ᶜ fun (_ : A ⟶ x i) ↦ x i))` (the codomain
of `CogeneratingMono x A`, and we take `B` equal to the pullback of
`u` and of `CogeneratingMono x A`. As the pullback of a monomorphism
is a monomorphism, the second projection `B ⟶ ∏ᶜ x` is a monomorphism,
so we get a morphism `e ⟶ B` by the universal property of the
minimal subobject. We compose this by the first projection
`B ⟶ A` to get the desired morphism.
-/
lemma HasInitialOfWellPowered [WellPowered.{v} C] [HasLimits C] {I : Type*}
    [Small.{v} I] (x : I → C) (h : IsCogenerating x) :
    HasInitial C := by
  have := Discrete.essentiallySmallOfSmall (α := I)
  have := hasLimitsOfShape_of_essentiallySmall (Discrete I) C
  -- Again some incantations to make sure we have limits indexed by `I`.
  set X := ∏ᶜ x
  set e := MinimalSubobject X
  have : ∀ (A : C), Subsingleton (e ⟶ A) := by
    intro _
    refine Subsingleton.intro (fun f g ↦ ?_)
    sorry
  have : ∀ (A : C), Inhabited (e ⟶ A) := by
    intro A
    refine Inhabited.mk ?_
    set u : ∏ᶜ x ⟶ ∏ᶜ (fun (i : I) ↦ (∏ᶜ fun (_ : A ⟶ x i) ↦ x i)) :=
      Pi.map (fun _ ↦ (Pi.lift (fun _ ↦ 𝟙 _)))
    set B := pullback (CogeneratingMono x A) u
    sorry
  have : ∀ (A : C), Unique (e ⟶ A) := fun A ↦ Unique.mk' _
  exact hasInitial_of_unique e

-- If `y : I → D` is cogenerating and if `X : C`, then the family of
-- all morphisms `X ⟶ G.obj (y i)` is cogenerating in `StructuredArrow X
#check StructuredArrow.hom_eq_iff
#check StructuredArrow.comp_right
#check StructuredArrow.homMk

lemma IsCogeneratingOfIsCogenerating (y : I → D) (h : IsCogenerating y)
    (X : C) :
    IsCogenerating (fun (a : Σ (i : I), X ⟶ G.obj (y i)) ↦
    StructuredArrow.mk a.2) := by
  intro a b u v
  sorry

#check StructuredArrow.hasLimitsOfSize

/-
Proof of the special adjoint theorem: under our hypotheses,
the categories `StructuredArrow X G` have small limits,
are well-powered and have small cogenerating families, hence
they have initial objects.
-/
theorem SpecialAdjointFunctor [HasLimits D] [WellPowered.{v'} D]
    [PreservesLimitsOfSize.{v', v'} G] [LocallySmall.{v'} C]
    (cogen : ∃ (I : Type*) (y : I → D) (_ : Small.{v'} I), IsCogenerating y) :
    G.IsRightAdjoint := by
  rw [IsRightAdjointIffInitial]
  intro X
  obtain ⟨I, y, hs, h⟩ := cogen
  refine @HasInitialOfWellPowered _ _ ?_ ?_ _ ?_ _
    (IsCogeneratingOfIsCogenerating G y h X)
  · sorry -- try to use `StructuredArrow.wellPowered_structuredArrow`
  · sorry -- here the helpful one is `StructuredArrow.hasLimitsOfSize`
  · sorry -- use `small_sigma`

end SpecialAdjointFunctorTheorem


section GroupObject

/-
To play with limits some more, we will look at the notion of
group objects in a category `C` that admits finite products.
This is a categorical definition of groups.

The idea is that a group object in `C` is the data of:
- An object of `C`, let's call it `X`.
- A "multiplication" map, which should be a morphism `X ⨯ X ⟶ X`.
(Here `⨯` is a notation for the categorical product, typed using
"\ + X".)
- An "inversion" map, which should be a morphism `X ⟶ X`.
- A "unit": If `X` were a type, the unit would be an element of
`X`, but this does not make sense here. Instead, we will ask
for a morphism `⊤_ C ⟶ X`, where `⊤_ C` is a terminal object of `C`.
(If `C` is `Type u`, then `⊤_ C` is a one-point type, so giving a
morphism `⊤_ C ⟶ X` is the same as giving an element of `X`.)
(Type `⊤` using "\ + top".)

Of course, these data should satisfy some axioms, such as associativity
of multiplication, the fact that the unit is a unit, etc. The insight
is that we can express all of these axioms categorically, as
equalities betweem some morphisms.
-/

variable (C : Type u) [Category.{v} C]

variable [HasFiniteProducts C]

structure GroupObject where
  X : C
  mul : X ⨯ X ⟶ X    -- type ⨯ using \ + X
  mul_assoc : prod.map mul (𝟙 X) ≫ mul =
      (prod.associator X X X).hom ≫ prod.map (𝟙 X) mul ≫ mul
  one : ⊤_ C ⟶ X -- type `⊤` using \ + top
  one_mul : (prod.leftUnitor X).inv ≫ prod.map one (𝟙 X) ≫ mul = 𝟙 X
  mul_one : (prod.rightUnitor X).inv ≫ prod.map (𝟙 X) one ≫ mul = 𝟙 X
  inv : X ⟶ X
  inv_mul_cancel : prod.lift inv (𝟙 X) ≫ mul = terminal.from X ≫ one
-- Note that we chose a minimal list of axioms. There should also be
-- a `mul_inv_cancel` for example, but it can be deduced from the
-- other axioms.

-- Category structure on group objects.
instance : Category (GroupObject C) where
  Hom G G' := {f : G.X ⟶ G'.X | G.one ≫ f = G'.one ∧
    prod.map f f ≫ G'.mul = G.mul ≫ f}
  id G := ⟨𝟙 G.X, by simp⟩
  comp f g := ⟨f.1 ≫ g.1, ⟨sorry, sorry⟩⟩

-- The forgetful functor from group objects in `C` to `C`.
def GroupObjectForget : GroupObject C ⥤ C where
  obj G := G.X
  map f := f.1

/-
Our next goal is to show that group objects in the category `Type u`
are just groups. (In fact, we will construct an equivalence of
categories `GroupObject (Type u) ≌ Grp.{u}`.) To simplify the proofs,
we use some lemmas about products in `Type u`.
-/

section Lemmas

#check prod.map_fst
#check prod.map_snd
#check prod.lift_fst
#check prod.lift_snd

lemma prod.map_fst_apply {A B C D : Type u} (f : A ⟶ B) (g : C ⟶ D)
    (x : A ⨯ C) :
    prod.fst (X := B) (prod.map f g x) = f (prod.fst (X := A) x) := by
  sorry

lemma prod.map_snd_apply {A B C D : Type u} (f : A ⟶ B) (g : C ⟶ D)
    (x : A ⨯ C) :
    prod.snd (X := B) (prod.map f g x) = g (prod.snd (X := A) x) := by
  sorry

lemma prod.lift_fst_apply {A B C : Type u} (f : A ⟶ B) (g : A ⟶ C) (x : A) :
    prod.fst (X := B) (prod.lift f g x) = f x := by
  sorry

lemma prod.lift_snd_apply {A B C : Type u} (f : A ⟶ B) (g : A ⟶ C) (x : A) :
    prod.snd (X := B) (prod.lift f g x) = g x := by
  sorry

end Lemmas

/- If `G` is a group object in `Type u`, then `G.X` gets a canonical
`Group` instance. We define this instance bit by bit as usual: first
we introduce the `Mul`, `Inv` and `One` instances, then we prove
their properties.

For example, the `Mul` seems easy, because it is just a map
`G.X × G.X → G.X`, i.e. a morphism `G.X × G.X ⟶ G.X` in the category
`Type u`, and we have a morphism `G.X ⨯ G.X ⟶ G.X` given by `G.mul`.
Similary, the unit element of `G.X` is the image of the unique
element of `⊤_ (Type u)` by `G.one`.

However, there is a technical complication: the categorical product
`G.X ⨯ G.X` in `Type u` (chosen by the axiom of choice among all binary
products) is NOT the Cartesian product `G.X × G.X`, it is only isomorphic
to it, etc.

(In fact, this shows that our definitio of group objects is not
the right one. There is a class called `ChosenFiniteProducts` which
allows us to choose "nice" representatives in a category such as
`Type u`, and we should use the finite products given by this class
to define group objects. I didn't do this because I wanted to torture
you a bit. End of digression.)
-/

#check Types.binaryProductIso

/- We will use that `⊤_ (Type u)` has a unique element, which
is called `default`.
It also has a `Subsingleton` insteance, so to prove that two of its
elements are equal, you can use this: -/
#check Subsingleton.elim
#print Subsingleton

noncomputable instance (G : GroupObject (Type u)) : Mul G.X where
  mul x y := G.mul ((Types.binaryProductIso G.X G.X).inv ⟨x, y⟩)

noncomputable instance (G : GroupObject (Type u)) : One G.X where
  one := G.one default

noncomputable instance (G : GroupObject (Type u)) : Inv G.X where
  inv x := G.inv x

noncomputable instance (G : GroupObject (Type u)) : Group G.X where
  mul_assoc x y z := by
    dsimp [HMul.hMul, Mul.mul]
    have eq : G.mul ((Types.binaryProductIso G.X G.X).inv (G.mul
        ((Types.binaryProductIso G.X G.X).inv (x, y)), z)) =
        (prod.map G.mul (𝟙 G.X) ≫ G.mul) ((Types.binaryProductIso _ _).inv
        ⟨(Types.binaryProductIso G.X G.X).inv ⟨x, y⟩, z⟩) := by
      simp only [types_comp_apply]
      refine congrArg G.mul ?_
      refine (Types.binaryProductIso G.X G.X).toEquiv.injective ?_
      ext
      · simp only [Iso.toEquiv_fun, inv_hom_id_apply, Types.binaryProductIso_hom_comp_fst_apply]
        rw [prod.map_fst_apply]
        simp only [types_comp_apply, Types.binaryProductIso_inv_comp_fst_apply]
      · simp only [Iso.toEquiv_fun, inv_hom_id_apply, Types.binaryProductIso_hom_comp_snd_apply]
        rw [prod.map_snd_apply]
        simp only [types_comp_apply, Types.binaryProductIso_inv_comp_snd_apply, types_id_apply]
    rw [eq, G.mul_assoc]
    dsimp
    refine congrArg G.mul ?_
    refine (Types.binaryProductIso G.X G.X).toEquiv.injective ?_
    ext
    · simp only [Iso.toEquiv_fun, Types.binaryProductIso_hom_comp_fst_apply, inv_hom_id_apply]
      rw [prod.map_fst_apply, prod.lift_fst_apply]
      simp only [types_comp_apply, Types.binaryProductIso_inv_comp_fst_apply, types_id_apply]
    · simp only [Iso.toEquiv_fun, Types.binaryProductIso_hom_comp_snd_apply, inv_hom_id_apply]
      rw [prod.map_snd_apply, prod.lift_snd_apply]
      refine congrArg G.mul ?_
      refine (Types.binaryProductIso G.X G.X).toEquiv.injective ?_
      ext
      · simp only [Iso.toEquiv_fun, Types.binaryProductIso_hom_comp_fst_apply, inv_hom_id_apply]
        rw [prod.lift_fst_apply]
        simp only [types_comp_apply, Types.binaryProductIso_inv_comp_fst_apply,
          Types.binaryProductIso_inv_comp_snd_apply]
      · simp only [Iso.toEquiv_fun, Types.binaryProductIso_hom_comp_snd_apply, inv_hom_id_apply]
        rw [prod.lift_snd_apply]
        simp only [Types.binaryProductIso_inv_comp_snd_apply]
  one_mul x := by
    dsimp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one]
    have eq : (Types.binaryProductIso G.X G.X).inv (G.one default, x) =
        prod.map G.one (𝟙 G.X) ((prod.leftUnitor G.X).inv x) := by
      refine (Types.binaryProductIso G.X G.X).toEquiv.injective ?_
      simp only [Iso.toEquiv_fun, inv_hom_id_apply, prod.leftUnitor_inv]
      ext
      · simp only [Types.binaryProductIso_hom_comp_fst_apply]
        rw [prod.map_fst_apply]
        refine congrArg G.one ?_
        rw [prod.lift_fst_apply]
        exact Subsingleton.elim _ _
      · simp only [Types.binaryProductIso_hom_comp_snd_apply]
        rw [prod.map_snd_apply]
        simp only [types_comp_apply, types_id_apply]
        rw [prod.lift_snd_apply]
        simp only [types_id_apply]
    rw [eq]
    change ((prod.leftUnitor G.X).inv ≫ prod.map G.one (𝟙 G.X) ≫ G.mul) _ = _
    rw [G.one_mul]
    simp
  mul_one x := by
    dsimp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one]
    have eq : (Types.binaryProductIso G.X G.X).inv (x, G.one default) =
        prod.map (𝟙 G.X) G.one ((prod.rightUnitor G.X).inv x) := by
      refine (Types.binaryProductIso G.X G.X).toEquiv.injective ?_
      simp only [Iso.toEquiv_fun, inv_hom_id_apply, prod.leftUnitor_inv]
      ext
      · simp only [prod.rightUnitor_inv, Types.binaryProductIso_hom_comp_fst_apply]
        rw [prod.map_fst_apply]
        simp only [types_comp_apply, types_id_apply]
        rw [prod.lift_fst_apply]
        simp only [types_id_apply]
      · simp only [Types.binaryProductIso_hom_comp_snd_apply]
        rw [prod.map_snd_apply]
        simp only [prod.rightUnitor_inv]
        refine congrArg G.one ?_
        exact Subsingleton.elim _ _
    rw [eq]
    change ((prod.rightUnitor G.X).inv ≫ prod.map (𝟙 G.X) G.one ≫ G.mul) _ = _
    rw [G.mul_one]
    simp
  inv_mul_cancel x := by
    dsimp [HMul.hMul, Mul.mul, Inv.inv]
    have eq : G.mul ((Types.binaryProductIso G.X G.X).inv (G.inv x, x)) =
        (prod.lift G.inv (𝟙 G.X) ≫ G.mul) x := by
      simp only [types_comp_apply]
      refine congrArg G.mul ?_
      refine (Types.binaryProductIso G.X G.X).toEquiv.injective ?_
      simp only [Iso.toEquiv_fun, inv_hom_id_apply]
      ext
      · simp only [Types.binaryProductIso_hom_comp_fst_apply]
        rw [prod.lift_fst_apply]
      · simp only [Types.binaryProductIso_hom_comp_snd_apply]
        rw [prod.lift_snd_apply]
        simp only [types_id_apply]
    rw [eq, G.inv_mul_cancel]
    change _ = G.one default
    simp only [types_comp_apply, PUnit.default_eq_unit]
    refine congrArg G.one ?_
    exact Subsingleton.elim _ _

/-
If `f : G ⟶ G'` is a morphism of group objects in `Type u`, this
constructs the corresponding morphism of groups from `G.X` to `G'.X`.
-/
@[simp]
def MonoidHomOfHom {G G' : GroupObject (Type u)} (f : G ⟶ G') :
    G.X →* G'.X where
      toFun := f.1
      map_one' := by
        change (G.one ≫ f.1) default = 1
        rw [f.2.1]
        rfl
      map_mul' x y := by
        dsimp [HMul.hMul, Mul.mul]
        change (G.mul ≫ f.1) _ = _
        rw [← f.2.2]
        simp only [Set.mem_setOf_eq, types_comp_apply]
        refine congrArg G'.mul ?_
        refine (Types.binaryProductIso G'.X G'.X).toEquiv.injective ?_
        simp only [Iso.toEquiv_fun, inv_hom_id_apply]
        ext
        · simp only [Types.binaryProductIso_hom_comp_fst_apply]
          rw [prod.map_fst_apply]
          simp only [Set.mem_setOf_eq, types_comp_apply, Types.binaryProductIso_inv_comp_fst_apply]
        · simp only [Types.binaryProductIso_hom_comp_snd_apply]
          rw [prod.map_snd_apply]
          simp only [Set.mem_setOf_eq, types_comp_apply, Types.binaryProductIso_inv_comp_snd_apply]

-- The functor from `GroupObject (Type u)` to `Grp.{u}` sending
-- `G` to `G.X` with the group structure defined above.
noncomputable def CanIso : GroupObject (Type u) ⥤ Grp.{u} where
  obj G := Grp.of G.X
  map f := Grp.ofHom (MonoidHomOfHom f)
  map_id X := by
    dsimp
    ext
    simp only [Grp.coe_of, Grp.coe_id', id_eq]
    rfl
  map_comp f g := by
    dsimp
    ext
    simp only [Grp.coe_of]
    rfl

/- The functor in the other direction: if `G` is a group, then
it defines a group object in `Type u`, because we have a morphism
`G × G → G` defined by the multiplication, etc. However, there is
the same technical complication as before: the categorical product
`G ⨯ G` in `Type u` is NOT the Cartesian product `G × G`, it is only
isomorphic to it, etc.
-/
#check Types.binaryProductIso

-- Every group defines a group object in `Type u`.
@[simp]
noncomputable def GroupObjectOfGrp (G : Type u) [Group G] :
    GroupObject (Type u) where
  X := G
  mul p := ((Types.binaryProductIso G G).hom p).1 * ((Types.binaryProductIso G G).hom p).2
  mul_assoc := by
    dsimp
    ext
    simp only [Types.binaryProductIso_hom_comp_fst_apply, Types.binaryProductIso_hom_comp_snd_apply,
      types_comp_apply]
    rw [prod.map_fst_apply, prod.map_snd_apply, prod.map_fst_apply, prod.map_snd_apply,
      prod.lift_fst_apply, prod.lift_snd_apply, prod.lift_fst_apply, prod.lift_snd_apply]
    simp only [types_id_apply, types_comp_apply]
    rw [mul_assoc]
  one _ := 1
  one_mul := by
    dsimp
    ext
    simp only [Types.binaryProductIso_hom_comp_fst_apply, Types.binaryProductIso_hom_comp_snd_apply,
      types_comp_apply, types_id_apply]
    rw [prod.map_fst_apply, prod.map_snd_apply, one_mul, prod.lift_snd_apply]
    simp only [types_id_apply]
  mul_one := by
    dsimp
    ext
    simp only [Types.binaryProductIso_hom_comp_fst_apply, Types.binaryProductIso_hom_comp_snd_apply,
      types_comp_apply, types_id_apply]
    rw [prod.map_fst_apply, prod.lift_fst_apply, prod.map_snd_apply, mul_one]
    simp only [types_id_apply]
  inv x := x⁻¹
  inv_mul_cancel := by
    ext
    simp only [Types.binaryProductIso_hom_comp_fst_apply, Types.binaryProductIso_hom_comp_snd_apply,
      types_comp_apply]
    rw [prod.lift_fst_apply, prod.lift_snd_apply]
    simp only [types_id_apply, inv_mul_cancel]

-- Every morphism of groups defines a morphism of group objects.
@[simp]
noncomputable def HomOfMonoidHom {G G' : Type u} [Group G] [Group G']
    (f : G →* G') : GroupObjectOfGrp G ⟶ GroupObjectOfGrp G' where
      val := f.toFun
      property := by
        constructor
        · aesop
        · ext
          dsimp
          simp only [Types.binaryProductIso_hom_comp_fst_apply,
            Types.binaryProductIso_hom_comp_snd_apply, map_mul]
          rw [prod.map_fst_apply, prod.map_snd_apply]

-- Putting all this together into a functor.
noncomputable def CanIsoInv : Grp.{u} ⥤ GroupObject (Type u) where
  obj G := GroupObjectOfGrp G.1
  map f := HomOfMonoidHom f
  map_id G := by
    dsimp
    rw [← SetCoe.ext_iff]
    ext
    rfl
  map_comp f g := by
    dsimp
    rw [← SetCoe.ext_iff]
    ext
    rfl

/-
To get an equivalence, we now need to define isomorphisms of functors
`𝟭 (GroupObject (Type u)) ≅ CanIso ⋙ CanIsoInv` and
`CanIsoInv ⋙ CanIso ≅ 𝟭 Grp.{u}`. These morphisms are basically given
by the identity, but we do have to check the compatibility with the
various group/group object structures.
-/

noncomputable def CanUnit : 𝟭 (GroupObject (Type u)) ≅ CanIso ⋙ CanIsoInv := by
  refine NatIso.ofComponents (fun G ↦ ?_) (fun f ↦ ?_)
  · dsimp [CanIso, CanIsoInv]
    refine {hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_}
    · refine {val := 𝟙 G.X, property := ⟨?_, ?_⟩}
      · dsimp
        ext
        change _ = G.one default
        simp only [types_comp_apply, types_id_apply]
        refine congrArg G.one ?_
        refine Types.terminalIso.toEquiv.injective ?_
        simp only [Iso.toEquiv_fun, inv_hom_id_apply]
      · dsimp
        ext
        simp only [prod.map_id_id, Types.binaryProductIso_hom_comp_fst_apply,
          Types.binaryProductIso_hom_comp_snd_apply, types_comp_apply, types_id_apply]
        change G.mul ((Types.binaryProductIso G.X G.X).inv _) = _
        refine congrArg G.mul ?_
        refine (Types.binaryProductIso _ _).toEquiv.injective ?_
        ext
        · simp only [Iso.toEquiv_fun, inv_hom_id_apply, Types.binaryProductIso_hom_comp_fst_apply]
        · simp only [Iso.toEquiv_fun, inv_hom_id_apply, Types.binaryProductIso_hom_comp_snd_apply]
    · refine {val := 𝟙 G.X, property := ⟨?_, ?_⟩}
      · dsimp
        ext
        simp only [types_comp_apply, types_id_apply]
        change G.one default = _
        refine congrArg G.one ?_
        refine Types.terminalIso.toEquiv.injective ?_
        simp only [Iso.toEquiv_fun]
      · dsimp
        ext
        simp only [prod.map_id_id, types_comp_apply, types_id_apply,
          Types.binaryProductIso_hom_comp_fst_apply, Types.binaryProductIso_hom_comp_snd_apply]
        change _ = G.mul ((Types.binaryProductIso G.X G.X).inv _)
        refine congrArg G.mul ?_
        refine (Types.binaryProductIso _ _).toEquiv.injective ?_
        ext
        · simp only [Iso.toEquiv_fun, Types.binaryProductIso_hom_comp_fst_apply, inv_hom_id_apply]
        · simp only [Iso.toEquiv_fun, Types.binaryProductIso_hom_comp_snd_apply, inv_hom_id_apply]
    · rw [← SetCoe.ext_iff]
      rfl
    · rw [← SetCoe.ext_iff]
      rfl
  · dsimp [CanIso, CanIsoInv]
    rw [← SetCoe.ext_iff]
    rfl

noncomputable def CanCounit : CanIsoInv ⋙ CanIso ≅ 𝟭 Grp.{u} := by
  refine NatIso.ofComponents (fun G ↦ ?_) (fun f ↦ ?_)
  · dsimp [CanIsoInv, CanIso]
    refine MulEquiv.toGrpIso ?_
    refine {toFun := fun x ↦ x, invFun := fun x ↦ x, left_inv := fun _ ↦ by rfl,
            right_inv := fun _ ↦ by rfl,  map_mul' := fun x y ↦ ?_}
    change (CanIsoInv.obj G).mul ((Types.binaryProductIso _ _).inv ⟨x, y⟩) = _
    simp only [CanIsoInv, GroupObjectOfGrp, HomOfMonoidHom, Set.mem_setOf_eq, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, inv_hom_id_apply]
  · ext
    rfl

-- The equivalence.
noncomputable def CanEquiv : GroupObject (Type u) ≌ Grp.{u} where
  functor := CanIso
  inverse := CanIsoInv
  unitIso := CanUnit
  counitIso := CanCounit
  functor_unitIso_comp _ := by rfl

-- Compatibility of the equivalence with the forgetful functors.
noncomputable def CanEquivCompat :
    CanEquiv.functor ⋙ forget Grp ≅ GroupObjectForget (Type u) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

end GroupObject
