import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.GroupTheory.Abelianization
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic


universe u v

section Generalities

/-
How are categories formalized in Lean?

We want the type of morphisms between objects `X` and `Y` to be a
type depending on `X`, `Y`. (I.e., we don't want to have a type
of "all morphisms of the category" with
domain and codomain maps to the type of objects.)
-/

structure NonFlatCat where
    Obj : Type u
    Mor : Obj → Obj → Type v
    id : (X : Obj) → Mor X X
    comp : (X : Obj) → (Y : Obj) → (Z : Obj) →
        (f : Mor X Y) → (g : Mor Y Z) → Mor X Z
    id_comp : sorry
    comp_id : sorry
    comp_assoc : sorry
-- This is not the actual definition. In fact, as you can see
-- formulating the associativity
-- of composition will get painful if we do it this way.

/-
A few remarks before we see the actual definition:

## Universes:
As we mentioned before, every term has a type. For example:
-/
#check ℕ
#check Bool
#check Prop
#check Type
#check Type 1
#check Type 2
/-
You see in particular that `Type` itself (which is short for `Type 0`)
has a type, called `Type 1`, that `Type 1` has a type called `Type 2`,
etc. The natural number that appears after `Type` is called a
*universe*; we can declare a universe with the following command:
`universe u`. We can add take the sum or max of two universes.

There are rules for assigning a universe to the various type
constructions. For example, if `α : Type u` and `β : Type v`,
then `α → β : Type (max u v)`. The general idea is that
the usual "set-theoretic" operations will not make you leave
a universe.

Universes are introduced to avoid set-theoretic paradoxes like
"the set of all sets which do not have themselves as an element".

There are special rules for terms of type `Prop`:
-/
variable (α : Type u) (R : α → Prop)
#check α → Prop
-- this is the type of sets of `α`, it should be in
-- the same universe as `α`
#check (x : α) → R x
-- this is the statement `∀ (x : α), R x` and so it
-- should be of type `Prop`

/-
Internally, there is another hierarchy called `Sort`, for
which `Prop` is `Sort 0` and `Type u` is `Sort (u + 1)`.
Let's not worry too much about that, as the rules are
pretty intuitive.

A couple more points about universes:
* Unlike set theory, we do NOT have an inclusion from an
universe to the next one. Instead, we have "universe lifting"
operations `ULift`.
-/
#print ULift
/-
This is a bit painful but you get used to it.
* Categories in Lean are "doubly universe polymorphic", which
means that we are allowing objects and morphisms to be in
different universes, because why not? The two most common
cases are when objects and morphisms are in the same universe
(called `SmallCategory` in mathlib) and when objects are one
universe level higher than morphisms (called `LargeCategory`
in mathlib).


## Equalities

Because morphisms between objects `X` and `Y` are in a type
depending on `X` and `Y`, it is a *very very good idea* to
avoid writing equalities between objects at all costs.

It is also good practice in category theory, because it is
almost always irrelevant whether two objects in a category
are actually equal, we care whether they are isomorphic. (The
property of being equal is not preserved if you pass to an
equivalent category, the property of being isomorphic is
preserved.)

## Canonical stuff

In informal mathematics, we use the word "canonical" a lot
without specifying what it means. We also allow ourselves to
talk about "the" product of two objects, "the" limit of a
diagram, "the" left adjoint of a functor etc, because those
are "given up to unique isomorphism".

We cannot do this in Lean. We will have to talk about "a"
product, "a" limit etc, and then we will have uniqueness lemmas
about them. Also, a product of `X` and `Y` is not just an
object of the category, it's the data of an object `P`, of
morphism `P ⟶ X` and `P ⟶ Y`, and of a proof of the universal
property of these morphisms. Same for limits, adjoints...

Relatedly, a lot of things that we think of as propositions are
actually definitions in category theory. For example, saying
that an object is the limit of a diagram:
-/
#check CategoryTheory.Limits.IsLimit
#print CategoryTheory.Limits.IsLimit

end Generalities


open CategoryTheory
-- A lot of the category theory stuff is in the namespace
-- `CategoryTheory`, so it's a good idea to open it now.


section Definitions

/- So how do we define a category? The way it is defined in
mathlib, a category is a type with a `CategoryTheory.Category`
instance on it.
-/
variable (C : Type u) [Category.{v} C]

/- What is the `Category` class?
It's actually built up from two other classes, `Quiver` which
contains the information of the `Hom` types (a quiver is just
an oriented graph):
-/
#print Quiver

/- then `CategoryStruct` which extends `Quiver` abd contains
the information of the identities and of the composition law:
@[pp_with_univ]
class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
-/
#print CategoryStruct

/-
and finally `Category`, which extends `CategoryStruct` and
contains the properties of the identities and the associativity
of composition:

@[pp_with_univ]
class Category (obj : Type u) extends CategoryStruct.{v} obj :
    Type max u (v + 1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
      (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat
-/
#print Category

/-
A few notational points.
-/
variable (X Y Z T : C) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

#check 𝟙 X  -- the identity morphism of `X`: \ + b + 1

#check X ⟶ Y -- the type of morphisms from `X` to `Y`
-- Warning: the arrow is typed using "\ + hom" and is different
-- from the "function" arrow → !

#check f ≫ g  -- the composition of `f` and `g` (≫ = \ + gg)
-- Note that composition is written in diagrammatic order!
-- You get used to it.

example : 𝟙 X ≫ f ≫ g = f ≫ 𝟙 Y ≫ g := by simp

/- Composition associates on the right.-/
#check f ≫ g ≫ h

example : f ≫ g ≫ h = f ≫ (g ≫ h) := by rfl

example : f ≫ g ≫ h = (f ≫ g) ≫ h := by rw [Category.assoc] --`rfl` does not work

/-
We have a special tactic for proving "obvious" categorical stuff.
It's called `aesop_cat`. Among other things, it will apply all
`simp` lemmas and also try to use `ext` tactics.

You can see it in the fields of `Category`:
@[pp_with_univ]
class Category (obj : Type u) extends CategoryStruct.{v} obj :
    Type max u (v + 1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
      (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat

This means that, when you define a category, if `aesop_cat` can
prove the fields `id_comp`, `comp_id` or `assoc`, then you don't
need to include them.

For example:
-/

def CatType := Type u

instance : Category CatType where
  Hom X Y := X → Y
  id X := fun a ↦ a
  comp f g := g ∘ f
-- Success!
-- Of course this instance already exists:
#synth Category (Type u)  -- This is a `LargeCategory` instance.

/-
After categories, the next step is functors.
-/
#print Functor -- careful, there is also a `_root_.Functor`!


/-
They are of course defined in two steps:
A `Prefunctor` is a morphism of quivers, i.e.:

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

It is written `C ⥤q D`. (\ + func + q)

A functor is a morphism of quivers that preserves identities and
compositions:

structure Functor (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] extends
    Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by aesop_cat
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      map (f ≫ g) = map f ≫ map g := by aesop_cat

It is written `C ⥤ D` (\ + func).
-/

variable {C : Type u} [Category.{v} C] (X : C)

-- The Hom functors:

def HomLeft : C ⥤ Type v where
  obj Y := X ⟶ Y
  map f g := g ≫ f

def HomRight : Cᵒᵖ ⥤ Type v where
  obj Y := Opposite.unop Y ⟶ X
  map f g := sorry
  map_id := sorry
  map_comp := sorry

#check Opposite.op
#check Opposite.unop
#check Quiver.Hom.op
#check Quiver.Hom.unop

variable {D : Type*} [Category D]

example (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj := sorry
  map := sorry
  map_id := sorry
  map_comp := sorry


/-
We can compose functors, and this is written `F ⋙ G` (\ + ggg), if `F : C ⥤ D`
and `G : D ⥤ E` (so diagrammatic order again).
The identity functor is `𝟭 C` (\ + sb1).
-/

/-
It is not a good idea in general to write equality between
functors, because that means writing equalities between objects.

For example, while it is technically true that composition of
functors is associative:
-/
example {E E' : Type*} [Category E] [Category E'] (F : C ⥤ D)
    (G : D ⥤ E) (H : E ⥤ E') :
    (F ⋙ G) ⋙ H = F ⋙ G ⋙ H := rfl
/-
it is still much better to use `Functor.associator`:
-/
#check Functor.associator

example {E E' : Type*} [Category E] [Category E'] (F : C ⥤ D)
    (G : D ⥤ E) (H : E ⥤ E') :
    (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H := Functor.associator F G H
-- `≅` (\ + iso) is the symbol for an isomorphism;
-- here it is a natural isomorphism.

-- Similary for composition with identity functors:
#check Functor.leftUnitor
#check Functor.rightUnitor

/-
And finally, we have natural transformations (and natural
isomorphisms):
-/
#print NatTrans
/-
@[ext]
structure NatTrans {C : Type u₁} [Category.{v₁, u₁} C]
    {D : Type u₂} [Category.{v₂, u₂} D] (F G : C ⥤ D) :
    Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    F.map f ≫ app Y = app X ≫ G.map f := by aesop_cat
-/

/-
The type of natural transformations from `F` to `G` is writte
`F ⟶ G` (with the `hom` arrow).
-/

#print NatIso
-- oops... A `NatIso` is actually just an isomorphism in
-- the category of functors.
#print Iso
#synth Category (C ⥤ D)
-- The category of functors from `C` to `D`, whose objects are
-- functors `C ⥤ D` and whose morphisms are natural
-- transformations, with vertical composition (denoted by
-- `≫`, just like ordinary composition).

/-
We also have horizontal composition of natural transformations:

def CategoryTheory.NatTrans.hcomp {C : Type u₁} [Category.{v₁, u₁} C]
    {D : Type u₂} [Category.{v₂, u₂} D]
    {E : Type u₃} [Category.{v₃, u₃} E]
    {F G : Functor C D} {H I : Functor D E}
    (α : F ⟶ G) (β : H ⟶ I) :
  F.comp H ⟶ G.comp I
-/

/- The Yoneda functors.-/

def Yon : C ⥤ (Cᵒᵖ ⥤ Type v) where
  obj := HomRight
  map {Y Y'} f := sorry
  map_id := sorry
  map_comp := sorry
-- What happens if I try to do `Yon : C ⥤ (Cᵒᵖ ⥤ Type)`?


def YonOp : Cᵒᵖ ⥤ (C ⥤ Type v) where
  obj X := sorry -- try `HomLeft X`, what happens?
  map := sorry
  map_id := sorry
  map_comp := sorry


/-
The Yoneda lemma. Of course it's already in mathlib, but let's
do it as an exercise.

First we should decide how to state it. One statement is that
the Yoneda embedding `Yon : C ⥤ (Cᵒᵖ ⥤ Type)` is fully faithful
(as well the as `YonOp`), but this is not the most general
version.

You also have a version that says that, for every `X : C` and
`F : Cᵒᵖ ⥤ Type v`, there is an equivalence between the types
`Yon.obj X ⟶ F` and `F.obj (Opposite.op X)` given by sending
`u : Yon.obj X ⟶ F` to the image of `𝟙 X` by `u`. Let's try to
prove this first.
-/

open Opposite

@[simp]
def YonedaEquivFun {X : C} {F : Cᵒᵖ ⥤ Type v} (u : Yon.obj X ⟶ F) :
    F.obj (op X) := sorry

@[simp]
def YonedaEquivInv {X : C} {F : Cᵒᵖ ⥤ Type v} (x : F.obj (op X)) :
    Yon.obj X ⟶ F := sorry

@[simp]
def YonedaEquiv (X : C) (F : Cᵒᵖ ⥤ Type v) :
    (Yon.obj X ⟶ F) ≃ F.obj (op X) := sorry

/-
Of course we could go further, because both sides of the
equivalence are functors in `X` and `F`, so we could ask for
an isomorphism of functors `X × (Cᵒᵖ ⥤ Type v) ⥤ Type`.
(What universe level here?)

Let's do full faithfulness of `Yon` instead.
-/

example : Yon.FullyFaithful (C := C) := sorry

end Definitions


section Examples

/- There are some categories already in mathlib.-/

-- Discrete categories
variable (J : Type*)

#check Discrete J

#print Discrete
/-
@[ext, aesop safe cases (rule_sets := [CategoryTheory])]
structure Discrete (J : Type u₁) where
  /-- A wrapper for promoting any type to a category,
  with the only morphisms being equalities. -/
  as : J
-/
-- `Discrete J` is basically `J`. More precisely, it is a
-- structure with a unique field whose value is a term of
-- type `J`. (Note that `Opposite` was constructed similarly.)
example (x : J) : Discrete J := {as := x}

example (x : J) : Discrete J := Discrete.mk x

example {x : J} : Discrete.mk x = {as := x} := rfl

#synth Category (Discrete J)

example (C : Type*) [Category C] (f : J → C) :
    Discrete J ⥤ C where
  obj := sorry
  map := sorry
  map_id := sorry
  map_comp := sorry

-- Preorders as categories

variable [Preorder J]

#synth Category J
-- The category whose objects are terms of type `J`, such that
-- there is a morphism `i ⟶ j` if and only if `i ≤ j`.

#print Preorder.smallCategory
/-
instance (priority := 100) smallCategory (α : Type u)
    [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans _ _ _ f.down.down g.down.down⟩⟩

Yikes! The horrible definition of `Hom U V` is because we don't
allow `Hom` types to be in `Prop`, and `U ≤ V` is.
-/
#check PLift

example (K : Type*) [Preorder K] (f : J → K) (h : Monotone f) :
    J ⥤ K where
  obj := sorry
  map := sorry
  map_id := sorry
  map_comp := sorry

-- The category of types (in a fixed universe), which we
-- already met:

#synth Category (Type u)

-- Morphisms are defined as functions:
example {X Y : Type u} (f : X → Y) : X ⟶ Y := f

-- If Lean doesn't understand, you can use `asHom`:
example {X Y : Type u} (f : X → Y) : X ⟶ Y := asHom f


/- Concrete categories: These are subcategories of the category
of types, i.e. categories `C` that come with a faithful functor
`forget C : C ⥤ Type u`.

We can also have two concrete categories `C` and `D` with a
forgetful functor from `C` to `D`, i.e. a functor
`forget₂ C D : C ⥤ D` such that
`forget₂ C D ⋙ forget D = forget C` (this is an equality of
functors, but is is written like this in mathlib.)

This includes all algebraic categories, as well catgeories like
as `TopCat`.

The algebraic categories (and related ones) are in
`Algebra.Category`, and `TopCat` is in `Topology.Category`.

For example you have `AlgebraCat`, `Coalgebracat`, `BialgebraCat`,
`HopfAlgebraCat`, `ModuleCat`, `FGModuleCat`, `RingCat` and
`CommRingCat`, `MonCat` and `CommMonCat` (the catgeory of
monoids/commutative monoids) as well as additive versions
`AddMonCat` and `AddCommMonCat`, `Grp` and `CommGrp` as well as
additive versions `AddGrp` and `AddCommGrp`.

As you can see, the naming scheme is not uniform. We cannot just
call these categories `Ring`, `Group` etc because this is already
the name of a class!

All these categories depend on a universe level (two for
`ModuleCat` and `FGModuleCat`: one for the ring, one for the
modules) and have forgetful functors to `Type`. They
also have forgetful functors between themselves.
-/
#check forget₂ Grp MonCat
#check forget Grp
#check Grp.{u}  --this is how you specify the universe
#check forget Grp.{u}

#check ModuleCat.{v, u}  -- category of `R`-modules in `Type v`, where `R` is a ring in `Type u`

/-
An object of one of these categories (for examplem `Grp`) is a
*bundled group*, i.e. a structure containing in its fields a type
and a group structure on that type.

Morphisms of by defintions morphisms between the underlying
types with extra structures.

If you have a group/ring/etc, you can form the corresponding
object of the category by using `_name_of_category_.of`; for
morphism, use `ofHom`:
-/
example (G : Type*) [Group G] : Grp := Grp.of G

example {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Grp.of G ⟶ Grp.of H := sorry
-- Lean complains because `G` and `H` are not necessarily
-- in the same universe

example {G H : Type u} [Group G] [Group H] (f : G →* H) :
    Grp.of G ⟶ Grp.of H := Grp.ofHom f

-- There are coercions in place to make things less painful.
-- Here for example I am applying a morphism of `Grp` to an
-- element of `G`, even though technically `G` is not a group
-- but an object of `Grp`.

example {G H : Grp} (f : G ⟶ H) (x : G) : H := f x

example {G : Type*} [Group G] : (Grp.of G).1 = G := rfl
example {G : Type*} [Group G] : (Grp.of G).α = G := rfl

example {G H : Type u} [Group G] [Group H] (f : G →* H) :
    (Grp.ofHom f).toFun = f.toFun := rfl
example {G H : Type u} [Group G] [Group H] (f : G →* H) :
    Grp.ofHom f = f := rfl

end Examples

section Adjunction

universe u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'}
  [Category.{v'} D] (F : C ⥤ D) (G : D ⥤ C)

/-
Let's see one of the fundamental concepts of category theory:
adjoint functors.

Informally, we say that functors `F : C ⥤ D` and `G : D ⥤ C`
are adjoint if there are equivalences
`(F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)` for every `X : C` and `Y : D`.
Of course, these equivalences should be natural in both `X`
and `Y`.

Let's look at the mathlib definition:

structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  /-- The unit of an adjunction -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit and counit with
      the identity `F ⟶ FGF ⟶ F = 𝟙` -/
  left_triangle_components (X : C) :
      F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X) :=
        by aesop_cat
  /-- Equality of the composition of the unit and counit with the
      identity `G ⟶ GFG ⟶ G = 𝟙` -/
  right_triangle_components (Y : D) :
      unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y) :=
        by aesop_cat

Note that this is the current definition, not the one in our
outdated version of mathlib! In our version, this is called
`Adjunction.CoreUnitCounit`.-/

#print Adjunction
#print Adjunction.CoreUnitCounit

/-
Current mathlib uses the `unit - counit` definition. The
equivalences `(F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)` we were discussing
are then called  `Adjunction.homEquiv X Y`. Let's try to get a
"mathlib adjunction" from an "informal adjunction". (Of course,
this is already in mathlib, in fact there are several different
constructors for adjunctions.)
-/

structure InfAdjunction where
  equiv (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  left_naturality {X X' : C} (Y : D) (f : X ⟶ X')
      (g : F.obj X' ⟶ Y) :
      f ≫ equiv X' Y g = equiv X Y (F.map f ≫ g)
  right_naturality (X : C) {Y Y' : D} (g : Y ⟶ Y')
      (f : X ⟶ G.obj Y) :
      (equiv X Y).symm f ≫ g = (equiv X Y').symm (f ≫ G.map g)

-- Exercise: going from "informal adjunctions" to "unit-counit
-- adjunctions".
example (adj : InfAdjunction F G) :
    Adjunction.CoreUnitCounit F G where
  unit := {
    app := fun X ↦ (adj.equiv X (F.obj X)).toFun (𝟙 (F.obj X))
    naturality := by
      intro _ _ _
      dsimp
      rw [adj.left_naturality]
      apply (adj.equiv _ _).symm.injective
      rw [← adj.right_naturality]
      simp
  }
  counit := sorry
  left_triangle := sorry
  right_triangle := sorry
-- This is kind of boring, let's not do it in class.

/-
Let's try to do some classical adjunctions.
-/

-- Abelianization ⊣ forgetful

-- Definition of the abelianization functor from `Grp` to
-- `CommGrp`. We used the definitions and lemmas of
-- `Mathlib.GroupTheory.Abelianization`.
@[simp]
def FunctorAbelianization : Grp ⥤ CommGrp where
  obj G := CommGrp.of (Abelianization G)
  map f := CommGrp.ofHom (Abelianization.map f)
  map_id _ := by sorry
  map_comp _ _ := by sorry

#check Adjunction.mkOfHomEquiv
#print Adjunction.CoreHomEquiv

def core : Adjunction.CoreHomEquiv FunctorAbelianization
    (forget₂ CommGrp Grp) where
  homEquiv G H := Abelianization.lift.symm
  homEquiv_naturality_left_symm _ _ := by sorry
  homEquiv_naturality_right _ _ := by sorry

def adjAb : FunctorAbelianization ⊣ (forget₂ CommGrp Grp) :=
  Adjunction.mkOfHomEquiv core

-- Adjunction between `Type` and `TopCat` given by the discrete
-- topology. Note that morphisms in `TopCat` are bundled
-- continuous maps of type `ContinuousMap`.
#print ContinuousMap

def DiscreteFunctor : Type ⥤ TopCat where
  obj X :=
    have : TopologicalSpace X := ⊥
    TopCat.of X
  map f := ContinuousMap.mk f continuous_bot

#check forget TopCat

def coreTop : Adjunction.CoreHomEquiv DiscreteFunctor
    (forget TopCat) where
  homEquiv X Y := by sorry
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

end Adjunction

section Initial

universe u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'}
  [Category.{v'} D] (G : D ⥤ C)

open Limits

/- Let `G : D ⥤ C`. We will prove that the functor `G` has a
left adjoint if and only if, for every `X : C`, the comma
category ` X ↓ G` has an initial object.

An initial object in a category `E` is a special case of
colimit (we will see the general notion next): it is
an object `I` of `E` such that, for every object `Z : E`,
there exists a unique morphism `I ⟶ Z`.
-/

#print IsInitial
#check isInitialEquivUnique

/-"Remember" also that `X ↓ G` is the category whose objects
are pairs `(Y,f)` with `Y : D` and `f : X ⟶ G.obj Y`, and whose
morphisms are commutative diagrams.

The category `X ↓ G` is a special case of `CategoryTheory.Comma F G`
where `F` is the functor from the one-point category `PUnit` to
`C` sending the unique object to `X`.
It already exists in mathlib and is called `StructuredArrow X G`.
-/

#print Comma
#print StructuredArrow

/-
If `A : StructuredArrow X G`, its fields are called `A.right`
(the object of `D`) and `A.hom` (the morphism `X ⟶ G.obj A.right`).
-/

/-
First direction: if `G` has a left adjoint, then each category
`StructuredArrow X G` has an initial object. We will use
`Limits.hasInitial_of_unique` to construct the `HasInitial`
classes. This requires us to find the initial object first.
-/

#check Limits.hasInitial_of_unique
#check Unique.mk'
#check Inhabited.mk
#check Subsingleton.intro
#check StructuredArrow.homMk
#check StructuredArrow.hom_ext
#check Adjunction.homEquiv_unit

/-
Suppose that `G` has a left adjoint `F`. Then, for every `X : C`,
the category `StructuredArrow X G` has an initial object, which
is given by `adj.unit.app X : X ⟶ G.obj (F.obj X)`.
-/
def HasInitialOfLeftAdjoint {F : C ⥤ D} (adj : F ⊣ G) (X : C) :
    HasInitial (StructuredArrow X G) := by
  set I : StructuredArrow X G :=
    StructuredArrow.mk (adj.unit.app X)
  have : ∀ (A : StructuredArrow X G), Unique (I ⟶ A) := by
    intro A
    refine @Unique.mk' _ ?_ ?_
    · sorry
    · sorry
  exact hasInitial_of_unique I

/- The other direction: if each category `StructuredArrow X G`
has an initial object, then `G` has a left adjoint `F`. We will
define `F.obj X` as the `right` component of the initial object
of `StructuredArrow X G`, and the `hom` component will give us
the unit of the adjunction at `X`.

Note that, if `u` is a morphism in `StructuredArrow X G`, then
it has fields `u.right` (the underlying morphism of objects of
`D`) and `u.w` (the commutative triangle).

To check the requisite compatibilities, we use many times the
fact that, if `X` is initial, then any two morphisms
`f, g : X ⟶ Y` are equal. This is called `Limits.initial.hom_ext`.
-/

#check Limits.initial
#check Limits.initial.to
#check StructuredArrow.map -- functor from `StructuredArrow X' G`
-- to `StructuredArrow X G` induced by a morphism `f : X ⟶ X'`
#check Limits.initial.hom_ext

noncomputable abbrev FunctorOfInitialObj (X : C)
    (_ : HasInitial (StructuredArrow X G)) : D :=
  (initial (StructuredArrow X G)).right

variable (h : ∀ (X : C), HasInitial (StructuredArrow X G))

noncomputable def FunctorOfInitial : C ⥤ D where
      obj X := FunctorOfInitialObj G X (h X)
      map {X X'} f := sorry
      map_id X := sorry
      map_comp {X X' X''} f g := sorry

noncomputable def UnitOfInitial :
    𝟭 C ⟶ FunctorOfInitial G h ⋙ G where
      app X := (initial (StructuredArrow X G)).hom
      naturality X X' f := sorry

noncomputable def CounitOfInitial :
    G ⋙ FunctorOfInitial G h ⟶ 𝟭 D where
  app Y := sorry
  naturality Y Y' f := sorry

#check whiskerLeft
#check whiskerRight
#check Functor.associator
#check initial.hom_ext

lemma LeftTriangleOfInitial :
    whiskerRight (UnitOfInitial G h) (FunctorOfInitial G h) ≫
    ((FunctorOfInitial G h).associator G (FunctorOfInitial G h)).hom ≫
    whiskerLeft (FunctorOfInitial G h) (CounitOfInitial G h) =
    𝟙 (𝟭 C ⋙ FunctorOfInitial G h) := by
  ext X
  sorry

lemma RightTriangleOfInitial :
    whiskerLeft G (UnitOfInitial G h) ≫
    (G.associator (FunctorOfInitial G h) G).inv ≫
    whiskerRight (CounitOfInitial G h) G = 𝟙 (G ⋙ 𝟭 C) := by
  ext X
  sorry

noncomputable def AdjunctionOfInitial : FunctorOfInitial G h ⊣ G :=
  Adjunction.mkOfUnitCounit (Adjunction.CoreUnitCounit.mk
  (UnitOfInitial G h) (CounitOfInitial G h)
  (LeftTriangleOfInitial G h) (RightTriangleOfInitial G h))

include h in
lemma IsRightAdjointOfInitial : G.IsRightAdjoint where
  exists_leftAdjoint :=
    ⟨FunctorOfInitial G h,
    Nonempty.intro (AdjunctionOfInitial G h)⟩

lemma IsRightAdjointIffInitial :
    G.IsRightAdjoint ↔ ∀ (X : C), HasInitial (StructuredArrow X G) :=
  ⟨fun _ ↦ HasInitialOfLeftAdjoint G (Adjunction.ofIsRightAdjoint G),
  IsRightAdjointOfInitial G⟩

end Initial
