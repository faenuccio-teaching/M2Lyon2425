import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Category.Preorder

universe u v

section Generalities

/-
How are categories formalized in Lean?

We want the type of morphisms between objects `X` and `Y` to be a type depending on
`X`, `Y`. (I.e., we don't want to have a type of "all morphisms of the category" with
domain and codomain maps to the type of objects.)
-/

structure NonFlatCat where
    Obj : Type u
    Mor : Obj → Obj → Type v
    id : (X : Obj) → Mor X X
    comp : (X : Obj) → (Y : Obj) → (Z : Obj) → (f : Mor X Y) → (g : Mor Y Z) → Mor X Z
    id_comp : sorry
    comp_id : sorry
    comp_assoc : sorry
-- This is not the actual definition. In fact, as you can see formulating the associativity
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
You see in particular that `Type` itself (which is short for `Type 0`) has a type, called
`Type 1`, that `Type 1` has a type called `Type 2`, etc. The natural number that appears
after `Type` is called a *universe*; we can declare a universe with the following command:
`universe u`. We can add take the sum or max of two universes.

There are rules for assigning a universe to the various type constructions. For example,
if `α : Type u` and `β : Type v`, then `α → β : Type (max u v)`. The general idea is that
the usual "set-theoretic" operations will not make you leave a universe.

Universes are introduced to avoid set-theoretic paradoxes like "the set of all sets which
do not have themselves as an element".

There are special rules for terms of type `Prop`:
-/
variable (α : Type u) (R : α → Prop)
#check α → Prop -- this is the type of sets of `α`, it should be in the same universe as `α`
#check (x : α) → R x  -- this is the statement `∀ (x : α), R x` and so it should be of type `Prop`
/-
Internally, there is another hierarchy called `Sort`, for which `Prop` is `Sort 0` and
`Type u` is `Sort (u + 1)`. Let's not worry too much about that, as the rules are
pretty intuitive.

A couple more points about universes:
* Unlike set theory, we do NOT have an inclusion from an universe to the next one.
Instead, we have "universe lifting" operations `ULift`.
-/
#print ULift
/-
This is a bit painful but you get used to it.
* Categories in Lean are "doubly universe polymorphic", which means that we are allowing
objects and morphisms to be in different universes, because why not? The two most common
cases are when objects and morphisms are in the same universe (called `SmallCategory` in
mathlib) and when objects are one universe level higher than morphisms (called `LargeCategory`
in mathlib).


## Equalities

Because morphisms between objects `X` and `Y` are in a type depending on `X` and `Y`,
it is a *very very good idea* to avoid writing equalities between objects at all costs.

It is also good practice in category theory, because it is almost always irrelevant whether
two objects in a category are actually equal, we care whether they are isomorphic. (The
property of being equal is not preserved if you pass to an equivalent category, the property
of being isomorphic is preserved.)

## Canonical stuff

In informal mathematics, we use the word "canonical" a lot without specifying what it means.
We also allow ourselves to talk about "the" product of two objects, "the" limit of a
diagram, "the" left adjoint of a functor etc, because those are "given up to unique
isomorphism".

We cannot do this in Lean. We will have to talk about "a" product, "a" limit etc, and
then we will have uniqueness lemmas about them. Also, a product of `X` and `Y` is not
just an object of the category, it's the data of an object `P`, of morphism
`P ⟶ X` and `P ⟶ Y`, and of a proof of the universal property of these morphisms. Same
for limits, adjoints...

Relatedly, a lot of things that we think of as propositions are actually definitions
in category theory. For example, saying that an object is the limit of a diagram:
-/
#check CategoryTheory.Limits.IsLimit
#print CategoryTheory.Limits.IsLimit

end Generalities

section Definitions

open CategoryTheory

/- So how do we define a category? The way it is defined in mathlib, a
category is a type with a `CategoryTheory.Category` instance on it.
-/
variable (C : Type u) [Category.{v} C]

/- What is the `Category` class?
It's actually built up from two other classes, `Quiver` which contains the
information of the `Hom` types (a quiver is just an oriented graph):
-/
#print Quiver

/- then `CategoryStruct` which extends `Quiver` abd contains the information of the
identities and of the composition law:
@[pp_with_univ]
class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
-/
#print CategoryStruct

/-
and finally `Category`, which extends `CategoryStruct` and contains the properties
of the identities and the associativity of composition:

@[pp_with_univ]
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat
-/
#print Category

/-
A few notational points.
-/
variable (X Y Z T : C) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

#check 𝟙 X  -- the identity morphism of `X`: \ + b + 1

#check X ⟶ Y -- the type of morphisms from `X` to `Y`
-- Warning: the arrow is typed using "\ + hom" and is different from the "function" arrow → !

#check f ≫ g  -- the composition of `f` and `g` (≫ = \ + gg)
-- Note that composition is written in diagrammatic order! You get used to it.

example : 𝟙 X ≫ f ≫ g = f ≫ 𝟙 Y ≫ g := by simp

/- Composition associates on the right.-/
#check f ≫ g ≫ h

example : f ≫ g ≫ h = f ≫ (g ≫ h) := by rfl

example : f ≫ g ≫ h = (f ≫ g) ≫ h := by rw [Category.assoc] --`rfl` does not work

/-
We have a special tactic for proving "obvious" categorical stuff. It's called `aesop_cat`.
Among other things, it will apply all `simp` lemmas and also try to use `ext` tactics.

You can see it in the fields of `Category`:
@[pp_with_univ]
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat

This means that, when you define a category, if `aesop_cat` can prove the fields
`id_comp`, `comp_id` or `assoc`, then you don't need to include them.

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

A functor is a morphism of quivers that preserves identities and compositions:

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by aesop_cat
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g := by aesop_cat

It is written `C ⥤ D` (\ + func).
-/

variable {C : Type u} [Category.{v} C] (X : C)

-- The Yoneda functors:

example : C ⥤ Type v where
  obj Y := X ⟶ Y
  map f g := g ≫ f

example : Cᵒᵖ ⥤ Type v where
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
It is not a good idea in general to write equality between functors, because that
means writing equalities between objects.

For example, while it is technically true that composition of functors is associative:
-/
example {E E' : Type*} [Category E] [Category E'] (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (F ⋙ G) ⋙ H = F ⋙ G ⋙ H := rfl
/-
it is still much better to use `Functor.associator`:
-/
#check Functor.associator

example {E E' : Type*} [Category E] [Category E'] (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H := Functor.associator F G H
-- `≅` (\ + iso) is the symbol for an isomorphism; here it is a natural isomorphism.

-- Similary for composition with identity functors:
#check Functor.leftUnitor
#check Functor.rightUnitor

/-
And finally, we have natural transformations (and natural isomorphisms):
-/
#print NatTrans
/-
@[ext]
structure NatTrans {C : Type u₁} [Category.{v₁, u₁} C] {D : Type u₂} [Category.{v₂, u₂} D]
    (F G : C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f := by aesop_cat
-/

/-
The type of natural transformations from `F` to `G` is writte `F ⟶ G` (with the `hom` arrow).
-/

#print NatIso
-- oops... A `NatIso` is actually just an isomorphism in the category of functors.
#print Iso
#synth Category (C ⥤ D)
-- The category of functors from `C` to `D`, whose objects are functors `C ⥤ D` and
-- whose morphisms are natural transformations, with vertical composition (denoted by
-- `≫`, just like ordinary composition).

/-
We also have horizontal composition of natural transformations:

def CategoryTheory.NatTrans.hcomp {C : Type u₁} [Category.{v₁, u₁} C] {D : Type u₂}
    [Category.{v₂, u₂} D] {E : Type u₃} [Category.{v₃, u₃} E]
    {F G : Functor C D} {H I : Functor D E} (α : F ⟶ G) (β : H ⟶ I) :
  F.comp H ⟶ G.comp I
-/

end Definitions

section Examples

open CategoryTheory

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
-- `Discrete J` is basically `J`. More precisely, it is a structure with a unique field
-- whose value is a term of type `J`. (Note that `Opposite` was constructed similarly.)
example (x : J) : Discrete J := {as := x}

example (x : J) : Discrete J := Discrete.mk x

example {x : J} : Discrete.mk x = {as := x} := rfl

#synth Category (Discrete J)

example (C : Type*) [Category C] (f : J → C) : Discrete J ⥤ C where
  obj := sorry
  map := sorry
  map_id := sorry
  map_comp := sorry

-- Preorders as categories

variable [Preorder J]

#synth Category J
-- The category whose objects are terms of type `J`, such that there is a morphism
-- `i ⟶ j` if and only if `i ≤ j`.

#print Preorder.smallCategory
/-
instance (priority := 100) smallCategory (α : Type u) [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans _ _ _ f.down.down g.down.down⟩⟩

Yikes! The horrible definition of `Hom U V` is because we don't allow `Hom` types to be
in `Prop`, and `U ≤ V` is.
-/
#check PLift

example (K : Type*) [Preorder K] (f : J → K) (h : Monotone f) : J ⥤ K where
  obj := sorry
  map := sorry
  map_id := sorry
  map_comp := sorry

-- The category of types (in a fixed universe), which we already met:

#synth Category (Type u)

-- Morphisms are defined as functions:
example {X Y : Type u} (f : X → Y) : X ⟶ Y := f

-- If Lean doesn't understand, you can use `asHom`:
example {X Y : Type u} (f : X → Y) : X ⟶ Y := asHom f


/- Concrete categories: These are subcategories of the category of types,
i.e. categories `C` that come with a faithful functor `forget C : C ⥤ Type u`.

We can also have two concrete categories `C` and `D` with a forgetful functor
from `C` to `D`, i.e. a functor `forget₂ C D : C ⥤ D` such that
`forget₂ C D ⋙ forget D = forget C` (this is an equality of functors, but is
is written like this in mathlib.)

This includes all algebraic categories, as well as `TopCat`.

-/




end Examples
