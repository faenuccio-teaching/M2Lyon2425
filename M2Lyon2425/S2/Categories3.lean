import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-
## Bicategories

A bicategory is, informally, a category`B` where the `Hom`
types have themselves category structures. This means that,
given `X, Y : B` and `f, g : X ⟶ Y`, there is a notion of
morphism from `f` to `g`, which we call a 2-morphism
(and we refer to `f` and `g` as 1-morphisms).

A bit less informally, a bicategory is the data of a type
`B` and, for all `X, Y : B`, of a category `Hom X Y`. We
also want identity objects `id X : Hom X X` and composition
*functors* `Hom X Y × Hom Y Z ⥤ Hom X Z`.
Associativity of composition and the unit property of the
identities objects are not strictly true but are expressed by
isomorphisms called `associator`, `leftUnitor` and
`rightUnitor`, and there are two axioms called the
`triangle` and `pentagon`. The triangle axiom expresses
a compatibility between the associator and the left/right
unitors, and the pentagon axiom is a compatibility property
of associators.

More precisely, the triangle axiom says that, for
all `X, Y, Z : B` and for all `f : X ⟶ Y` and `g : Y ⟶ Z`,
the two possible 2-isomorphisms from `(f ≫ 𝟙 Y) ≫ g` to
`f ≫ (𝟙 Y ≫ g)` (one the associator, and the other
formed by composing right and left unitors) are equal.
The pentagon axiom says that, given `X, Y, Z, T, U : B`
and 1-morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ T`
and `i : T ⟶ U`, the two possible 2-isomorphisms
from `((f ≫ g) ≫ h) ≫ i` to `f ≫ (g ≫ (h ≫ i))`
(formed by applying associators in different ways) are
equal.

To get even more technical, composition of 1-morphisms in
mathlib is not actually given as a functor but through the
whiskering functions, though the functor is available
later as `CategoryTheory.Bicategory.precomposing` or
`CategoryTheory.Bicategory.postcomposing`.

As another technical note, a bicategory can have three
distinct universe levels: one for the objects, one for
the 1-morphisms, and one for the 2-morphisms.

-/

universe u u' v v' w w'

open CategoryTheory Category
open scoped Bicategory

#print Bicategory
/-
@[nolint checkUnivs]
class Bicategory (B : Type u) extends CategoryStruct.{v} B where
  -- remember that `CategoryStruct` is the data of the `Hom`
  -- types, the composition and the identities, but without
  -- the axioms
  -- category structure on the collection of 1-morphisms:
  homCategory : ∀ a b : B, Category.{w} (a ⟶ b) := by infer_instance
  -- left whiskering:
  whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
      f ≫ g ⟶ f ≫ h
  -- right whiskering:
  whiskerRight {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
      f ≫ h ⟶ g ≫ h
  -- associator:
  associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
      (f ≫ g) ≫ h ≅ f ≫ g ≫ h
  -- left unitor:
  leftUnitor {a b : B} (f : a ⟶ b) : 𝟙 a ≫ f ≅ f
  -- right unitor:
  rightUnitor {a b : B} (f : a ⟶ b) : f ≫ 𝟙 b ≅ f
  -- axioms for left whiskering:
  whiskerLeft_id : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
      whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g) := by
    aesop_cat
  whiskerLeft_comp :
    ∀ {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i),
      whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ := by
    aesop_cat
  id_whiskerLeft :
    ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerLeft (𝟙 a) η =
        (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := by
    aesop_cat
  comp_whiskerLeft :
    ∀ {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
      whiskerLeft (f ≫ g) η =
        (associator f g h).hom ≫
        whiskerLeft f (whiskerLeft g η) ≫
        (associator f g h').inv := by
    aesop_cat
  -- axioms for right whiskering:
  id_whiskerRight : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
      whiskerRight (𝟙 f) g = 𝟙 (f ≫ g) := by
    aesop_cat
  comp_whiskerRight :
    ∀ {a b c} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c),
      whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i := by
    aesop_cat
  whiskerRight_id :
    ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerRight η (𝟙 b) = (rightUnitor f).hom ≫ η ≫
        (rightUnitor g).inv := by
    aesop_cat
  whiskerRight_comp :
    ∀ {a b c d} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
      whiskerRight η (g ≫ h) =
        (associator f g h).inv ≫
          whiskerRight (whiskerRight η g) h ≫
            (associator f' g h).hom := by
    aesop_cat
  -- associativity of whiskerings:
  whisker_assoc :
    ∀ {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
      whiskerRight (whiskerLeft f η) h =
        (associator f g h).hom ≫
        whiskerLeft f (whiskerRight η h) ≫ (associator f g' h).inv := by
    aesop_cat
  -- exchange law of left and right whiskerings:
  whisker_exchange :
    ∀ {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
      whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫
      whiskerLeft g θ := by
    aesop_cat
  -- pentagon identity:
  pentagon :
    ∀ {a b c d e} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
      whiskerRight (associator f g h).hom i ≫
          (associator f (g ≫ h) i).hom ≫
          whiskerLeft f (associator g h i).hom =
          (associator (f ≫ g) h i).hom ≫
          (associator f g (h ≫ i)).hom := by
    aesop_cat
  -- triangle identity:
  triangle :
    ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
      (associator f (𝟙 b) g).hom ≫
      whiskerLeft f (leftUnitor g).hom
      = whiskerRight (rightUnitor f).hom g := by
    aesop_cat
-/

--This of course unreadable.

/-
Notation:
- For `X, Y : B`, the category `Hom X Y` is written `X ⟶ Y`.
- For `X : B`, the identity in `X ⟶ X` is written `𝟙 X`.
- Composition of 1-morphisms is denoted by `≫` and written
in diagrammatic order.
- We also use `⟶`, `𝟙` and `≫` to denote 2-morphisms,
and the identities and compositions inside the category
`X ⟶ Y`, so be careful.
- The left unitor of a 1-morphism `f` is denoted by
`λ_ f`.
- The right unitor of a 1-morphism `f` is denoted by
`ρ_ f`.
- The associator of three 1-morphisms `f,g,h` is denoted
by `α_ f g h`.
- We use `◁` (\ + lhd) for left whiskering.
- We use `▷` (\ + rhd) for right whiskering.

(The last five are scoped notation, to make this available
you need to `open` or `open scoped` the `Bicategory`
namespace.)
(Check if they know the difference between `open` and
`open scoped`.)
-/

variable (B : Type*) [Bicategory B] (X Y Z T U : B)
  (f f' f'' : X ⟶ Y) (g g' : Y ⟶ Z) (h : Z ⟶ T) (i : T ⟶ U)
  (u : f ⟶ f') (u' : f' ⟶ f'') (v : g ⟶ g')

#check 𝟙 X
#check 𝟙 f
#check f ≫ g
#check u ≫ u'
#check f ◁ v
#check u ▷ g
#check λ_ f
#check ρ_ f
#check α_ f g h

#check Bicategory.triangle f
#check Bicategory.pentagon f g h i

#check Bicategory.precomposing
#check Bicategory.postcomposing

/-
# Examples.

The first example is the bicategory `Cat` of categories at
fixed universe levels.
-/
#check Cat

#synth Bicategory Cat.{v, u}

#check Cat.bicategory

#print Cat.bicategory

/-
Note that `Cat` is what is called a *strict* bicategory, i.e.
a bicategory where the associators, left unitors and right
unitors isomorphisms are just identity morphisms.

In mathlib, as the type of 2-morphisms (where associators etc
live) depends on the the 1-morphisms, we cannot use that
definition immediately, so instead we use the construction
`eqToIso` (the isomorphism version of `eqToHom`).
-/

#check eqToIso -- from an equality between objects, produces
               -- an isomorphism between them

#print Bicategory.Strict

/-
class Bicategory.Strict : Prop where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {a b : B} (f : a ⟶ b), 𝟙 a ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {a b : B} (f : a ⟶ b), f ≫ 𝟙 b = f := by aesop_cat
  /-- Composition in a bicategory is associative. -/
  assoc : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat
  /-- The left unitors are given by equalities -/
  leftUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b),
      λ_ f = eqToIso (id_comp f) := by aesop_cat
  /-- The right unitors are given by equalities -/
  rightUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b),
      ρ_ f = eqToIso (comp_id f) := by aesop_cat
  /-- The associators are given by equalities -/
  associator_eqToIso :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
       α_ f g h = eqToIso (assoc f g h) := by
    aesop_cat
-/

/-
Another example are monoidal categories. A monoidal
category is often presented as a category with an
extra operation on objects, often denote by `⊗`, which
also acts on morphisms and satisfies some compatibility
conditions (associativity up to isomorphism, existence
of units up to isomorphism...). Think of vector spaces with
the tensor product, or types with the Cartesian product.

But we can also see a monoidal category as a (non-strict)
bicategory with only one object `X`. The monoical category
is then `X ⟶ X`, and composition of 1-morphisms gives the
extra operation `⊗`. The axioms are identical. See
`Mathlib.CategoryTheory.Bicategory.SingleObj`.
-/

/-
Another example is the fundamental 2-groupoid of a topological
space `X`:
- The objects are points of `X`;
- The 1-morphisms `x ⟶ y` are paths from `x` to `y`, i.e.
continuous maps `[0,1] → X` sending `0` to `x` and `1` to `y`.
- Composition of 1-morphisms is given by concatenation, and
the identities are constant paths.
- The 2-morphisms between two paths are homotopies between
the paths (fixing the end points).
-/

/-
Another example is the bicategory of spans in a category
`C` (admitting fiber products). It is not strict in general.

We will construct this example.
-/

open Limits

variable {C : Type u} [Category.{v} C]

-- The objects are objects of `C`.
variable (C) in
structure Span where
  pt : C
-- Even though `C` and `Span C` have the same objects, we
-- don't want to give them the same name, because the
-- category instance on `C` would clash the bicategory
-- instance that we will construct. So we introduce `Span C`
-- as a structure whose unique field is a term of type `C`.
-- (We could also have used a type synonym, i.e.
-- `def Span (C : Type*) := C`.)

-- Given `X, Y : C`, the 1-morphisms from `X` to `Y` are
-- spans from `X` to `Y`, i.e. diagrams
--       Z
--   f /  \ g  with f : Z ⟶ X and g : Z ⟶ Y
--   X     Y
structure OneMor (X Y : Span C) where
  roof : C
  left : roof ⟶ X.pt
  right : roof ⟶ Y.pt

-- The 2-morphisms are commutative diagrams between spans.
@[ext]
structure TwoMor {X Y : Span C} (a b : OneMor X Y) where
  hom_roof : a.roof ⟶ b.roof
  left_comp : hom_roof ≫ b.left = a.left := by aesop_cat
  right_comp : hom_roof ≫ b.right = a.right := by aesop_cat

@[simp, reassoc]
lemma TwoMor.left_comp' {X Y : Span C} (a b : OneMor X Y)
    (u : TwoMor a b) : u.hom_roof ≫ b.left = a.left :=
  u.left_comp

@[simp, reassoc]
lemma TwoMor.right_comp' {X Y : Span C} (a b : OneMor X Y)
    (u : TwoMor a b) : u.hom_roof ≫ b.right = a.right :=
  u.right_comp

-- In fact, let's make `OneMor X Y` into a category right away:
instance {X Y : Span C} : Category (OneMor X Y) where
  Hom a b := TwoMor a b
  id a := {hom_roof := 𝟙 a.roof}
  comp {a b c} u v :=
    {hom_roof := u.hom_roof ≫ v.hom_roof}
  id_comp := by aesop_cat
  comp_id := by aesop_cat
  assoc := by aesop_cat

def TwoMor.homMk {X Y : Span C} {a b : OneMor X Y}
    (u : a.roof ⟶ b.roof) (comp₁ : u ≫ b.left = a.left)
    (comp₂ : u ≫ b.right = a.right) : a ⟶ b where
      hom_roof := u
      left_comp := comp₁
      right_comp := comp₂

def TwoMor.isoMk {X Y : Span C} {a b : OneMor X Y}
    (u : a.roof ≅ b.roof) (comp₁ : u.hom ≫ b.left = a.left)
    (comp₂ : u.hom ≫ b.right = a.right) : a ≅ b where
      hom := TwoMor.homMk u.hom comp₁ comp₂
      inv := TwoMor.homMk u.inv sorry sorry
      hom_inv_id := sorry
      inv_hom_id := sorry

-- The identity 1-morphism from `X` to `X` is given by
-- taking `Z` equal to `X` and `f, g` equal to `𝟙 X`.
@[simp]
def OneMorId (X : Span C) : OneMor X X where
  roof := X.pt
  left := 𝟙 _
  right := 𝟙 _

variable [HasPullbacks C]

-- The composition of 1-morphisms is given by the following
-- diagram, that I will also draw on the board.

--      Z
--     / \            Here we take `Z` equal to the
--   Y    Y'          fiber product of `Y` and `Y'` over
--  / \f g/ \          `X'` (called `pullback f g` in mathlib).
-- X    X'   X''      The two projections give morphisms from
--                    `Z` to `Y` and `Y'`, and we compose them
--                    with the available morphisms to get
--                    morphisms `Z ⟶ X` and `Z ⟶ X''`.

#check pullback
#check pullback.fst
#check pullback.snd

@[simp]
noncomputable def OneMorComp {X Y Z : Span C}
    (a : OneMor X Y) (b : OneMor Y Z) : OneMor X Z where
      roof := pullback a.right b.left
      left := pullback.fst _ _ ≫ a.left
      right := pullback.snd _ _ ≫ b.right

-- Now for bicategory structure on `Span C`:
instance : Bicategory (Span C) where
  Hom X Y := OneMor X Y
  id X := OneMorId X
  comp {X Y Z} a b := OneMorComp a b
  homCategory X Y := instCategoryOneMor
  whiskerLeft {X X' X''} a {b b'} u :=
    -- draw the diagram! (see below for useful functions)
    {
      hom_roof := pullback.lift (pullback.fst _ _)
        (pullback.snd _ _ ≫ u.hom_roof)
        (by simp [pullback.condition])
    }
  whiskerRight {X X' X''} {a a'} u b :=
    {
      hom_roof := pullback.lift (pullback.fst _ _ ≫ u.hom_roof)
        (pullback.snd _ _) (by simp [pullback.condition])
    }
  associator {X X' X'' X'''} a b c := by
    refine TwoMor.isoMk (pullbackAssoc _ _ _ _) ?_ ?_
    · sorry
    · sorry
  leftUnitor {X X'} a := by
    refine TwoMor.isoMk ?_ ?_ ?_
    · exact asIso (pullback.snd (𝟙 X.pt) a.left)
-- Here we use the fact that mathlib knows that the pullback
-- of an isomorphism is an isomorphism (and the identity is
-- an isomorphism).
-- If a morphism `α` has an `IsIso` instance, then
-- `asIso α` is `α` upgraded to an isomorphism.
    · sorry
    · sorry
  rightUnitor {X X'} a := by
    refine TwoMor.isoMk ?_ ?_ ?_
    · exact asIso (pullback.fst a.right (𝟙 X'.pt))
    · sorry
    · sorry
  whiskerLeft_id := sorry
  whiskerLeft_comp := sorry
  id_whiskerLeft := sorry
  comp_whiskerLeft := sorry
  id_whiskerRight := sorry
  comp_whiskerRight := sorry
  whiskerRight_id := sorry
  whiskerRight_comp := sorry
  whisker_assoc := sorry
  whisker_exchange := sorry
  pentagon := sorry
  triangle := sorry

-- We need the universal property of the pullback.
#check pullback.fst
#check pullback.snd
#check pullback.condition
#check pullback.lift
#check pullback.lift_fst
#check pullback.lift_snd
#check pullback.hom_ext
#check pullback.map

-- Associativity of pullbacks.
#check pullbackAssoc
