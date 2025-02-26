import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-
## Bicategories

A bicategory is, informally, a category`B` where the `Hom`
types have themselves category structures. This means that,
given `X, Y : B` and `f, g : X ⟶ Y`, there is a notion of
morphism from `f` to `g`, which we call a 2-morphism
(and we refer to `f` and `g` as 1-morphisms).

A bit less informally, a bicategory is the data of a type
`B` and, for all `X, Y : B`, of a category `Hom X Y` whose
objects are the 1-morphisms from `X` to `Y`. We
also want identity 1-morphisms `id X : Hom X X` and composition
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

universe u v w

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
- The associator of three 1-morphisms `f, g, h` is denoted
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

#check Bicategory.precomposing X Y Z
#check Bicategory.postcomposing X Y Z

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
live) depends on the 1-morphisms, we cannot use that
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
category is usually presented as a category with an
extra operation on objects, often denoted by `⊗`, which
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

instance : Quiver (Span C) where
  Hom := OneMor

-- The identity 1-morphism from `X` to `X` is given by
-- taking `Z` equal to `X` and `f, g` equal to `𝟙 X`.
@[simp]
def OneMorId (X : Span C) : OneMor X X where
  roof := X.pt
  left := 𝟙 _
  right := 𝟙 _

section OneMorComp

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

-- With this, we get the `CategoryStruct` on `Span C`:
@[simp]
noncomputable instance : CategoryStruct (Span C) where
  id := OneMorId
  comp a b := OneMorComp a b

end OneMorComp


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

-- Let's make `OneMor X Y` into a category:
instance {X Y : Span C} : Category (X ⟶ Y) where
  Hom a b := TwoMor a b
  id a := {hom_roof := 𝟙 a.roof}
  comp {a b c} u v := {hom_roof := u.hom_roof ≫ v.hom_roof}
-- Note how a lot of the fields are filled by their default
-- value `by aesop_cat`.

@[simp]
lemma TwoMor.id {X Y : Span C} {f : X ⟶ Y} :
    (𝟙 f : TwoMor f f).hom_roof = 𝟙 f.roof := rfl

@[simp]
lemma TwoMor.comp {X Y : Span C} {f g h : X ⟶ Y} (u : f ⟶ g)
    (v : g ⟶ h) :
    (u ≫ v).hom_roof = u.hom_roof ≫ v.hom_roof := rfl

-- The two lemmas above look useless, but you can check
-- what happens in `TwoMor.isoMk` if you comment them.
-- Suddenly `simp` cannot solve obvious goals anymore.


@[ext (iff := false)]
lemma TwoMor.ext' {X Y : Span C} {f g : X ⟶ Y}
    {u v : (f : OneMor X Y) ⟶ g} (eq : u.hom_roof = v.hom_roof) : u = v :=
  TwoMor.ext eq
-- This allows us to use the `ext` tactic on 2-morphisms.
-- If you remove it, `aesop_cat` loses a lot of its power.

@[simp]
def TwoMor.homMk {X Y : Span C} {a b : X ⟶ Y}
    (u : a.roof ⟶ b.roof) (comp₁ : u ≫ b.left = a.left)
    (comp₂ : u ≫ b.right = a.right) : a ⟶ b where
      hom_roof := u
      left_comp := comp₁
      right_comp := comp₂

#check cancel_epi
#check eqToIso

@[simp]
def TwoMor.isoMk {X Y : Span C} {a b : X ⟶ Y}
    (u : a.roof ≅ b.roof) (comp₁ : u.hom ≫ b.left = a.left)
    (comp₂ : u.hom ≫ b.right = a.right) : a ≅ b where
      hom := TwoMor.homMk u.hom comp₁ comp₂
      inv := by
        refine TwoMor.homMk u.inv ?_ ?_
        · rw [← cancel_epi u.hom]
          aesop_cat
        · rw [← cancel_epi u.hom]
          aesop_cat
-- Hint: `cancel_epi`.

variable [HasPullbacks C]

-- Now for the bicategory structure on `Span C`:
noncomputable instance : Bicategory (Span C) where
  homCategory X Y := inferInstance
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
  whiskerLeft_id := by
    intros a b c f g
    ext
    dsimp
    refine pullback.hom_ext ?_ ?_
    rw [pullback.lift_fst]
    have := id_comp (pullback.fst f.right g.left)
    rw [this]
    simp only [comp_id, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, id_comp]
  whiskerLeft_comp := sorry
  id_whiskerLeft := by
    intros a b c f g
    ext
    dsimp
    refine pullback.hom_ext ?_ ?_
    rw [pullback.lift_fst]
    sorry
    sorry
  comp_whiskerLeft := sorry
  id_whiskerRight := sorry
  comp_whiskerRight := sorry
  whiskerRight_id := sorry
  whiskerRight_comp := sorry
  whisker_assoc := sorry
  whisker_exchange := sorry
  pentagon := by
    intros a b c d e f g h i
    dsimp
    sorry
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

/-
# Functors

A pseudofunctor `F` between bicategories `B` and `B'` is
a map `F.obj` between objects, a map `F.map` between
1-morphisms (respecting source and target) and a map
`F.map₂` between 2-morphisms (respecting source and target),
such that `F.map₂` is compatible with identities and composition,
and `F.map` is compatible with identities and composition *up
to isomorphism* (+ compatibilities with whiskering, associators
and left/right unitors).
-/
#print Pseudofunctor

/-
structure Pseudofunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
    [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  obj : B → C
  map {X Y : B} : (X ⟶ Y) → (obj X ⟶ obj Y)
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)
  map₂_id {a b : B} (f : a ⟶ b) : map₂ (𝟙 f) = 𝟙 (map f)
  map₂_comp {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    map₂ (η ≫ θ) = (map₂ η) ≫ (map₂ θ)
-- The first five fields are the `PrelaxFunctor` structure.
  mapId (a : B) : map (𝟙 a) ≅ 𝟙 (obj a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      map (f ≫ g) ≅ map f ≫ map g
  map₂_whisker_left :
    ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫
      (mapComp f h).inv := by
    aesop_cat
  map₂_whisker_right :
    ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫
      (mapComp g h).inv := by
    aesop_cat
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫
      (mapComp f g).hom ▷ map h ≫
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫
      (mapComp f (g ≫ h)).inv := by
    aesop_cat
  map₂_left_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = (mapComp (𝟙 a) f).hom ≫
      (mapId a).hom ▷ map f ≫ (λ_ (map f)).hom := by
    aesop_cat
  map₂_right_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫
      map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom := by
    aesop_cat
-/

/-
As an example, we can define a pseudofunctor from `C` to
`Span C`. Note that a 1-category can be seen as a
strict bicategory where the only 2-morphisms are identity
morphisms. To avoid instance clashes, this is called
`LocallyDiscrete C`.
-/

#synth Bicategory (LocallyDiscrete C)

#print LocallyDiscrete
-- This is again a structure with a unique field `as`.
-- So if `X : LocallyDiscrete C`, the corresponding object of
-- `C` is called `X.as`.
-- Note that if `f : X ⟶ Y` is a 1-morphisms in `LocallyDiscrete C`,
-- the corresponding morphisms of `C` is called `f.as`.

/-
The pseudofunctor from `C` to `Span C` will be the identity on
objects. It will send `f : X ⟶ Y` to the span
   X
 𝟙/ \f
X    Y
As the only 2-morphisms in `C` are identity morphisms, it will
send them to identity morphisms. In fact we will need to use
`eqToHom`, and the following function (saying that if there
is a 2-morphism between two 1-morphisms `f` and `g` in a locally
discrete bicategory, then `f` and `g` are equal):
-/
#check LocallyDiscrete.eq_of_hom

@[simp]
lemma eqToHom_hom_roof {X Y : Span C} {a b : X ⟶ Y} (eq : a = b) :
    (eqToHom eq).hom_roof = eqToHom (by rw [eq]) := by
  aesop_cat

noncomputable def ToSpan :
    Pseudofunctor (LocallyDiscrete C) (Span C) where
  obj X := {pt := X.as}
  map {X Y} f := {roof := X.as, left := 𝟙 X.as, right := f.as}
  map₂ {X Y f g} u := by
    have eq := LocallyDiscrete.eq_of_hom u
    refine eqToHom ?_
    simp [eq]
  map₂_id := by simp
  map₂_comp := by simp
  mapId X := by
    refine TwoMor.isoMk (Iso.refl _) ?_ ?_ <;> simp <;> rfl
  mapComp {X Y Z} f g := by
    refine TwoMor.isoMk ?_ ?_ ?_
    · exact (asIso (pullback.fst f.as (𝟙 _))).symm
    · simp only [LocallyDiscrete.comp_as, Iso.symm_hom, asIso_inv,
        IsIso.inv_comp_eq, comp_id]
      change pullback.fst _ _ ≫ _ = _
      simp
    · simp only [LocallyDiscrete.comp_as, Iso.symm_hom, asIso_inv,
        IsIso.inv_comp_eq]
      change pullback.snd _ _ ≫ _ = _
      dsimp
      rw [← assoc, pullback.condition]
      simp
  map₂_whisker_left := by
    intros a b c f g h η
    dsimp
    ext
    simp only [eqToHom_hom_roof, eqToHom_refl, Bicategory.whiskerLeft_eqToHom, TwoMor.comp, id_comp,
      IsIso.inv_hom_id]
  map₂_whisker_right := by
    intros a b c f g h η
    dsimp
    ext
    simp
    sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry
