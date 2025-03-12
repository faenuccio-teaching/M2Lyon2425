import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Subobject.Comma

open CategoryTheory Category Limits

universe u u' v v' w w'

section Initial

variable {C : Type u} [Category.{v} C] {D : Type u'}
  [Category.{v'} D] (G : D ⥤ C)

open Limits

/- Let `G : D ⥤ C`. For every `X : C`, we have a category
`StructuredArrow X G`, which is a special case of a
comma category.
-/

#print Comma
#print StructuredArrow

/-
The objects of `StructuredArrow X G` are morphisms
`X ⟶ G.obj Y` with `Y : D`. If `A : StructuredArrow X G`,
its fields are called `A.right` (the object of `D`) and
`A.hom` (the morphism `X ⟶ G.obj A.right`).

If `A, B : StructuredArrow X G`, a morphism `f : A ⟶ B` is
by definition a morphism `u : A.right ⟶ B.right` in `D`
such that `A.hom ≫ G.map u = B.hom`. The morphism `u`
is called `f.right` and the condition on `u` is called
`f.w`.
-/

example {X : C} {A B : StructuredArrow X G} (f : A ⟶ B) :
    0 = 0 := by
  have := A.right
  have : X ⟶ G.obj A.right := A.hom
  have := f.right
  have := f.w
  simp only [Functor.const_obj_obj, StructuredArrow.left_eq_id,
    Functor.const_obj_map, id_comp] at this
  rfl

/-
We will prove that the functor `G` has a
left adjoint if and only if, for every `X : C`, the category
`StructuredArrow X G` has an initial object.

An initial object in a category `E` is a special case of
colimit (we will see the general notion next if there is time):
it is an object `I` of `E` such that, for every object `Z : E`,
there exists a unique morphism `I ⟶ Z`.

Examples of initial objects:
- Empty types in `Type u`;
- Trivial groups in `Grp` or `CommGrp`;
- Empty topological spaces in `TopCat`;
- Any ring isomorphism to `ℤ` in `Ring`.

Some categories don't have initial objects. For example, the
category of fields doesn't, because there doesn't exist a field
that injects into all fields.
-/

#print IsInitial
#check isInitialEquivUnique

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
is given by the object `I : StructuredArrow X G` defined as
`adj.unit.app X : X ⟶ G.obj (F.obj X)`.

Indeed, if `A` is any object of `StructuredArrow X G`,
then applying the inverse of `adj.homEquiv` to
`A.hom : X ⟶ G.obj A.right` gives a morphism `u : F.obj X ⟶ A.right`.
We can prove that `u` defines a morphism `I ⟶ A` using the
properties of the adjunction.

If we have two morphisms `v, v' : I ⟶ A`, i.e.
morphisms `v.right, v'.right : F.obj X ⟶ A.right` satisfying
some condition, we want to prove that `v.right = v'.right`.
But it suffices to do this after applying `adj.homEquiv`,
which sends both morphisms to `A.hom`.
-/
def HasInitialOfLeftAdjoint {F : C ⥤ D} (adj : F ⊣ G) (X : C) :
    HasInitial (StructuredArrow X G) := by
  set I : StructuredArrow X G :=
    StructuredArrow.mk (adj.unit.app X)
  have : ∀ (A : StructuredArrow X G), Unique (I ⟶ A) := by
    intro A
    refine @Unique.mk' _ ?_ ?_
    · exact Inhabited.mk (StructuredArrow.homMk
        ((adj.homEquiv _ _).invFun A.hom) (by simp [I]))
    · refine Subsingleton.intro (fun f g ↦ StructuredArrow.hom_ext _ _ ?_)
      refine (adj.homEquiv X A.right).injective ?_
      simp only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj]
      erw [← f.w, ← g.w]
      simp
  exact hasInitial_of_unique I

/- The other direction: if each category `StructuredArrow X G`
has an initial object, then `G` has a left adjoint `F`. We will
define `F.obj X` as the `right` component of the initial object
of `StructuredArrow X G`, and the `hom` component will give us
the unit of the adjunction at `X`.

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
      map {X X'} f := (initial.to ((StructuredArrow.map f (T := G)).obj
        (initial (StructuredArrow X' G)))).right
      map_id X := by
        dsimp [FunctorOfInitialObj]
        have eq : (initial.to ((StructuredArrow.map (𝟙 X)).obj
            (⊥_ StructuredArrow X G))) = eqToHom
            (by rw [StructuredArrow.map_id]) := initial.hom_ext _ _
        simp [eq]
      map_comp {X X' X''} f g := by
        dsimp
        set u := (StructuredArrow.map f (T := G)).map (initial.to
          ((StructuredArrow.map g).obj (⊥_ StructuredArrow X'' G)))
        change _ = _ ≫ u.right
        rw [← StructuredArrow.comp_right]
        have eq : (initial.to ((StructuredArrow.map (f ≫ g)).obj (⊥_ StructuredArrow X'' G))) =
          (initial.to ((StructuredArrow.map f).obj (⊥_ StructuredArrow X' G)) ≫
          u ≫ eqToHom (by rw [StructuredArrow.map_comp])) := initial.hom_ext _ _
        rw [eq]
        dsimp
        simp

noncomputable def UnitOfInitial :
    𝟭 C ⟶ FunctorOfInitial G h ⋙ G where
      app X := (initial (StructuredArrow X G)).hom
      naturality X X' f := by
        dsimp [FunctorOfInitial]
        have := (initial.to ((StructuredArrow.map f).obj (⊥_ StructuredArrow X' G))).w
        dsimp at this
        rw [← this]
        simp

noncomputable def CounitOfInitial :
    G ⋙ FunctorOfInitial G h ⟶ 𝟭 D where
  app Y := (initial.to (StructuredArrow.mk (𝟙 (G.obj Y)) (T := G))).right
  naturality Y Y' f := by
    dsimp [FunctorOfInitial]
    have eq : (initial.to (StructuredArrow.mk (𝟙 (G.obj Y)))).right ≫ f =
        (initial.to (StructuredArrow.mk (G.map f) (T := G))).right := by
      simp only [StructuredArrow.mk_right]
      have eq : (StructuredArrow.mk (𝟙 (G.obj Y))).hom ≫ G.map f =
          (StructuredArrow.mk (G.map f)).hom := by simp
      conv_lhs =>
            rw [← StructuredArrow.homMk_right (f := (StructuredArrow.mk
              (𝟙 (G.obj Y)) (T := G))) (f' := StructuredArrow.mk (G.map f)
              (T := G)) (T := G) (g := f) eq, ← StructuredArrow.comp_right,
              initial.hom_ext ((initial.to (StructuredArrow.mk (𝟙 (G.obj Y))) ≫
              StructuredArrow.homMk (f := (StructuredArrow.mk (𝟙 (G.obj Y))
              (T := G))) (f' := StructuredArrow.mk (G.map f) (T := G))
              (g := f) eq)) (initial.to (StructuredArrow.mk (G.map f)))]
    rw [eq, ← StructuredArrow.map_map_right (T := G) (f := G.map f)
          (initial.to (StructuredArrow.mk (𝟙 (G.obj Y')))),
          ← StructuredArrow.comp_right]
    rw [initial.hom_ext ((initial.to ((StructuredArrow.map (G.map f)).obj
          (⊥_ StructuredArrow (G.obj Y') G)) ≫ (StructuredArrow.map
          (G.map f)).map (initial.to (StructuredArrow.mk (𝟙 (G.obj Y'))))))
          (initial.to (StructuredArrow.mk (G.map f)) ≫ eqToHom (by simp))]
    dsimp
    simp

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
  dsimp [FunctorOfInitial, CounitOfInitial, UnitOfInitial]
  simp only [Category.id_comp]
  rw [← StructuredArrow.map_map_right (T := G) (f := (UnitOfInitial G h).app X),
    ← StructuredArrow.comp_right]
  simp only [Functor.comp_obj, Functor.id_obj, Functor.const_obj_obj, Functor.const_map_app,
    StructuredArrow.mk_left, StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self,
    initial.to_comp]
  erw [Category.comp_id]
  change (initial.to (⊥_ (StructuredArrow X G))).right = _
  rw [← StructuredArrow.id_right]
  congr
  exact initial.hom_ext _ _

lemma RightTriangleOfInitial :
    whiskerLeft G (UnitOfInitial G h) ≫
    (G.associator (FunctorOfInitial G h) G).inv ≫
    whiskerRight (CounitOfInitial G h) G = 𝟙 (G ⋙ 𝟭 C) := by
  ext
  dsimp [FunctorOfInitial, CounitOfInitial, UnitOfInitial]
  simp only [Category.id_comp, StructuredArrow.w, StructuredArrow.mk_hom_eq_self]


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


section GroupObject

variable {C : Type u} [Category.{v} C]

/-
This section is intended to introduce you to categorical
(binary) products and terminal/final objects.

A terminal object in a category `C` is the dual notion of an
initial object: it is an object `F : C` such that, for
every `X : C`, there exists a unique morphism `X ⟶ F`.

Examples of terminal objects:
- Any one-point type in `Type u`;
- Trivial groups in `Grp` and `CommGrp`;
- Any one-point topological space in `TopCat`.

Not all categories have terminal objects. For example, `Ring`
does not, and neither does the category of fields. The category
of rings without a unit does admit a final objects (take any
zero ring).
-/

#print IsTerminal
#check isTerminalEquivUnique

/-
Now we define binary products. Let `X, Y : C`. A (binary) product
of `X` and `Y` in `C` is the data of an object `P : C`
and two morphisms `p : P ⟶ X`, `q : P ⟶ Y` such that, every
time we take `Q : C` and morphisms `p' : Q ⟶ X`, `q' : Q ⟶ Y`,
there exists a unique morphism `u : Q ⟶ P` such that
`p' = u ≫ p` and `q' = u ≫ q`.

A product of `X` and `Y` is unique up to unique isomorphism
if it exists (because of the universal property). Please
note that you should include the morphisms `p` and `q` to
get uniqueness.

Binary products are called "binary" because we could make
the same definition with three, four etc objects, or actually
with any family of objects of `C`. (For the empty family, we
recover the notion of terminal objects. Think about it!)

There are classes expressing the fact that `C` has terminal
objects, binary products etc:
-/
#print HasTerminal
#print HasBinaryProducts
#print HasFiniteProducts
#print HasProducts


/-
If a product of `X, Y : C` exists, mathlib picks an arbitrary
one using the axiom of choice and calls it `Limits.prod X Y` or
`X ⨯ Y` (\ + X). Warning, the `⨯` is not the same as the
Cartesian product symbol for types (which is `×` i.e. \ + x).
-/
#check Limits.prod
#check Limits.prod.fst -- first projection, i.e. morphism
                       -- from `X ⨯ Y` to `X`
#check Limits.prod.snd -- second projection, i.e. morphism
                       -- from `X ⨯ Y` to `Y`
#check Limits.prod.lift -- universal property of the product
#check Limits.prod.lift_fst
#check Limits.prod.lift_snd

/-
Now we come to group objects in `C`.
Let's assume that `C` has finite products. This is equivalent
to assuming the existence of terminal objects and binary products.
(You can then construct all finite products by induction.)
-/
variable [HasFiniteProducts C]

/-
The idea is that a group object in `C` is the data of:
- An object of `C`, let's call it `X`.
- A "multiplication" map, which should be a morphism `X ⨯ X ⟶ X`.
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

variable (C) in
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
  comp f g := ⟨f.1 ≫ g.1, ⟨by rw [← assoc, f.2.1, g.2.1],
    by rw [← prod.map_map, assoc, g.2.2, ← assoc, f.2.2, assoc]⟩⟩

-- The forgetful functor from group objects in `C` to `C`.
variable (C) in
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
  change (prod.map f g ≫ prod.fst) _ = _
  rw [prod.map_fst]
  rfl

lemma prod.map_snd_apply {A B C D : Type u} (f : A ⟶ B) (g : C ⟶ D)
    (x : A ⨯ C) :
    prod.snd (X := B) (prod.map f g x) = g (prod.snd (X := A) x) := by
  change (prod.map f g ≫ prod.snd) _ = _
  rw [prod.map_snd]
  rfl

lemma prod.lift_fst_apply {A B C : Type u} (f : A ⟶ B) (g : A ⟶ C) (x : A) :
    prod.fst (X := B) (prod.lift f g x) = f x := by
  change (prod.lift f g ≫ prod.fst) _ = _
  rw [prod.lift_fst]

lemma prod.lift_snd_apply {A B C : Type u} (f : A ⟶ B) (g : A ⟶ C) (x : A) :
    prod.snd (X := B) (prod.lift f g x) = g x := by
  change (prod.lift f g ≫ prod.snd) _ = _
  rw [prod.lift_snd]

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

(In fact, this shows that our definition of group objects is not
the right one. There is a class called `ChosenFiniteProducts` which
allows us to choose "nice" representatives in a category such as
`Type u`, and we should use the finite products given by this class
to define group objects. I didn't do this because I wanted to torture
you a bit. End of digression.)
-/

-- Here is the isomorphism:
#check Types.binaryProductIso

/- For the unit, we will use that `⊤_ (Type u)` has a unique
element, which is called `default`.
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
  mul p := ((Types.binaryProductIso G G).hom p).1 *
    ((Types.binaryProductIso G G).hom p).2
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
        · aesop_cat
        · ext
          dsimp
          simp only [Types.binaryProductIso_hom_comp_fst_apply,
            Types.binaryProductIso_hom_comp_snd_apply, map_mul]
          rw [prod.map_fst_apply, prod.map_snd_apply]

-- Putting all this together

-- Putting all this together into a functor.
noncomputable def CanIsoInv : Grp.{u} ⥤ GroupObject (Type u) where
  obj G := GroupObjectOfGrp G.1
  map f := HomOfMonoidHom f
  map_id G := by
    dsimp
    rw [← SetCoe.ext_iff]
    ext; rfl
  map_comp f g := by
    dsimp
    rw [← SetCoe.ext_iff]
    ext; rfl

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


section Initial

variable {C : Type u} [Category.{v} C]

/-
In the next exercise, we will manipulate arbitrary products
and equalizers.

Let `x : J → C` be a family of objects of `C`. A product of
`x` is an object `P` of `C` together with morphisms
`p j : P ⟶ x j` for every `j : J` such that, for every
`Q : C` and every family `q j : Q ⟶ x j` of morphisms of `C`,
there exists a unique `u : Q ⟶ P` such that
`q j = u ≫ p j` for every `j : J`.

Now we suppose that `C` admits products indexed by
types in `Type w`.
-/

variable [HasProducts.{w} C]

/-
Equalizers: Let `f, g : X ⟶ Y` be morphisms of `C`.
An equalizer of `f` and `g` is a morphism `i : Z ⟶ X`
such that `i ≫ f = i ≫ g` and such that, for every
morphism `i' : Z' ⟶ X` satisfying `i' ≫ f = i' ≫ g`, there
exists a unique morphism `u : Z' ⟶ Z` such that
`i' = u ≫ i`.

For example, if we are in `Type u`, we can take
`Z = {x : X | f x = g x}` and `i: Z ⟶ X` given by the inclusion.
In a category that has zero morphisms, such as `AddCommGrp`
or `ModuleCat`, an equalizer of `f : X ⟶ Y` and of the
zero morphism `0 : X ⟶ Y` is also called a kernel of `f`.

In fact we will use a generalization of equaliwers called
"wide equalizers", which are for a family of morphisms
`f j : X ⟶ Y` indexed by some type `J`. (It's a morphism
`i : Z ⟶ X` such that `i ≫ f j = i ≫ g j` for every `j`
and such that, for every morphism `i' : Z' ⟶ X` satisfying
`i' ≫ f j = i' ≫ g j`, there exists a unique morphism
`u : Z' ⟶ Z` such that `i' = u ≫ i`.)

We assume that `C` has wide equalizers.
-/

variable [HasWideEqualizers C]

/-
Suppose that there exists a family `x : J ⟶ C` such that
every `X : C` admits at least one morphism from one of the
`x j`, and suppose that `J` is `w`-small. (Which means
that `J` is equivalent to a type in `Type w`.)

We will prove that `C` has an initial object.

In the proof, we use the notion of "monomorphism". This is a
categorical version of injectivity for a morphism: a morphism
`f : X ⟶ Y` is called a monomorphism (`Mono` in lean) if, for
every object `Z` and all `g, h : Z ⟶ X`, if `g ≫ f = h ≫ f`, then
`g = h`.

For example, all equalizers and wide equalizers are monomorphisms
thanks to their universal property (and mathlib knows it, it's an
instance so should automatically be available).

The dual notion, which generalizes surjectivity, is that of an
epimorphism (`Epi` in lean) : a morphism `f : X ⟶ Y` is called an
epimorphism every object `Z` and all `g, h : Y ⟶ Z`,
if `f ≫ g = f ≫ h`, then `g = h`.
-/

-- Useful lemmas and defs:
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

lemma InitialOfFamily [HasLimits C] {J : Type*} (x : J → C)
    (wi : ∀ (X : C), ∃ (j : J), Nonempty (x j ⟶ X)) [Small.{w} J] :
    HasInitial C := by
  have : HasLimitsOfShape (Discrete J) C :=
    hasLimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink _)).symm
  -- We first establish that products indexed by `J` exist in `C`. As `J`
  -- is not in `Type w` but only `w`-small, this takes a couple of
  -- lemmas.
  set X := ∏ᶜ x -- this is the notation for the product of a family
  set I := wideEqualizer (fun (u : X ⟶ X) ↦ u)
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
    refine Inhabited.mk ?_
    set i := Classical.choose (wi A)
    set u := Classical.choice (Classical.choose_spec (wi A))
    set g : X ⟶ x i := Pi.π x i
    exact g ≫ u
  have : ∀ (A : C), Unique (I ⟶ A) := by
    intro A
    refine @Unique.mk' _ ?_ ?_
  -- Then we prove that each `A : C` admits a unique morphism from `Y`.
    · exact Inhabited.mk (limit.π (parallelFamily
        (fun (u : X ⟶ X) ↦ u)) WalkingParallelFamily.zero ≫ (IX A).default)
  -- For the existence, we use tha fact that there exists a morphism
  -- `i : Y ⟶ X`.
    · refine Subsingleton.intro (fun f g ↦ ?_)
      set Z := equalizer f g
      set j : Z ⟶ I := limit.π (parallelPair f g) WalkingParallelPair.zero
      set k := (IX Z).default
      set i : I ⟶ X := wideEqualizer.ι (fun (u : X ⟶ X) ↦ u)
      have eq : i ≫ k ≫ j ≫ i = i := by
        conv_rhs => rw [← Category.comp_id i]
        exact wideEqualizer.condition (f := fun (u : X ⟶ X) ↦ u) _ _
      have : Mono i := inferInstance
      have eq' : (i ≫ k) ≫ j = 𝟙 _ := by
        rw [← cancel_mono i, Category.assoc, Category.assoc, Category.id_comp]
        exact eq
      have : Epi j := epi_of_epi_fac eq'
      exact eq_of_epi_equalizer
  -- For the uniqueness, suppose that we have `f, g : Y ⟶ A`.
  -- We take `j : Z ⟶ Y` the equalizer of `f` and `g`.
  -- Then `i ≫ k ≫ j ≫ i = i` because `Y` is the (wide) equalizer of
  -- all the morphisms `X ⟶ X`, so `(i ≫ k) ≫ j = 𝟙 Y` because `i`
  -- is a monomorphism (see `Mono`), so `j` is an epimorphism (`Epi`),
  -- which implies that `f = g` because `j` is the equalizer of `f` and `g`.
  exact hasInitial_of_unique I

end Initial

variable {C : Type u} [Category.{v} C]

variable {J : Type w} [Category.{w'} J]

section LimitsColimits
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

end LimitsColimits

/- Let's do some exercises to learn to manipulate (co)limits, and
let's open the namespace `Limits` to shorten the declarations.
-/

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
      refine (adj.homEquiv _ _).toFun ?_
      set c':= (Cones.postcompose (whiskerLeft K adj.counit)).obj (G.leftAdjoint.mapCone s)
      exact hc.lift c'
    · dsimp
      rw [← Adjunction.homEquiv_naturality_right]
      simp
    · dsimp
      refine (adj.homEquiv _ _).symm.injective ?_
      simp
      refine hc.hom_ext (fun j ↦ ?_)
      refine (adj.homEquiv _ _).injective ?_
      simp only [assoc, Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj,
        Functor.map_comp, Adjunction.unit_naturality_assoc,
        Adjunction.right_triangle_components_assoc, IsLimit.fac, Cones.postcompose_obj_pt,
        Functor.mapCone_pt, Cones.postcompose_obj_π, NatTrans.comp_app, Functor.const_obj_obj,
        Functor.mapCone_π_app, whiskerLeft_app, Adjunction.right_triangle_components, comp_id]
      exact eq j

end Preserves

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
    ext j
    have : Mono (j.1.hom) := j.2
    rw [← cancel_mono j.1.hom]
    simp only [Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj, Over.forget_obj,
      MonoOver.forget_obj_left, Category.assoc]
    have := limit.w (MonoOver.forget X ⋙ Over.forget X) (j := j)
      (j' := MonoOver.mk' (𝟙 X)) (MonoOver.homMk j.1.hom)
    change _ ≫ j.1.hom = MinimalSubobjectTo X at this
    rw [this]
    exact eq

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
    have : Mono (j.1.hom) := j.2
    rw [← cancel_mono j.1.hom]
    dsimp [v]
    have := limit.w (MonoOver.forget X ⋙ Over.forget X) (j' := MonoOver.mk' (𝟙 X)) (MonoOver.homMk j.1.hom)
    change _ ≫ j.1.hom = MinimalSubobjectTo X at this
    rw [Category.assoc, this, Category.id_comp]
    rfl
  have eq' : v ≫ u = 𝟙 (MinimalSubobject X) := by
    rw [← cancel_mono (MinimalSubobjectTo X)]
    dsimp [v]
    rw [Category.assoc, Category.id_comp]
    have := limit.w (MonoOver.forget X ⋙ Over.forget X) (j' := MonoOver.mk' (𝟙 X)) (MonoOver.homMk j.1.hom)
    change _ ≫ u ≫ MinimalSubobjectTo X = _ at this
    rw [this]
    rfl
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
    rw [h]
    intro i u
    apply_fun (fun k ↦ k ≫ Pi.π (fun i ↦ ∏ᶜ fun _ ↦ x i) i) at eq
    rw [Category.assoc, Pi.lift_π (f := fun (i : I) ↦ (∏ᶜ fun (_ : X ⟶ x i) ↦ x i))
      (fun _ ↦ (Pi.lift (fun u ↦ u))) i, Category.assoc,
      Pi.lift_π (f := fun (i : I) ↦ (∏ᶜ fun (_ : X ⟶ x i) ↦ x i))
      (fun _ ↦ (Pi.lift (fun u ↦ u))) i] at eq
    apply_fun (fun k ↦ k ≫ Pi.π (fun _ ↦ x i) u) at eq
    rw [Category.assoc,
      Pi.lift_π (f := fun (_ : X ⟶ x i) ↦ x i) (fun u ↦ u) u,
      Category.assoc,
      Pi.lift_π (f := fun (_ : X ⟶ x i) ↦ x i) (fun u ↦ u) u] at eq
    exact eq

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
    have : IsIso (equalizer.ι f g) := MinimalSubobjectIsMinimal _ _
    exact eq_of_epi_equalizer
  have : ∀ (A : C), Inhabited (e ⟶ A) := by
    intro A
    refine Inhabited.mk ?_
    set u : ∏ᶜ x ⟶ ∏ᶜ (fun (i : I) ↦ (∏ᶜ fun (_ : A ⟶ x i) ↦ x i)) :=
      Pi.map (fun _ ↦ (Pi.lift (fun _ ↦ 𝟙 _)))
    set B := pullback (CogeneratingMono x A) u
    have := CogeneratingMonoIsMono x h A
    set j : MonoOver X := MonoOver.mk' (pullback.snd (CogeneratingMono x A) u)
    set v : e ⟶ B := limit.π (MonoOver.forget X ⋙ Over.forget X) j
    exact v ≫ pullback.fst (CogeneratingMono x A) u
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
  rw [StructuredArrow.hom_eq_iff, h]
  refine ⟨fun h ↦ (fun i f ↦ ?_), fun h ↦ (fun i f ↦ ?_)⟩
  · rw [StructuredArrow.hom_eq_iff, StructuredArrow.comp_right,
      StructuredArrow.comp_right]
    exact h i.1 f.right
  · have := h ⟨i, b.hom ≫ G.map f⟩ (StructuredArrow.homMk f (by simp))
    exact (StructuredArrow.hom_eq_iff _ _).mp this


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
  · sorry  -- using `sorry` here because the necessary instances are not in our
           -- old version of mathlib (but they are in the current version)
  · exact StructuredArrow.hasLimitsOfSize
  · infer_instance

end SpecialAdjointFunctorTheorem

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
-/

def SolutionSetCondition := ∀ (X : C), ∃ (I : Type u) (_ : Small.{v'} I)
  (y : I → D) (f : (i : I) → (X ⟶ G.obj (y i))), ∀ (Y : D) (h : X ⟶ G.obj Y),
  ∃ (i : I) (g : y i ⟶ Y), h = f i ≫ G.map g

/-
The idea of the proof is that, under the conditions
of the theorem, every category `StructuredArrow X G`
will have an initial object, by a lemma called `InitialOfFamily`
that we proved before in this file.
-/


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
  -- We use `InitialOfFamily` (proved above) to show that
  -- `StructuredArrow X G` has an initial object.
  obtain ⟨I, _, y, f, h⟩ := h X
  set a : I → StructuredArrow X G := fun i ↦ StructuredArrow.mk (f i)
  refine InitialOfFamily a ?_
  intro b
  obtain ⟨i, g, comm⟩ := h b.right b.hom
  use i
  exact Nonempty.intro (StructuredArrow.homMk g comm.symm)

end GeneralAdjointFunctorTheorem
