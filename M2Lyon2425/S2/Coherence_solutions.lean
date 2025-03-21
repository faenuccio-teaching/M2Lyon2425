import Mathlib.CategoryTheory.Bicategory.Free
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Algebra.Free
import Mathlib.Logic.Relation

/-
# Coherence

The coherence theorem for bicategories says, roughly, that
if we have 1-morphisms `f, g` in a bicategory with the same
source and target, then any two 2-morphisms `f ⟶ g` that are
built solely from associators and unitors are equal. This
generalizes the triangle and pentagon axioms.

This is the basis for the `bicategory_coherence` tactic.
(There is another tactic building on this, `bicategoricalComp`,
that, given 1-morphisms `f` and `g`, automatically tries to
insert associators and unitors to make the target of `f` match
the source of `g` and so make sense of the composition of `f`
and `g`.)

In mathlib, the coherence theorem is stated in the following
way: the free bicategory on any quiver is locally thin, where
"locally thin" means that there exists at most one 2-morphism
between any two 1-morphisms.

Remember that a quiver is just an oriented graph. The free
bicategory on a quiver `Q` has as its objects the vertices of
`Q`. Its 1-morphisms are the paths in `Q`, and its 2-morphisms
are freely generated from the identities, the associators and
the unitors modulo the relations given by the bicategory axioms.
-/

universe u v w

open CategoryTheory Category
open scoped Bicategory

#print FreeBicategory

#print FreeBicategory.Hom
-- 1-morphisms in the free bicategory.
/-
inductive FreeBicategory.Hom {B : Type u} [Quiver.{v + 1} B] :
    B → B → Type max u v
  | of {a b : B} (f : a ⟶ b) : Hom a b
  | id (a : B) : Hom a a
  | comp {a b c : B} (f : Hom a b) (g : Hom b c) : Hom a c
-/

#print FreeBicategory.Hom₂
-- Representatives of 2-morphisms in the free bicategory.
/-
inductive Hom₂ {B : Type u} [Quiver.{v + 1} B] :
    ∀ {a b : FreeBicategory B}, (a ⟶ b) → (a ⟶ b) → Type max u v
  | id {a b} (f : a ⟶ b) : Hom₂ f f
  | vcomp {a b} {f g h : a ⟶ b} (η : Hom₂ f g) (θ : Hom₂ g h) :
      Hom₂ f h
  | whisker_left {a b c} (f : a ⟶ b) {g h : b ⟶ c} (η : Hom₂ g h) :
      Hom₂ (f ≫ g) (f ≫ h)
-- `η` cannot be earlier than `h` since it is a recursive argument.
  | whisker_right {a b c} {f g : a ⟶ b} (h : b ⟶ c) (η : Hom₂ f g) :
      Hom₂ (f.comp h) (g.comp h)
  | associator {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
      Hom₂ ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
  | associator_inv {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
      Hom₂ (f ≫ (g ≫ h)) ((f ≫ g) ≫ h)
  | right_unitor {a b} (f : a ⟶ b) : Hom₂ (f ≫ (𝟙 b)) f
  | right_unitor_inv {a b} (f : a ⟶ b) : Hom₂ f (f ≫ (𝟙 b))
  | left_unitor {a b} (f : a ⟶ b) : Hom₂ ((𝟙 a) ≫ f) f
  | left_unitor_inv {a b} (f : a ⟶ b) : Hom₂ f ((𝟙 a) ≫ f)
-/

/-
On the other hand, we also have the free (1-)category over
a quiver `Q`, which is given by the same construction but
without 2-morphisms. It is called the category of paths,
`CatgeoryTheory.Paths` in mathlib.
-/

#check Paths

/-
To prove the coherence theorem, we construct a normalizing
pseudofunctor from `FreeBicategory Q` to
`LocallyDiscrete (Paths Q)` and prove that it induces an
equivalence on `Hom` categories.

The idea is taken from a similar normalization procedure in
basic algebra: Suppose that you have a set `X` of letters,
consider the set `W_X` of non-associative words on `X`
with parentheses, where the empty word is denoted by `∅`.
We have a binary operation `⬝` on `W_X`, which takes words
`w` and `w'` and returns the concatenation `(w)(w')`. (`W_X`
is the free magma on `X`.)

We consider the equivalence relation on `W_X` generated by
the relations `∅ ⬝ w ∼ w`, `w ⬝ ∅ ∼ w` and
`w ⬝ (w' ⬝ w'') ∼ (w ⬝ w') ⬝ w''`. The quotient of `W_X` by
`∼` is the free monoid `M_X` on `X`.

We also consider the smallest subset `N_X` of `W_X` such that
`∅` is in `N_X`, and if `n` is in `N_X` and `x` is in `X`, then
`n ⬝ x` is in `N_X`. (These are the words that are associated
on the left.)

The normalization theorem says that there is a function
`f : W_X → N_X` such that `a ∼ b` if and only if `f a = f b`,
hence which induces an equivalence `M_X ≃ N_X`.

To prove this, we first define `F : W_X → (N_X → N_X)` by
sending ∅ to the identity, `x` in `X` to `n ↦ n ⬝ x`, and
`⬝` to composition. As `N_X → N_X` is a monoid for composition,
this descends to `M_X`. Then we set `f w = (F w) ∅`.
-/

variable (X : Type*)

inductive W
  | empty : W
  | of : X → W
  | conc : W → W → W

instance : Mul (W X) where
  mul a b := W.conc a b

inductive N
  | empty : N
  | concX : N → X → N

def inclusion (n : N X) : W X := match n with
  | N.empty => W.empty
  | N.concX n x => W.conc (inclusion n) (W.of x)

inductive relW : W X → W X → Prop
  | assoc (a b c : W X) : relW (a * b * c) (a * (b * c))
  | left : ∀ a b c d, relW (a * (b * c * d)) (a * (b * (c * d)))
  | one_left (a : W X) : relW (W.empty * a) a
  | one_right (a : W X) : relW (a * W.empty) a
  | left_one_left (a b : W X) : relW (b * (W.empty * a)) (b * a)
  | left_one_right (a b : W X) : relW (b * (a * W.empty)) (b * a)

def M := Quot (relW X)

variable {X}

lemma quot_mk_one_left (a : W X) :
    Quot.mk (relW X) (W.empty * a) =
    Quot.mk (relW X) a := Quot.sound (relW.one_left _)

lemma quot_mk_one_right (a : W X) :
    Quot.mk (relW X) (a * W.empty) =
    Quot.mk (relW X) a := Quot.sound (relW.one_right _)

lemma quot_mk_assoc (a b c : W X) :
    Quot.mk (relW X) ((a * b) * c) =
    Quot.mk (relW X) (a * (b * c)) :=
  Quot.sound (relW.assoc _ _ _)

local instance : Trans (EqvGen (relW X)) (EqvGen (relW X)) (EqvGen (relW X)) where
  trans := EqvGen.trans _ _ _

lemma relW_mul_left (a b x : W X)
    (rel : relW X a b) :
    Quot.mk (relW X) (x * a) = Quot.mk (relW X) (x * b) := by
  apply Quot.EqvGen_sound
  revert rel a b
  rintro _ _ (⟨a, b, c⟩ | ⟨a, b, c, d⟩ | ⟨a⟩ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩)
  · exact EqvGen.rel _ _ (relW.left _ _ _ _)
  · calc EqvGen (relW X) (x * (a * (b * c * d))) ((x * a) * (b * c * d)) :=
           EqvGen.symm _ _ (EqvGen.rel _ _ (relW.assoc _ _ _))
         EqvGen (relW X) _ ((x * a) * (b * (c * d))) := EqvGen.rel _ _ (relW.left _ _ _ _)
         EqvGen (relW X) _ (x * (a * (b * (c * d)))) := EqvGen.rel _ _ (relW.assoc _ _ _)
  · exact EqvGen.rel _ _ (relW.left_one_left _ _)
  · exact EqvGen.rel _ _ (relW.left_one_right _ _)
  · calc EqvGen (relW X) (x * (b * (W.empty * a))) ((x * b) * (W.empty * a)) :=
           EqvGen.symm _ _ (EqvGen.rel _ _ (relW.assoc _ _ _))
         EqvGen (relW X) _ ((x * b) * a) := EqvGen.rel _ _ (relW.left_one_left _ _)
         EqvGen (relW X) _ (x * (b * a)) := EqvGen.rel _ _ (relW.assoc _ _ _)
  · calc EqvGen (relW X) (x * (b * (a * W.empty))) ((x * b) * (a * W.empty)) :=
           EqvGen.symm _ _ (EqvGen.rel _ _ (relW.assoc _ _ _))
         EqvGen (relW X) _ ((x * b) * a) := EqvGen.rel _ _ (relW.left_one_right _ _)
         EqvGen (relW X) _ (x * (b * a)) := EqvGen.rel _ _ (relW.assoc _ _ _)

lemma relW_mul_right (a b x : W X)
    (rel : relW X a b) :
    Quot.mk (relW X) (a * x) = Quot.mk (relW X) (b * x) := by
  apply Quot.EqvGen_sound
  revert rel a b
  rintro _ _ (⟨a, b, c⟩ | ⟨a, b, c, d⟩ | ⟨a⟩ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩)
  · calc EqvGen (relW X) (a * b * c * x) ((a * b) * (c * x)) := EqvGen.rel _ _ (relW.assoc _ _ _)
         EqvGen (relW X) _ (a * (b * (c * x))) := EqvGen.rel _ _ (relW.assoc _ _ _)
         EqvGen (relW X) _ (a * ((b * c) * x)) := EqvGen.symm _ _ (EqvGen.rel _ _ (relW.left _ _ _ _))
         EqvGen (relW X) _ ((a * (b * c)) * x) := EqvGen.symm _ _ (EqvGen.rel _ _ (relW.assoc _ _ _))
  · calc EqvGen (relW X) (a * (b * c * d) * x) (a * ((b * c * d) * x)) :=
           EqvGen.rel _ _ (relW.assoc _ _ _)
         EqvGen (relW X) _ (a * ((b * c) * (d * x))) := EqvGen.rel _ _ (relW.left _ _ _ _)
         EqvGen (relW X) _ (a * (b * (c * (d * x)))) := EqvGen.rel _ _ (relW.left _ _ _ _)
         EqvGen (relW X) _ (a * (b * ((c * d) * x))) :=
           EqvGen.symm _ _ (Quot.exact _ (relW_mul_left _ _ _ (relW.left _ _ _ _)))
         EqvGen (relW X) _ (a * ((b * (c * d)) * x)) :=
           EqvGen.symm _ _ (EqvGen.rel _ _ (relW.left _ _ _ _))
         EqvGen (relW X) _ (a * (b * (c * d)) * x) := EqvGen.symm _ _ (EqvGen.rel _ _ (relW.assoc _ _ _))
  · calc EqvGen (relW X) (W.empty * _ * x) (W.empty * (_ * x)) := EqvGen.rel _ _ (relW.assoc _ _ _)
         EqvGen (relW X) _ (_ * x) := EqvGen.rel _ _ (relW.one_left _)
  · calc EqvGen (relW X) (_ * W.empty * x) (_ * (W.empty * x)) := EqvGen.rel _ _ (relW.assoc _ _ _)
         EqvGen (relW X) _ (_ * x) := EqvGen.rel _ _ (relW.left_one_left _ _)
  · calc EqvGen (relW X) (b * (W.empty * a) * x) (b * _) := EqvGen.rel _ _ (relW.assoc _ _ _)
         EqvGen (relW X) _ (b * _) := EqvGen.rel _ _ (relW.left _ _ _ _)
         EqvGen (relW X) _ (b * (a * x)) := EqvGen.rel _ _ (relW.left_one_left _ _)
         EqvGen (relW X) _ (b * a * x) := EqvGen.symm _ _ (EqvGen.rel _ _ (relW.assoc _ _ _))
  · calc EqvGen (relW X) (b * (a * W.empty) * x) (b * _) := EqvGen.rel _ _ (relW.assoc _ _ _)
         EqvGen (relW X) _ (b * (a * (W.empty * x))) := EqvGen.rel _ _ (relW.left _ _ _ _)
         EqvGen (relW X) _ ((b * _) * _) := EqvGen.symm _ _ (EqvGen.rel _ _ (relW.assoc _ _ _))
         EqvGen (relW X) _ (b * a * x) := EqvGen.rel _ _ (relW.left_one_left _ _)

lemma quot_mk_mul_right (a b c : W X)
    (eq : Quot.mk (relW X) a = Quot.mk (relW X) b) :
    Quot.mk (relW X) (a * c) = Quot.mk (relW X) (b * c) := by
  refine Quot.EqvGen_sound ?_
  set r := Function.onFun (EqvGen (relW X)) (fun x ↦ x * c)
  have h : Equivalence r :=
    Equivalence.comap (EqvGen.is_equivalence (relW X)) (fun x ↦ x * c)
  change r a b
  rw [← Equivalence.eqvGen_iff h]
  exact EqvGen.mono (fun a b rel ↦ (Quot.exact (relW X)
    (relW_mul_right a b c rel))) (Quot.exact _ eq)

@[simp]
def F (w : W X) (n : N X) : N X := match w with
  | W.empty => n
  | W.of x => N.concX n x
  | W.conc a b => (F b) (F a n)

lemma quot_mk_F (w : W X) (n : N X) :
    Quot.mk (relW X) (inclusion X (F w n)) =
    Quot.mk (relW X) ((inclusion X n) * w) := by
  match w with
  | W.empty => dsimp [F]; simp [quot_mk_one_right]
  | W.of x => dsimp [F, inclusion]; rfl
  | W.conc a b =>
    dsimp [F]
    rw [quot_mk_F]; erw [← quot_mk_assoc]
    exact quot_mk_mul_right _ _ b (quot_mk_F a n)

lemma quot_mk_F' (w : W X) :
    Quot.mk (relW X) (inclusion X (F w N.empty)) =
    Quot.mk (relW X) w := by
  simp [quot_mk_F w N.empty, inclusion, quot_mk_one_left]

lemma F_inclusion (n : N X) : F (inclusion X n) N.empty = n := by
  match n with
  | N.empty => dsimp [F, inclusion]
  | N.concX n x => dsimp [F, inclusion]; rw [F_inclusion]

@[simp]
def f_aux (x : M X) (n : N X) : N X := by
  refine Quot.liftOn x (fun a ↦ (F a) n) ?_
  rintro _ _ (⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_⟩ | ⟨_⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> simp only <;> rfl

variable (X)

@[simp]
def f : M X → N X := fun x ↦ f_aux x N.empty

@[simp]
def g : N X → M X := fun n ↦ Quot.mk (relW X) (inclusion X n)

def equiv : M X ≃ N X where
  toFun := f X
  invFun := g X
  left_inv x := by
    dsimp
    refine Quot.inductionOn x (fun w ↦ ?_)
    change Quot.mk (relW X) (inclusion X (F w N.empty)) = _
    simp [quot_mk_F']
  right_inv n := by
    dsimp
    change F _ N.empty = _
    rw [F_inclusion]



/- Coming back to bicategories.

This was all taken from the mathlib file `Mathlib.CategoryTheory.Bicategory.Coherence`,
so you can find solutions there.
-/

open Quiver (Path)

open Quiver.Path

namespace CategoryTheory

open Bicategory Category

namespace FreeBicategory

variable {B : Type u} [Quiver.{v + 1} B]

/-- Auxiliary definition for `inclusionPath`. -/
@[simp]
def inclusionPathAux {a : B} : ∀ {b : B}, Path a b → Hom a b
  | _, nil => Hom.id a
  | _, cons p f => (inclusionPathAux p).comp (Hom.of f)

/-- Category structure on `Hom a b`. In this file, we will use
`Hom a b` for `a b : B` (precisely, `FreeBicategory.Hom a b`)
instead of the definitionally equal expression `a ⟶ b` for
`a b : FreeBicategory B`. The main reason is that we have to
annoyingly write `@Quiver.Hom (FreeBicategory B) _ a b` to get
the latter expression when given `a b : B`. -/
local instance homCategory' (a b : B) : Category (Hom a b) :=
  homCategory a b

/-- The discrete category on the paths includes into the
category of 1-morphisms in the free bicategory.
-/
def inclusionPath (a b : B) :
    Discrete (Path.{v + 1} a b) ⥤ Hom a b :=
  Discrete.functor inclusionPathAux

/-- The inclusion from the locally discrete bicategory on the
path category into the free bicategory as a prelax functor.
This will be promoted to a pseudofunctor after proving the
coherence theorem. See `inclusion`.
-/
def preinclusion (B : Type u) [Quiver.{v + 1} B] :
    PrelaxFunctor (LocallyDiscrete (Paths B)) (FreeBicategory B)
  where
  obj a := a.as
  map {a b} f := (@inclusionPath B _ a.as b.as).obj f
  map₂ η := (inclusionPath _ _).map η

@[simp]
theorem preinclusion_obj (a : B) : (preinclusion B).obj ⟨a⟩ = a :=
  rfl

@[simp]
theorem preinclusion_map₂ {a b : B}
    (f g : Discrete (Path.{v + 1} a b)) (η : f ⟶ g) :
    (preinclusion B).map₂ η = eqToHom (congr_arg _
    (Discrete.ext (Discrete.eq_of_hom η))) := by
  rcases η with ⟨⟨⟩⟩
  cases Discrete.ext (by assumption)
  convert (inclusionPath a b).map_id _

/-- The normalization of the composition of `p : Path a b` and
`f : Hom b c`. `p` will eventually be taken to be `nil` and we
then get the normalization of `f` alone, but the auxiliary `p`
is necessary for Lean to accept the definition of `normalizeIso`
and the `whisker_left` case of `normalizeAux_congr` and
`normalize_naturality`.
-/
@[simp]
def normalizeAux {a : B} : ∀ {b c : B},
    Path a b → Hom b c → Path a c
  | _, _, p, Hom.of f => p.cons f
  | _, _, p, Hom.id _ => p
  | _, _, p, Hom.comp f g => normalizeAux (normalizeAux p f) g

/-- A 2-isomorphism between a partially-normalized 1-morphism in
the free bicategory to the fully-normalized 1-morphism.
-/
@[simp]
def normalizeIso {a : B} :
    ∀ {b c : B} (p : Path a b) (f : Hom b c),
      (preinclusion B).map ⟨p⟩ ≫ f ≅
      (preinclusion B).map ⟨normalizeAux p f⟩
  | _, _, _, Hom.of _ => sorry
  | _, _, _, Hom.id b => sorry
  | _, _, p, Hom.comp f g => sorry

#check whiskerRightIso
-- Use ≪≫ to compose isomophisms. (\ + ll + \ + gg)

/-- Given a 2-morphism between `f` and `g` in the free bicategory,
we have the equality `normalizeAux p f = normalizeAux p g`.
-/
theorem normalizeAux_congr {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    normalizeAux p f = normalizeAux p g := by
  rcases η with ⟨η'⟩
  apply @congr_fun _ _ fun p => normalizeAux p f
  clear p η
  induction η' with
  | vcomp _ _ _ _ => sorry
  | whisker_left _ _ ih => funext; sorry
  | whisker_right _ _ ih => funext; sorry
  | _ => sorry

/-- The 2-isomorphism `normalizeIso p f` is natural in `f`. -/
theorem normalize_naturality {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    (preinclusion B).map ⟨p⟩ ◁ η ≫ (normalizeIso p g).hom =
      (normalizeIso p f).hom ≫
        (preinclusion B).map₂ (eqToHom (Discrete.ext (normalizeAux_congr p η))) := by
  rcases η with ⟨η'⟩; clear η
  induction η' with
  | id => simp
  | vcomp η θ ihf ihg =>
    simp only [mk_vcomp, Bicategory.whiskerLeft_comp]
    slice_lhs 2 3 => rw [ihg]
    slice_lhs 1 2 => rw [ihf]
    simp
  -- p ≠ nil required! See the docstring of `normalizeAux`.
  | whisker_left _ _ ih =>
    dsimp
    sorry
    --rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ih]
    --simp
  | whisker_right h η' ih =>
    dsimp
    sorry
    --rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ih, comp_whiskerRight]
    --have := dcongr_arg (fun x => (normalizeIso x h).hom) (normalizeAux_congr p (Quot.mk _ η'))
    --dsimp at this; simp [this]
  | _ => simp; sorry

theorem normalizeAux_nil_comp {a b c : B} (f : Hom a b)
    (g : Hom b c) :
    normalizeAux nil (f.comp g) =
    (normalizeAux nil f).comp (normalizeAux nil g) := by
  induction g generalizing a with
  | id => sorry
  | of => sorry
  | comp g _ ihf ihg => sorry

/-- The normalization pseudofunctor for the free bicategory on
a quiver `B`. -/
def normalize (B : Type u) [Quiver.{v + 1} B] :
    Pseudofunctor (FreeBicategory B) (LocallyDiscrete (Paths B)) where
  obj a := ⟨a⟩
  map f := ⟨normalizeAux nil f⟩
  map₂ η := eqToHom <| Discrete.ext <| normalizeAux_congr nil η
  mapId _ := eqToIso <| Discrete.ext rfl
  mapComp f g := eqToIso <| Discrete.ext <| normalizeAux_nil_comp f g

/-- Auxiliary definition for `normalizeEquiv`. -/
def normalizeUnitIso (a b : FreeBicategory B) :
    𝟭 (a ⟶ b) ≅ (normalize B).mapFunctor a b ⋙ @inclusionPath B _ a b :=
  NatIso.ofComponents (fun f => (λ_ f).symm ≪≫ normalizeIso nil f)
    (by
      intro f g η
      erw [leftUnitor_inv_naturality_assoc, assoc]
      congr 1
      exact normalize_naturality nil η)

/-- Normalization as an equivalence of categories. -/
def normalizeEquiv (a b : B) : Hom a b ≌ Discrete (Path.{v + 1} a b) :=
  Equivalence.mk ((normalize _).mapFunctor a b) (inclusionPath a b) (normalizeUnitIso a b)
    (Discrete.natIso fun f => eqToIso (by
      obtain ⟨f⟩ := f
      induction f with
      | nil => rfl
      | cons _ _ ih =>
        ext1
        injection ih with ih
        conv_rhs => rw [← ih]
        rfl))

/-- The coherence theorem for bicategories. -/
instance locally_thin {a b : FreeBicategory B} : Quiver.IsThin (a ⟶ b) := fun _ _ =>
  ⟨fun _ _ =>
    (@normalizeEquiv B _ a b).functor.map_injective (Subsingleton.elim _ _)⟩

/-- Auxiliary definition for `inclusion`. -/
def inclusionMapCompAux {a b : B} :
    ∀ {c : B} (f : Path a b) (g : Path b c),
      (preinclusion _).map (⟨f⟩ ≫ ⟨g⟩) ≅ (preinclusion _).map ⟨f⟩ ≫ (preinclusion _).map ⟨g⟩
  | _, f, nil => (ρ_ ((preinclusion _).map ⟨f⟩)).symm
  | _, f, cons g₁ g₂ => whiskerRightIso (inclusionMapCompAux f g₁) (Hom.of g₂) ≪≫ α_ _ _ _

/-- The inclusion pseudofunctor from the locally discrete bicategory on the path category into the
free bicategory.
-/
def inclusion (B : Type u) [Quiver.{v + 1} B] :
    Pseudofunctor (LocallyDiscrete (Paths B)) (FreeBicategory B) :=
  { -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
    preinclusion B with
    mapId := fun _ => Iso.refl _
    mapComp := fun f g => inclusionMapCompAux f.as g.as }

end FreeBicategory

example (B : Type*) [Bicategory B] (X Y : B) (f g : X ⟶ Y)
    (u v : f ⟶ g) : f = g := by
  bicategory_coherence -- we have not imported the tactic...

end CategoryTheory
