-- Credit: I stole (almost)  everything from *Mathematics in Lean*.
import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Quotient
import Mathlib.Tactic

open Classical

section Morphisms

/- How do we define morphisms of groups/monoids? Just like for groups, we have two
choices: define bundled morphisms as a structure containing a function plus some
conditions on it, or define a `IsMorphism` structure that takes a function as an
argument.-/

@[ext]
structure MonoidHom₁ (M N : Type*) [Monoid M] [Monoid N] where
-- We use the mathlib classes now.
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = (toFun x) * (toFun y)

-- Not the @[ext] tag.
#check MonoidHom₁.ext

structure IsMonoidHom₁ {M N : Type*} [Monoid M] [Monoid N] (f : M → N) where
  map_one : f 1 = 1
  map_mul : ∀ (x y : M), f (x * y) = (f x) * (f y)

/- In this case, mathlib chose the first solution. But that's just for
algebraic structures; for example, continuous maps are functions with a `Continuous`
structure on them.-/

def f : MonoidHom₁ (ℕ × ℕ) ℕ where
  toFun p := p.1 * p.2
  map_one := by simp only [Prod.fst_one, Prod.snd_one, mul_one]
  map_mul p p' := by simp only [Prod.fst_mul, Prod.snd_mul]; ring

/-
#check f ⟨2,3⟩ -- we can't apply a `MonoidHom₁` to an element, which is annoying
-/

#check f.toFun ⟨2,3⟩
#eval! f.toFun ⟨2,3⟩

/- We would like to able to write `f ⟨2,3⟩` instead of `f.toFun ⟨2,3⟩`. We do this
using the `CoeFun` class, which is a class for objects that can be coerced into
functions.-/

#print CoeFun

instance {G H : Type*} [Monoid G] [Monoid H] :
    CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

#check f ⟨2,3⟩

attribute [coe] MonoidHom₁.toFun --in the tactic, the coercion of a `MonoidHom₁` `f` to
                                -- a function will be displayed as `↑f`

#check f ⟨2,3⟩

namespace MonoidHom₁
-- any definitions and lemmas until the end of this namespace (i.e. when we see `end MonoidHom₁`) will
-- be prefixed with `MonoidHom₁.`

lemma map_pow {M N : Type*} [Monoid M] [Monoid N] (f : MonoidHom₁ M N) (a : M) (n : ℕ) :
    f (a ^ n) = (f a) ^ n := by
  induction' n with n hn
  · simp; rw [f.map_one]
  · rw [pow_succ, f.map_mul, hn, pow_succ]

end MonoidHom₁

/- But soon we will have another problem, this time with inheritance. Because morphisms
are bundled, Lean will not now that a morphism of rings is a morphism of monoids, and
so we will not be able to apply the lemmas about morphisms of monoids to morphisms
of rings.-/

-- If we define morphisms of rings like so:
@[ext]
structure AddMonoidHom₁ (G H : Type*) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

@[ext]
structure RingHom₁ (R S : Type*) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S
-- then every time we want to apply a lemma about morphisms of monoids to
-- a morphism of rings `f`, we'll have to apply it to `f.toMonoidHom₁` or
-- `f.toAddMonoidHom₁`. :-(

section RingHomCoe_first_try

local instance {R S : Type*} [Ring R] [Ring S] :
    CoeFun (RingHom₁ R S) (fun _ ↦ R → S) where
  coe := MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁
-- using `local` because I don't want this unconvenient instance to persist after
-- I close the section

/-
attribute [coe] (MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁) -- does not work :-(
-/

/-
example {R S : Type*} [Ring R] [Ring S] (f : RingHom₁ R S) (a : R) (n : ℕ) :
    f (a ^ n) = (f a) ^ n := by
  erw [MonoidHom₁.map_pow] -- does not work
  -- (okay, so it would here if we do `simp` first, but this is very simple situation)
-/

end RingHomCoe_first_try

/- Do we want to coerce all the ring morphisms into monoid morphisms every time we need to apply
a lemma about monoid morphism? (But what if we want to apply a lemma about ring morphisms next?)
Or do we want to rewrite all the lemmas about monoid morphisms so that they apply to ring morphisms?
The answer is "neither".

What we do instead is define a class for "things that look like a set of monoid morphisms".
-/

section MisguidedStuff

class MonoidHomClass₁ (F : Type*) (M N : Type*) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

/- Then we can tell Lean that both `MonoidHom₁` and `RingHom₁` are instances of that class.-/

instance (M N : Type*) [Monoid M] [Monoid N] : MonoidHomClass₁ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type*) [Ring R] [Ring S] : MonoidHomClass₁ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul

namespace MonoidHomClass₁
-- any definitions and lemmas until the end of this namespace (i.e. when we see `end MonoidHom₁`) will
-- be prefixed with `MonoidHom₁.`

lemma map_pow {M N F : Type*} [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] (f : F) (a : M) (n : ℕ) :
    toFun f (a ^ n) = (toFun f a : N) ^ n := by
  induction' n with n hn
  · simp; rw [map_one]
  · rw [pow_succ, map_mul, hn, pow_succ]

end MonoidHomClass₁

example {R S : Type*} [Ring R] [Ring S] (f : RingHom₁ R S) (a : R) (n : ℕ) :
    MonoidHomClass₁.toFun f (a ^ n) = (MonoidHomClass₁.toFun f a : S) ^ n := by
  rw [MonoidHomClass₁.map_pow]
-- Yay! Except that we lost our coercions to functions, so applying `f` to elements is horrible again.

/-
-- So why not define a `CoeFun` instance on `MonoidHomClass₁`?
--set_option synthInstance.checkSynthOrder false in
local instance badInst {F M N : Type*} [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] :
    CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun
-- oops, strange error :-((((
-/

/- Okay, what is the problem with this instance? Suppose that Lean wants to apply a coercion
to `f : F`, in order to make `f` into a function `M → N`. The problem is that Lean does not
know in which order it should look for `F`, `M` and `N`. If it looks for `M` and `N` first,
the type class inference would have to go through *every* type it knows with
a monoid instance, which might take a very long time.  If it looks for `F` first, then
for the `MonoidHomClass₁ F M N` instance on `F`, then this will tell it what `M` and
`N`. So we need a way to tell it to find `F` first, then deduce `M` and `N`. This it
done using a function called `outParam`, like so:
-/

class MonoidHomClass₂ (F : Type*) (M N : outParam Type*) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance {F M N : Type*} [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] :
    CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun

-- Let's put `MonoidHomClass₂` instances on monoid and ring morphisms.

instance (M N : Type*) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type*) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul

namespace MonoidHomClass₂

lemma map_pow {M N F : Type*} [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) (a : M) (n : ℕ) :
    f (a ^ n) = (f a : N) ^ n := by -- coercions work now
  induction' n with n hn
  · simp; rw [map_one]
  · rw [pow_succ, map_mul, hn, pow_succ]

end MonoidHomClass₂

example {R S : Type*} [Ring R] [Ring S] (f : RingHom₁ R S) (a : R) (n : ℕ) :
    f (a ^ n) = (f a : S) ^ n := by
  rw [MonoidHomClass₂.map_pow]

end MisguidedStuff

/- To finish, we would like to use a better coercion, which also remembers the fact
that coercing a monoid morphism to a function is an injective.

For his, we use the class `FunLike`. An instance `[FunLike F α β]` means that `F`
behaves like a set of functions from `α` to `β`. More precisely, it means that
there is a coercion from `F` to `α → β` (called `FunLike.coe`), plus a condition
that this coercion is injective (called `FunLike.coe_injective'`).

Actually, `FunLike` is just an abbreviation for `DFunLike`, which is the same
thing but with dependent functions.
-/

#print FunLike
#print DFunLike

class MonoidHomClass₃ (F : Type*) (M N : outParam Type*) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type*) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' _ _ := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul

section Exo

/- Adapt the ideas above to define order-preserving morphisms, and then
order-preserving monoid morphisms.-/

@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
    MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β] extends
    DFunLike F α (fun _ ↦ β) where
  le_of_le := ∀ (f : F) (a a' : α), a ≤ a' → f a ≤ f a'

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where
  coe := OrderPresHom.toFun
  coe_injective' _ _ := OrderPresHom.ext

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
      coe f := f.toFun
      coe_injective' _ _ := OrderPresMonoidHom.ext

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β where
      coe f := f.toFun
      coe_injective' _ _ := OrderPresMonoidHom.ext
      map_one f := f.map_one
      map_mul f := f.map_mul

end Exo

end Morphisms

section Subgroups

/- The goals here are:

(1) Given a type `G` with a group structure, define a type `Subgroup G`
whose inhabitants are sets in `G` stable by the group operations.
We would like subgroups to behave as sets as much as possible, for
example we want to able to talk about their elements without
extra effort.

(2) Given `H : Subgroup G`, have an "automatic" group structure on
`H` (or rather on the coercion of `H` to a type).
-/

variable (G : Type*) [Group G]

/-Remember that a `Set` in `G` is by definition a function `G → Prop`.
A subgroup is a `Set` with certain properties, so it is just a function
with the corresponding properties. We want an automatic coercion from
the type `Subgroup G` to `Set G`, so one solution would be to
use a `FunLike` instance as in the case of morphisms. But we want to
make a distinction between `Set X` and `X → Prop` at the hman level, so
instead we use a related class called `SetLike`.
-/

#print SetLike -- a class for types that look like types of sets
-- (`SetLike A G` comes with a coercion `SetLike.coe : A → Set G`,
-- and a condition saying that this coercion is injective)

@[ext] -- creates a theorem saying that subgroups are equal if their carriers are
structure Subgroup₁ where
  /-- The carrier of a subgroup. -/
  carrier : Set G
  /-- The product of two elements of a subgroup belongs to the subgroup. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The inverse of an element of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier
  /-- The unit element belongs to the subgroup. -/
  one_mem : 1 ∈ carrier

#print Subgroup₁ --note that `G` and `Group G` are arguments

/-- Subgroups in `G` can be seen as sets in `G`. -/
instance : SetLike (Subgroup₁ G) G where
  coe := Subgroup₁.carrier
  coe_injective' _ _ := Subgroup₁.ext

/- Examples of the coercion to sets un action:-/

example (H : Subgroup₁ G) : 1 ∈ H := H.one_mem   -- elements of a subgroup

example (H : Subgroup₁ G) (α : Type) (f : G → α) := f '' H  -- image by a function

/- Now for the group structure on subgroups.

We have an automatic coercion from sets to types, so we get a coercion
from subgroups to types:
-/

example (H : Subgroup₁ G) (x : H) : 0 = 0 := by
  set x' : G := x.1
  set x'' : G := x.val
  set x''' : G := (x : G)
  have xprop := x.2
  have xprop' := x.property
  rfl

/- Our main tool to prove things about terms of type `↥H` is the
theorem `SetCoe.ext` (also provided by `SetLike`), which says that
the function `↥H → G` sending `x` to `x.val` is injective.-/

#print SetCoe.ext -- If `a, b : ↥H`, then `a = b` (in `↥H`) as soon as
--`a.val = b.val` (in `G`).

instance Subgroup₁Group (H : Subgroup₁ G) : Group H where
  mul x y := ⟨x*y, H.mul_mem x.property y.property⟩
  mul_assoc x y z := by
    apply SetCoe.ext
    exact mul_assoc (x : G) y z
  one := ⟨1, H.one_mem⟩
  one_mul x := SetCoe.ext (one_mul (x : G))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : G))
  inv x := ⟨x⁻¹, H.inv_mem x.property⟩
  inv_mul_cancel x := SetCoe.ext (inv_mul_cancel (x : G))

/- Just like with morphisms, we will later define subrings, or submodules, and
we will want Lean to know that they are also subgroups (so the lemmas we proved
for subgroups can apply without extra effort). So we define a `SubgroupClass₁` for
"things that behave like a type of subgroups", and put a `SubgroupClass₁` instance
on `Subgroup₁`.-/

class SubgroupClass₁ (S : Type*) (G : Type*) [Group G] [SetLike S G] : Prop where
  mul_mem : ∀ (s : S) {a b : G}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance : SubgroupClass₁ (Subgroup₁ G) G where
  mul_mem := Subgroup₁.mul_mem
  one_mem := Subgroup₁.one_mem
  inv_mem := Subgroup₁.inv_mem

section BadIdea

/-
class SubgroupClass₂ (S : Type*) (G : Type*) [Group G] extends SetLike S G where
  mul_mem : ∀ (s : S) {a b : G}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s
-/
-- This is really a bad idea: leaving it in the code causes
-- timeouts later!

class SubgroupClass₃ (S : Type*) (G : outParam Type*) [Group G] extends SetLike S G where
  mul_mem : ∀ (s : S) {a b : G}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance : SubgroupClass₃ (Subgroup₁ G) G where
  mul_mem := Subgroup₁.mul_mem
  one_mem := Subgroup₁.one_mem
  inv_mem := Subgroup₁.inv_mem

end BadIdea

/- The intersection of two subgroups is a subgroup.-/

instance : Inf (Subgroup₁ G) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩
      inv_mem := fun hx ↦ ⟨S₁.inv_mem hx.1, S₂.inv_mem hx.2⟩
      }⟩

#print Inf

-- This instance serves to represent the "inf of two elements" function. It comes with
-- a notation which is A ⊓ B`. (Type with \ + glb, or \ + inf.)

-- Note that we do not (yet) prove that this is actually the inf! This is
-- provided by another instance, called `SemilatticeInf` (which extends `Inf`,
-- so it can use the notation `⊓`).

#print SemilatticeInf

instance : SemilatticeInf (Subgroup₁ G) where
  inf := Inf.inf
  le H K := H ≤ K
  lt H K := H < K
  le_refl := le_refl
  le_trans H K L := le_trans
  lt_iff_le_not_le H K := lt_iff_le_not_le
  le_antisymm H K := le_antisymm
  inf_le_left H K := by
    intro x hx
    exact hx.1
  inf_le_right H K := fun _ h ↦ h.2
  le_inf := by
    intro H K L hHK hHL
    intro x hx
    constructor
    · exact hHK hx
    · exact hHL hx

-- Less code duplication this way:
instance : SemilatticeInf (Subgroup₁ G) :=
  {SetLike.instPartialOrder with
   inf := Inf.inf
   inf_le_left := by intro H K x hx; exact hx.1
   inf_le_right := by intro H K x hx; exact hx.2
   le_inf := by intro H K L hHK hHL x hx; exact ⟨hHK hx, hHL hx⟩
   }

/- We also a "sup" function on subgroups, which we denote by
`⊔` (type using \ + lub or \ + sup). In fact, subgroups form a
complete lattice.-/


/- We finally talk about quotients. Ot simplify the situation, we'll
stick to commutative groups (`CommGroup`).-/

variable {A : Type*} [CommGroup A]

/- In Lean (and Coq/Rocq), a type with a distinguished equivalence
relation is called a `Setoid`. The type is an argument of the
`Setoid` class, so we write `Setoid α` to say that we are
fixing an equivalence relation on `α`.

This comes with a notation `a ≈ b` to say that `a,b : α` are
equivalence. (type using \ + ~~)
-/

#print Setoid
#print Equivalence

/- Given `s : Setoid α`, we can form the quotient of `α` by the
equivalence relation, called `Quotient s`. It comes with a certain
number of functions and properties:
- `Quotient.mk s : α → Quotient s` is the quotien map;
- `Quotient.rep : Quotient s → α` sends `x : Quotient s` to a lift
of `x`;
- `Quotient.lift` : a theorem saying that, if `f : α → β` is a function
such that `a ≈ b → f a = f b`, then `f` induces a function
`g : Quotient s → β` such that `g ∘ Quotient.mk s = f`;
- `Quotient.sound` : for all `a,b : α`, if `a ≈ b`, then
`Quotient.mk s a = Quotient.mk s b`.

(This is a difference between Lean and Coq/Rocq: Lean has quotients
by default.)
-/

-- Given a subgroup `B` of `A`, define the corresponding setoid:
-- `x,y : A` are quivalent if and only if `x*y⁻¹ ∈ B`.
def Subgroup.Setoid (B : Subgroup A) : Setoid A  where
  r := fun x y ↦ x*y⁻¹ ∈ B
  iseqv := {
    refl := fun x ↦ by simp only [mul_inv_cancel]; exact B.one_mem
    symm := fun h ↦ by have := B.inv_mem h
                       simp only [mul_inv_rev, inv_inv] at this
                       exact this
    trans := fun h₁ h₂ ↦ by have := B.mul_mem h₁ h₂; group; group at this; exact this
  }

instance : HasQuotient A (Subgroup A) where
  quotient' := fun B ↦ Quotient B.Setoid
-- This just allows us to write `A ⧸ B` instead of `Quotient B.Setoid`.
-- Type `⧸` using \ + quot.

def QuotientGroup₁.mk (B : Subgroup A) : A → A ⧸ B := Quotient.mk B.Setoid
-- So we can write `QuotientGroup₁.mk B` instead of `Quotient.mk B.Setoid`.

-- Multiplication on the quotient.
instance (B : Subgroup A) : Mul (A ⧸ B) where
  mul := Quotient.map₂' (· * ·) (by
    intro a b hab c d hcd
    simp only
    change (a * c) * (b * d)⁻¹ ∈ B
    have : a * c * (b * d)⁻¹ = (a * b⁻¹) * (c * d⁻¹) := by
      simp only [mul_inv_rev]
      conv_lhs => rw [mul_assoc, ← mul_assoc c, mul_comm _ b⁻¹, ← mul_assoc a]
    rw [this]
    exact B.mul_mem hab hcd)

-- Unit in the quotient.
instance (B : Subgroup A) : One (A ⧸ B) where
  one := QuotientGroup₁.mk B (1 : A)

-- Inverse function on the quotient.
instance (B : Subgroup A) : Inv (A ⧸ B) where
  inv := Quotient.map' (fun a ↦ a⁻¹)
    (by intro a b h
        simp only
        change a⁻¹ * (b⁻¹)⁻¹ ∈ B
        have : a⁻¹ * (b⁻¹)⁻¹ = (a * b⁻¹)⁻¹ := by
          simp only [inv_inv, mul_inv_rev]; rw [mul_comm]
        rw [this]
        exact B.inv_mem h
    )

-- The quotient is a commutative group.
instance (B : Subgroup A) : CommGroup (A ⧸ B) where
  mul := _ * _
  mul_assoc := by
    intro x y z
    apply Quotient.inductionOn₃ (motive := fun (x y z : A ⧸ B) ↦ (x * y) * z = x * (y * z))
    intro a b c
    change QuotientGroup₁.mk B ((a * b) * c) = QuotientGroup₁.mk B (a * (b * c))
    rw [mul_assoc]
  one := 1
  one_mul := by
      intro x
      apply Quotient.inductionOn (motive := fun (x : A ⧸ B) ↦ 1 * x = x)
      intro a
      change QuotientGroup₁.mk B (1 * a) = _
      rw [one_mul]; rfl
  mul_one := by
      intro x
      apply Quotient.inductionOn (motive := fun (x : A ⧸ B) ↦ x * 1 = x)
      intro a
      change QuotientGroup₁.mk B (a * 1) = _
      rw [mul_one]; rfl
  inv := Inv.inv
  inv_mul_cancel := by
    intro x
    apply Quotient.inductionOn (motive := fun (x : A ⧸ B) ↦ x⁻¹ * x = 1)
    intro a
    change QuotientGroup₁.mk B (a⁻¹ * a) = 1
    rw [inv_mul_cancel]; rfl
  mul_comm := by
    intro x y
    apply Quotient.inductionOn₂ (motive := fun (x y : A ⧸ B) ↦ (x * y = y * x))
    intro a b
    change QuotientGroup₁.mk B (a * b) = QuotientGroup₁.mk B (b * a)
    rw [mul_comm]

-- Exercise: define `QuotientGroup₁.mk B` as a group morphism (call
-- it something like `QuotientMorphism₁ B`).

def QuotientMorphism₁ (B : Subgroup A) : A →* A ⧸ B where
  toFun := QuotientGroup₁.mk B
  map_one' := rfl
  map_mul' _ _ := rfl

end Subgroups


/- More exercises.-/

/- First here are some tactics to work in groups:
(1) `group` proves identities that hold in any group:-/

example {G : Type*} [Group G] (x y z : G) :
    x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by group

/-(2) proves identities that hold in any abelian group:-/

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

/- The conjugate of a subgroup of `G` by an element of `G`.-/

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1, H.one_mem
    group
  inv_mem' := by
    dsimp
    intro x hx
    obtain ⟨h, mem, cond⟩ := hx
    use h⁻¹, H.inv_mem mem
    rw [cond]; group
  mul_mem' := by
    dsimp
    intro x y hx hy
    obtain ⟨h₁, mem₁, cond₁⟩ := hx
    obtain ⟨h₂, mem₂, cond₂⟩ := hy
    use h₁ * h₂, H.mul_mem mem₁ mem₂
    rw [cond₁, cond₂]; group


/- Group actions. Mathematically, an action of a group `G` on
a type `X` is just a morphism of groups `φ : G →* Equiv.Perm X` (`→*`
is mathlib's notation for a monoid morphism, and `Equiv.Perm X` is
the type of permutations of `X`, which has a group structure
given by the instance `Equiv.Perm.permGroup`).

But, just as in pen-and-paper math, we don't want to write
`φ` all the time. So mathlib introduces a class for (multiplicative)
group actions, called `MulAction`.
-/

#print MulAction

--We can recover `φ` using `MulAction.toPermHom`:
example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  MulAction.toPermHom G X

-- Example: the action of `G` on its subgroups by conjugation.
example {G : Type*} [Group G] : MulAction G (Subgroup G) where
  smul x H := conjugate x H
  one_smul H := by
    change conjugate 1 H = H
    ext h
    simp only [conjugate, one_mul, inv_one, mul_one, exists_eq_right', Subgroup.mem_mk,
      Set.mem_setOf_eq]

  mul_smul x y H:= by
    change conjugate (x * y) H = conjugate x (conjugate y H)
    ext g
    simp only [conjugate, mul_inv_rev, Subgroup.mem_mk, Set.mem_setOf_eq]
    constructor
    · intro ⟨h, mem, cond⟩
      use y * h * y⁻¹
      constructor
      · use h, mem
      · rw [cond]; group
    · intro ⟨g', ⟨h, mem, cond₁⟩, cond₂⟩
      use h, mem
      rw [cond₂, cond₁]; group

/- An exercise about quotients: let `G` be a finite group,
and let `H` and `K` be disjoint normal subgroups of `G`
such that the cardinal of `G` is the product of the cardinals
of `H` and `K`. Then `G` is isomorphic to `H × K`.

Here `Disjoint H K` means that `H ⊓ K = ⊥` (where `⊥` is the
smallest subgroup, i.e. the trivial subgroup), or rather it's
equivalent by `disjoint_iff`.
-/

section
variable {G : Type*} [Group G] {H K : Subgroup G}

/- First we prove that `card(G ⧸ H) = card K`. Here are some useful
theorems.-/
#check Nat.card_pos -- The `Nonempty α` argument will be automatically inferred
                    -- if `α` has a `Group` instance. (In theory at least...)
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

#synth One H
#synth Nonempty H
-- This timeouts because of one of the definitions in the `BadIdea` section.
-- We can comment the definition of add the following line to cheat:
-- local instance : Nonempty H := One.instNonempty

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
  have : Nonempty H := One.instNonempty
  rw [← Subgroup.index_mul_card H, mul_comm] at h'
  have := Nat.eq_of_mul_eq_mul_left Nat.card_pos h'
  rw [← this, Subgroup.index_eq_card]

variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

/- Helper functions.-/
#check Nat.bijective_iff_injective_and_card
#check MonoidHom.ker_eq_bot_iff
#check MonoidHom.restrict
#check MonoidHom.ker_restrict

example : G →* G ⧸ H := QuotientGroup.mk' H

-- Making an isomorphism out of a bijective group morphism:
noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h

-- Exercise.
noncomputable def iso₁ : K ≃* G ⧸ H := by
  set f := (QuotientGroup.mk' H).restrict K
  refine MulEquiv.ofBijective f ?_
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_restrict]
    simp only [QuotientGroup.ker_mk', Subgroup.subgroupOf_eq_bot]
    exact h
  · exact (aux_card_eq h').symm

-- You can use `MonoidHom.prod`, which makes
-- a morphism `G₀ →* G₁ × G₂` from morphisms
-- `G₀ →* G₁` and `G₀ →* G₂`.
#check MonoidHom.prod

noncomputable def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
  set f := MonoidHom.prod (QuotientGroup.mk' K) (QuotientGroup.mk' H)
  refine MulEquiv.ofBijective f ?_
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_prod]
    simp only [QuotientGroup.ker_mk']
    rw [inf_comm, ← disjoint_iff]
    exact h
  · rw [Nat.card_prod, aux_card_eq h', ← Subgroup.index_mul_card,
      Subgroup.index_eq_card]

-- Last helper function: it makes an isomorphism
-- `G₁ × G₂ ≃* G₁' × G₂'` from isomorphisms `G₁ ≃* G₁'`
-- and `G₂ ≃* G₂'`.
#check MulEquiv.prodCongr

noncomputable def finalIso : G ≃* H × K := by
  refine (iso₂ h h').trans ?_
  apply MulEquiv.prodCongr
  · rw [mul_comm] at h'
    exact (iso₁ h.symm h').symm
  · exact (iso₁ h h').symm
