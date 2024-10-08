import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic

open Classical

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
  map_one := sorry
  map_mul := sorry

#check f ⟨2,3⟩

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
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S
-- then every time we want to apply a lemma about morphisms of monoids to
-- a morphism of rings `f`, we'll have to apply it to `f.toMonoidHom₁` or
-- `f.toAddMonoidHom₁`. :-(
