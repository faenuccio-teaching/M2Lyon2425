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

#check f ⟨2,3⟩ -- we can't apply a `MonoidHom₁` to an element, which is annoying

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

attribute [coe] (MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁) -- does not work :-(

example {R S : Type*} [Ring R] [Ring S] (f : RingHom₁ R S) (a : R) (n : ℕ) :
    f (a ^ n) = (f a) ^ n := by
  erw [MonoidHom₁.map_pow] -- does not work
  -- (okay, so it would here if we do `simp` first, but this is very simple situation)

end RingHomCoe_first_try

/- Do we want to coerce all the ring morphisms into monoid morphisms every time we need to apply
a lemma about monoid morphism? (But what if we want to apply a lemma about ring morphisms next?)
Or do we want to rewrite all the lemmas about monoid morphisms so that they apply to ring morphisms?
The answer is "neither".

What we do instead is define a class for "things that look like a set of monoid morphisms".
-/

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

-- So why not define a `CoeFun` instance on `MonoidHomClass₁`?
--set_option synthInstance.checkSynthOrder false in
instance badInst {F M N : Type*} [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] :
    CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun
-- oops, strange error :-((((

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
