import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE

section Filter

/- Filters. -/

-- A filter `F` on a type `α` is set in `Set α` (i.e. a set of
-- sets in `α`) such that:
-- (1) The biggest set `⊤` is in `F`;
-- (2) If `x,y : Set α` and `x ⊆ y`, then `x ∈ F` implies that `y ∈ F`;
-- (3) `F` is stable by finite intersections.

-- More precisely, `Filter` is a structure:
#print Filter

variable {α β : Type*}

/-- If `F` is a filter on `α`, and `U` a subset of `α` then we can
write `U ∈ F` as on paper, thanks to the following declaration: -/
instance instMembership : Membership (Set α) (Filter α) :=
  ⟨fun U F => U ∈ F.sets⟩
-- NB: comment this, this is already declare in mathlib.

-- Examples:

-- If `a : α`, the set of sets containing `a` is a filter,
-- and even an ultrafilter (= a maximal filter, cf. later).
example (a : α) : Filter α where
  sets := {A | a ∈ A}
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

-- More generally, if `s : Set α`, the set of sets containing `s`
-- is a filter.
example (s : Set α) : Filter α where
  sets := {A : Set α | s ⊆ A}
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

-- This is called a principal filter, `Filter.principal` in mathlib:
#print Filter.principal

-- The set of sets of natural integers (or real numbers, or
-- rational numbers...) that are "big enough" is a filter.
example : Filter ℕ where
  sets := {A | ∃ n, Set.Ici n ⊆ A}
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

-- This filter is called `Filter.atTop`:
#print Filter.atTop
#print Filter.mem_atTop

-- There is also a filter for "small enough" elements, called
-- `Filter.atBot`.


-- The neighborhoods of a point in `ℝ` (or any metric or more
-- generally topological space):
example (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Set.Ioo (a - ε) (a + ε) ⊆ A}
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

example (a : ℝ) : Filter ℝ where
  sets := {A | ∃ (U : Set ℝ), IsOpen U ∧ a ∈ U ∧ U ⊆ A}
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

-- This filter is called `nhs` or `𝓝` (\ + nhds):
#print nhds

-- If `a : ℝ`, we can also look at the set of subsets of `ℝ`
-- that contain an interval `(a-ε,a]` with `ε > 0`, and this is
-- still a filter.
def nhds_left (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Set.Ioc (a - ε) a ⊆ A}
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry



/- Why filters?-/

/- Filters are (among other things) a very convenient way
to talk about convergence.

For example, consider a function `f : ℝ → ℝ` and `a,b : ℝ`.

Suppose that we want to say that the limit of `f` at `a`
is `b`. This means that, for every `ε > 0`, there exists
`δ > 0` such that `f` sends `(a - δ, a + δ)` to
`(b - ε, b + ε)`.
We can reformulate this by saying that `f ⁻¹' (b - ε, b + ε)`
is in the filter of neighborhoods of `a` for every `ε`, which
means: `∀ (A : nhds b), f ⁻¹' A ∈ nhds a`.

But now suppose to say that `f(x)` tends to `b` as `x` tends to
on the left. This means that for every `ε > 0`, there exists
`δ > 0` such that `f` sends `(a - δ, a]` to `(b - ε, b + ε)`.
With filters, this becomes: `∀ (A : nhds b), f ⁻¹'A ∈ nhds_left a`.

We can similarly express things like "`f(x)` approaches `b`
on the right when `x` approaches `a` on the left", etc.

Now suppose that we want to say `f(x)` tends to `b` as `x`
tends to `+ ∞`. This means that, for every `ε > 0`, there
exists `M : ℝ` such that `f` sends `[M, + ∞)` to
`(b - ε, b + ε)`. Or, with filters:
`∀ (A : nhds b), f ⁻¹' A ∈ Filter.atTop`.
We could similarly express the fact that `f(x)` approaches
`b` from the left as `x` tends to `+ ∞`, by using `nhds_left b`
instead of `nhds`.

Similarly, if `u : ℕ → ℝ` is a sequence (here with real values,
but it could have values in any topological space), we can
express the fact that `u` conveges to `b : ℝ` with filters:
`∀ (A : nhds b), f ⁻¹' b ∈ Filter.atTop`.

Note that all these definitions of convergence can be written
in exactly the same way once we decide to use filters. This is
already nice, but it starts being really powerful when we
want to prove theorems about limits.

For example, let `f,g : ℝ → ℝ` and let `a,b,c : ℝ`. We can
prove that, if `f(x)` tends to `b` as `x` tends to `a`
and `g(y)` tends to `c` as `y` tends to `b`, then `(g ∘ f) (x)`
tends to `c` as `x` tends to `a`.
But then suppose that we want to use that, if `f(x)` tends to
`b` on the right as `x` tends to `a` on the left and `g(y)`
tends to `c` on the left as `y` tends to `b` on the right, then
`(g ∘ f) (x)` tends to `c` on the left as `x` tends to `a` on
the left. On paper, we can just say that "the proof is similar",
but Lean won't accept that, so we would have to rewrite the
proof. Now think about all the different possibilities
(including limits at infinity, limits as `x` is only in a certain
subset etc), and ask yourselves if you really want to write the
resulting 3487 lemmas (conservative estimation).

If instead we can express everything with filters, then
we only need to prove each statement once.
-/

-- First attempt to define convergence: `f : X → Y` is a
-- function, we have a filter `F` on `X`, a filter `G` on
-- `Y`, and we want to say `f` tends to `Y` along `X`.
-- We generalize the definition that appeared before.

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X)
    (G : Filter Y) := ∀ V ∈ G, f ⁻¹' V ∈ F

-- Compatibility with composition.
example {X Y Z : Type*} (f : X → Y) (g : Y → Z) (F : Filter X)
    (G : Filter Y) (H : Filter Z) :
    Tendsto₁ f F G → Tendsto₁ g G H → Tendsto₁ (g ∘ f) F H := by sorry
/-  intro h₁ h₂ V hV
  rw [Set.preimage_comp]
  apply h₁
  exact h₂ V hV -/


/- An intuitive way to think about filters, and a reformulation
of convergence.

Remember that, for every `s : Set α`, we have the principal filter
generated by `s`: it is the filter whose elements are sets
containing `s`.

We think of this filter as standing in for `s`, and we think of
more general filters as "generalized sets" of `α`.

For example, if `α` is `ℝ` (or more generally if `α` has a
topology) and `a : α`, then `𝓝 a` is "the set of elements
close enough to `a`".
If `α` has a (pre)order, then `Filter.atTop` is "the set
of elements that are big enough".
If `α` has a measure `μ`, then we have a filter
`MesureTheory.ae μ` whose elements are co-null sets (i.e.
measurable sets whose complement has measure zero). This
is "the set of almost all elements of `α`".

(If you know what this means, filters on `X` actually
correspond to closed sets of the Stone-Cech compactification
of `X`. If you don't know what this means, it doesn't matter.)
-/

/- Now that we think of filters as generalized sets,
let's extend some set notions to them.

The first is the order relation: sets on `α` are
ordered by inclusion. How does it translate to filters?
Well, it means that every set that contains `t` also
contains `s`:
-/

example (s t : Set α) : s ⊆ t ↔
    (Filter.principal t).sets ⊆ (Filter.principal s).sets := sorry

-- So this is how we define order on filters:
#print Filter.le_def

/- The second notion is the image of a filter by
a function `f : α → β`. This operation is called
`Filter.map`. The idea is that, if `F : Filter α`
and `V : Set β`, the statement
`V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F` should be true
by definition.-/

#print Filter.map

-- This is compatible to the definition for sets.
example {s : Set α} (f : α → β) :
    Filter.map f (Filter.principal s) = Filter.principal (f '' s) := sorry

/- We can now reformulate the notation of convergence
using these notions. The idea is that, for example,
if `f : ℝ → ℝ`, then `f` tends to `b : ℝ` at `a : ℝ`
if, for every `x : ℝ` close enough to `a`, its image
`f(x)` is close enough to `b`. In other words, `f` sends
the "set of elements close enough to `a`" to a "subset"
of "the set of elements close enough to `b`".
-/

def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X)
    (G : Filter Y) := Filter.map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

/- Now to prove the compatibility of limits with compositions,
we use the properties of `Filter.map`.-/
#print Filter.map_mono -- `Filter.map f` is monotone.
#print Filter.map_map -- `Filter.map (g ∘ f) = Filter.map g ∘ Filter.map f`

-- Compatibility with composition.
example {X Y Z : Type*} (f : X → Y) (g : Y → Z) (F : Filter X)
    (G : Filter Y) (H : Filter Z) :
    Tendsto₂ f F G → Tendsto₂ g G H → Tendsto₂ (g ∘ f) F H := by sorry
