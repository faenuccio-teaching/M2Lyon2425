/-
  ## Calculus 1
  Credits.
  * Formalising Mathematics 2022 - 2024, K. Buzzard
  * Mathematics in Lean, J. Avigad, P. Massot
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter

open scoped NNReal ENNReal MeasureTheory BigOperators Topology

namespace MeasureTheory

-- Let Ω be a set equipped with a sigma algebra.
variable {Ω : Type} [MeasurableSpace Ω]

-- Now let's add a measure `μ` on `Ω`
variable {μ : Measure Ω}

/-
Try proving the following:
-/
example (S T : Set Ω) (hS : μ S ≠ ∞) (hT : MeasurableSet T) :
    μ (S ∪ T) = μ S + μ T - μ (S ∩ T) := sorry

/-!
## Measurable functions

So far we've worked in the space `Ω` though with all mathematical objects, we
want to map between them. In measure theory, the correct notion of maps is
measurable functions. If you have seen continuity in topology, they are quite
similar, namely, a function `f` between two measurable spaces is said to be
measurable if the preimages of all measurable sets along `f` is measurable.
-/


/-
*Remark*: while proving the above, you might have noticed I've added the
condition `hS` (think about what is a + ∞ - ∞). In particular, subtraction in
extended non-negative reals (`ℝ≥0∞`) might not be what you expect,
e.g. 1 - 2 = 0 in `ℝ≥0∞`. For this reason, the above lemma is better phrased as
`μ (S ∪ T) + μ (S ∩ T) = μ S + μ T` for which we can omit the condition `hS`.
-/
/-
If you go to the definition of measurable you will find what you expect.
However, of course, measure theory in Lean is a bit more complicated. As we
shall see, in contrast to maths, there are 3 additional notions of measurability
in mathlib. These are:
- `AEMeasurable`
- `StronglyMeasurable`
- `AEStronglyMeasurable`
The reasons for their existence is technical but TLDR: `ae_foo f` is the predicate
that `f` is almost everywhere equal to some function satisfying `foo` (see the
a.e. filter section) while `StronglyMeasurable f` is saying `f` is the limit
of a sequence of simple functions.

Alongside `measurable`, we also see them quite often in the mathlib, although
all you have to know is in most cases (range is metrizable and second-countable),
`Measurable` and `StronglyMeasurable` are equivalent.
-/
example : Measurable (id : Ω → Ω) := sorry

example {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (f : X → Y) (g : Y → Z) (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) := sorry

/-!
## Integration

One of the primary motivations of measure theory is to introduce a more
satisfactory theory of integration. If you recall the definition of the
Darboux-Riemann integral, we cannot integrate the indicator function of
`ℚ ∩ [0, 1]` despite, intuitively, the set of rationals in the unit interval
is much "smaller" (rationals is countable while the irrationals are not.
In contrast, measure theory allows us to construct the Lebesgue integral
which can deal with integrals such as this one.

Lean uses a even more general notion of integration known as Bochner integration
which allows us to integrate Banach-space valued functions. Its construction
is similar to the Lebesgue integral.

Read page 5-6 of https://arxiv.org/pdf/2102.07636.pdf
if you want to know the details.
-/


-- Suppose now `X` is another measurable space
variable {X : Type} [MeasurableSpace X]

-- and suppose it's also a Banach space (i.e. a vector space and a complete metric space)
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

-- If `f : Ω → X` is a function, then the integral of `f` is written as
-- `∫ x, f x ∂μ`. If you want to integrate over the set `s : set Ω` then write
-- `∫ x in s, f x ∂μ`.
-- Try looking in mathlib
example {f g : Ω → X} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := sorry

example (a : X) (s : Set Ω) : ∫ _ in s, a ∂μ = (μ s).toReal • a := sorry

-- Harder
example
    {f : Ω → ℝ} (hf : Measurable f)
    (hint : Integrable f μ) (hμ : 0 < μ {ω | 0 < f ω}) :
    (0 : ℝ) < ∫ ω in {ω | 0 < f ω}, f ω ∂μ := by
  sorry

/-!
## ae filter

Now we have come to a very important section of working with measure theory
in Lean.

In measure theory we have a notion known as almost everywhere (a.e.). In
probability this is known as almost surely however we will stick with
almost everywhere in this project. Namely, a predicate `P` on `Ω` is said to
be true almost everywhere if the set for which `P` holds is co-null, i.e.
`μ {ω : Ω | P ω}ᶜ = 0`.

As examples, we say:
- given functions `f, g`, `f` equals `g` a.e. if `μ {ω : Ω | f ω ≠ g ω} = 0`;
- `f` is less equal to `g` a.e. if `μ {ω : Ω | ¬ f ω ≤ g ω} = 0` etc.

Often, showing that a property holds a.e. is the best we can do in
measure/probability theory.

In Lean, the notion of a.e. is handled by the `Measure.ae` filter.
Let's construct that filter ourselves.
-/


/-
*Remark* It's a common myth that Lebesgue integration is strictly better than
the Darboux-Riemann integral. This is true for integration on bounded intervals
though it is not true when considering improper integrals. A common example
for this is, while `∫ x in [0, ∞), sin x / x dx` is Darboux-Riemann integrable
(in fact it equals `π / 2`) it is not Lebesgue integrable as
`∫ x in [0, ∞), |sin x / x| dx = ∞`.
-/
example (X : Type) [MeasurableSpace X] (μ : Measure X) : Filter X := sorry

-- say `f` and `g` are measurable functions `Ω → X`
variable (f g : Ω → X)

-- The following is a proposition that `f` and `g` are almost everywhere equal
-- it's **not** a proof that `f` and `g` are a.e. equal but simply a statement
example : Prop :=
  ∀ᵐ ω ∂μ, f ω = g ω

-- Here's another example on how to state `f` is almost everywhere less equal
-- than `g`
-- To be able to formulate this we need a notion of inequality on `X` so we
-- will add the `LE` instance on `X`, i.e. equip `X` with a inequality
example [LE X] : Prop :=
  ∀ᵐ ω ∂μ, f ω ≤ g ω

-- Since the above two cases come up quite often, there are special notations
-- for them. See if you can guess what they mean
example : Prop :=
  f =ᵐ[μ] g

example [LE X] : Prop :=
  f ≤ᵐ[μ] g

-- In general, if `P : Ω → Prop` is a predicate on `Ω`, we write `∀ᵐ ω ∂μ, P ω`
-- for the statement that `P` holds a.e.
example (P : Ω → Prop) : Prop :=
  ∀ᵐ ω ∂μ, P ω

-- Sanity check: the above notation actually means what we think
example (P : Ω → Prop) : (∀ᵐ ω ∂μ, P ω) ↔ μ ({ω | P ω}ᶜ) = 0 := by rfl

-- Here's a more convoluted example. See if you can figure what it means
example (f : ℕ → Ω → ℝ) (s : Set Ω) :=
  ∀ᵐ ω ∂μ.restrict s, ∃ l : ℝ, Tendsto (fun n ↦ f n ω) atTop (𝓝 l)

-- Now to do some exercises: you will need to dig into the source code to see
-- what the definitions are and search for helpful lemmas
-- *Hint*: try out the `measurability` tactic. It should be able to solve simple
-- goals of the form `MeasurableSet s` and `Measurable f`
example (s : Set Ω) (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ ω ∈ s, f ω = g ω) : f =ᵐ[μ.restrict s] g := sorry

example (f g h : Ω → ℝ)
    (h₁ : f ≤ᵐ[μ] g) (h₂ : f ≤ᵐ[μ] h) : 2 * f ≤ᵐ[μ] g + h := sorry

example (f g : Ω → ℝ) (h : f =ᵐ[μ] g) (hg : ∀ᵐ ω ∂μ, 2 * g ω + 1 ≤ 0) :
    ∀ᵐ ω ∂μ, f ω ≤ -1 / 2 := sorry

example (f g : ℕ → Ω → ℝ) (a b : ℝ)
    (hf : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 a))
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 b)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω + g n ω) atTop (𝓝 (a + b)) := sorry

/-
I hope that you found the above examples slightly annoying, especially the
third example: why can't we just `rw h`?! Of course, while we often do do so on
paper, rigourously, such a rewrite require some logic. Luckily, what we normally
do on paper is most often ok and we would like to do so in Lean as well. While
we can't directly rewrite almost everywhere equalities, we have the next best
thing: the `filter_upwards` tactic. See the tactic documentation here:
https://leanprover-community.github.io/mathlib_docs/tactics.html#filter_upwards

The `filter_upwards` tactic is much more powerful than simply rewriting a.e.
equalities and is helpful in many situations, e.g. the above second, third
and fourth examples are all easily solvable with this tactic. Let us see how
it works in action.
-/
-- Hover over each line and see how the goal changes
example (f₁ f₂ g₁ g₂ : Ω → ℝ)
    (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ := by
  filter_upwards [h₁, h₂]
  intro ω hω₁ hω₂
  exact add_le_add hω₁ hω₂

-- Here's an even shorter proof using additional parameters of `filter_upwards`
example (f₁ f₂ g₁ g₂ : Ω → ℝ) (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ := by
  filter_upwards [h₁, h₂] with ω hω₁ hω₂ using add_le_add hω₁ hω₂

/-
Intuitively, what `filter_upwards` is doing is simply exploiting the fact that
the intersection of two full measure sets (i.e. complements are null) is also
a set of full measure. Thus, it suffices to work in their intersection instead.

Now, try the above examples again using the `filter_upwards` tactic.
-/
end MeasureTheory

open MeasureTheory intervalIntegral

open Interval
-- this introduces the notation `[[a, b]]` for the segment from `min a b` to `max a b`

example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
  integral_one_div h

example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
        hf.continuousAt).hasDerivAt.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'

noncomputable section

open Set

variable {α : Type*} [MeasurableSpace α]

example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example : Encodable ℕ := by infer_instance

example (n : ℕ) : Encodable (Fin n) := by infer_instance

variable {ι : Type*} [Encodable ι]

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h

open MeasureTheory
variable {μ : Measure α}

example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis

example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x :=
  Iff.rfl

end

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}

example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg

example {s : Set α} (c : E) : ∫ x in s, c ∂μ = (μ s).toReal • c :=
  setIntegral_const c

open Filter

example {F : ℕ → α → E} {f : α → E} (bound : α → ℝ) (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n : ℕ ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim

example {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} [SigmaFinite ν] (f : α × β → E)
    (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  sorry

end
