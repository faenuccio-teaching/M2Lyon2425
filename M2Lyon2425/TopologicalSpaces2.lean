import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Filter Set Topology Metric

/- Metric spaces: a matric space is a type `X` with a distance
function `dist : X × X → ℝ` that takes nonnegative values, sends
`⟨x,y⟩` if and only `x = y`, is symmetric and satisfies the
triangle inequality.
-/

-- This is how you introduce a metric space.
variable {X : Type*} [MetricSpace X]

section
variable (a b c : X)

-- The distance function is called `dist`.
#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

end

/- One particular case of metric spaces is that
of normed vector spaces (over `ℝ` or `ℂ`, or more
generally over a valued field.)
You will see them more in the calculus section, but here
is how to introduce one:
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
-- The first instance declares the group structure and the
-- norm on `E`, the second instance declares the action of `ℝ`
-- and the compatibility of the norm with it.
#synth Module ℝ E
#synth MetricSpace E -- A normed space is automatically a metric space.

variable {Y : Type*} [MetricSpace Y]

#check dist (α := Y) -- How to pin down the space on which
                     -- we consider the distance function.

variable (a b : Y) in
#check dist a b -- If we give `dist` arguments, Lean will
                -- infer the correct space.


/- You can express limits and continuity in metric spaces
with the usual `ε/δ` statements.
-/
example {f : X → Y} {a : X} {b : Y} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x},
    dist x a < δ → dist (f x) b < ε := Metric.tendsto_nhds_nhds

#check Metric.tendsto_nhds
-- Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ (x : β) in f, dist (u x) a < ε

example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {f : X → Y} : Continuous f ↔
    ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

/- Note that we also have a definition `ContinuousAt`:
`ContinuousAt f x` means `Tendsto f (𝓝 x) (𝓝 (f x))`.
-/
#print ContinuousAt


/- Proofs of continuity.-/

-- Suppose that we want to prove that the distance function is continuous
-- (as a function from `X × X` to `ℝ`).
-- Note that `X × X` gets a `MetricSpace` instance from that on `X`.
#check Prod.metricSpaceMax -- the product distance is the sup distance

example {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := sorry

/- The first solution is to use the `continuity` tactic.
It knows about the continuity of some basic functions,
and that continuity is stable by composition, products,
projections etc.
-/

example {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  continuity

-- Remember that `E` is a normed vector space over `ℝ`.
example : Continuous fun p : ℝ × E ↦ p.1 • p.2 := by
  continuity

example : Continuous fun p : E × E ↦ p.1 - p.2 := by
  continuity

example : Continuous fun p : ℝ × E × E ↦ p.1 • (p.2.1 - p.2.2) := by sorry
--  continuity -- `continuity` has limits...

/- However, `continuity` cannot do everything, and it is
rather slow. So it's good to know the basic lemmas and to
able to do proofs by hand.-/
