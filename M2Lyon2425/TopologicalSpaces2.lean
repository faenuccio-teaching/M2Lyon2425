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
able to do proofs by hand.
-/
-- First some lemmas about continuity of particular functions:
#check continuous_dist -- `dist` is continuous as a function `X × X → ℝ`
#check continuous_smul -- `smul` is continuous as a function `ℝ × E → E`
#check continuous_add -- continuity of addition on `E`
#check continuous_sub -- continuity of subtraction on `E`
#check continuous_fst -- the first projection `X × Y → X` is continuous
#check continuous_snd -- the second projection `X × Y → Y` is continuous

-- Then some lemmas about the permanence properties of continuity:
#check Continuous.comp -- a composition of continuous functions is continuous
#check Continuous.prod_mk -- a product of continuous functions is continuous

example {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
--  apply Continuous.comp -- this does not work :-(
  change Continuous
    ((fun q ↦ dist q.1 q.2) ∘ (fun (p : X × X) ↦ (⟨f p.1, f p.2⟩ : Y × Y)))
  apply Continuous.comp
  · exact continuous_dist
  · apply Continuous.prod_mk
    · apply Continuous.comp
      · exact hf
      · exact continuous_fst
    · apply Continuous.comp
      · exact hf
      · exact continuous_snd

-- If we shorten the proof, we get this:
example {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))
-- This works, but we had to guess the whole proof term.

-- Remember that `E` is a normed vector space over `ℝ`.
example : Continuous fun p : ℝ × E × E ↦ p.1 • (p.2.1 - p.2.2) := by sorry

-- Try to solve the exercises using only the lemmas above.
-- Then try again using these more powerful lemmas:
#check Continuous.dist
#check Continuous.fst
#check Continuous.snd
#check Continuous.prod_map

example {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by sorry

-- Remember that `E` is a normed vector space over `ℝ`.
example : Continuous fun p : ℝ × E × E ↦ p.1 • (p.2.1 - p.2.2) := by sorry

-- One more exercise...
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  sorry

-- Useful lemmas:
#check Continuous.add
#check continuous_pow
#check continuous_id


/- In mathlib, all the usual topological notions like comtinuity,
open sets etc are defined in the general setting of topological
spaces. Let's see a few lemmas to translate them into statements
using either the distance, or open/closed balls in metric spaces.
-/

-- First, we need balls.
variable (r : ℝ) (a : X)

example : Metric.ball a r = { b | dist b a < r } := rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } := rfl

-- Is the center of the a always in the ball?
example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr

-- Open and closed balls (with positive radius) form a
-- basis of the neighborhood filter of `a`.
#check Metric.nhds_basis_ball
#check Metric.nhds_basis_closedBall

-- We can deduce necessary and sufficient conditions
-- for a set to be a neighborhod of `a`:
example {a : X} {s : Set X} :
    s ∈ 𝓝 a ↔ ∃ ε > 0, Metric.ball a ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {a : X} {s : Set X} :
    s ∈ 𝓝 a ↔ ∃ ε > 0, Metric.closedBall a ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff

#check Filter.HasBasis.mem_iff

-- Continuity at a point:
example (f : X → Y) :
    ContinuousAt f a ↔
    ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

-- Open sets:
example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

-- A set is closed if its complement is open:
example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

-- If a set `s` is closed, then it contains the limit
-- of any sequence of elements of `s`. (This is an if
-- and only if, and mathlib knows it, cf. for example
-- `mem_closure_iff_seq_limit`).
example {s : Set X} (hs : IsClosed s) {u : ℕ → X}
    (hu : Tendsto u atTop (𝓝 a)) (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (Eventually.of_forall hus)

 --Lemma used in the previous proof:
 #check IsClosed.mem_of_tendsto

-- Now try to prove this:
example {s : Set X} (hs : IsClosed s) {f : Y → X} {b : Y}
    (hu : Tendsto f (𝓝 b) (𝓝 a)) (hus : ∀ y, f y ∈ s) : a ∈ s :=
  sorry

example {s : Set X} : a ∈ closure s ↔
    ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X}
    (hs : ∀ n, u n ∈ s) : a ∈ closure s :=
  sorry
-- (Don't use `mem_closure_iff_seq_limit`, it would make it too easy.)

/- "Remember" that a topological space `X` is called compact if:

(1) X is Hausdorff (aka T₂): for any `a,b` in `X` such that `a ≠ b,
there exist a neighborhood `U` of `a` and a neighborhood `V` of `b`
such that `U ∩ V = ∅`.

(2) Any covering of `X` by open subsets has a finite subcovering,
i.e. if `X = ⋃ i in I, Uᵢ` with the `Uᵢ` open, there these
exists a finite set `J` in `I` such that `X = ⋃ i in J, Uᵢ`.

The first condition is automatic if `X` is a metric space.
-/

-- Every sequence with values in a compact set
-- has a convergence subsequence.
example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

/- A set having the property that every sequence
with values in it has a convergent subsequence is
called "sequentially compact". For metric spaces,
the Bolzano-Weierstrass theorem says that
"sequentially compact" and "compact" are equivalent
properties:
-/
example {s : Set X} : IsCompact s ↔ IsSeqCompact s :=
  UniformSpace.isCompact_iff_isSeqCompact

/- How to construct compact spaces in practice?-/

-- Closed intervals in `ℝ` are compact:
example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

-- More generally, in a finite-dimensional normed vector
-- space, any closed bounded set is compact:
example [FiniteDimensional ℝ E] {s : Set E}
    (hc : IsClosed s) (hb : Bornology.IsBounded s) : IsCompact s :=
  Metric.isCompact_of_isClosed_isBounded hc hb

-- If `s` is compact, so is any closed subset of `s`:
example {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) :
    IsCompact t := IsCompact.of_isClosed_subset hs ht h

-- Some properties of compact sets:
-- They are closed in `X`:
example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

-- Every continuous function on a compact set has a minimum:
example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs

-- and a maximum:
example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_isMaxOn hs' hfs

-- How to say that the metric space `X` itself is compact:
-- we use a type class called `CompactSpace`:
example [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ
