import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Filter Set Topology Metric

section MetricSpaces

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
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  continuity

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

-- example : Continuous fun p : ℝ × E × E ↦ p.1 • (p.2.1 - p.2.2) := by sorry
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
example : Continuous fun p : ℝ × E × E ↦ p.1 • (p.2.1 - p.2.2) := by   
  change Continuous
    ((λ p ↦ p.1 • p.2) ∘ (λ p : ℝ × E × E ↦ (⟨p.1, p.2.1 - p.2.2⟩ : ℝ × E)))
  apply Continuous.comp
  · apply continuous_smul
  · apply Continuous.prod_mk
    · apply continuous_fst
    · change Continuous ((λ x : E × E ↦ x.1 - x.2) ∘ (λ x : ℝ × E × E ↦ x.2))
      apply Continuous.comp
      · apply continuous_sub
      · apply continuous_snd

-- Try to solve the exercises using only the lemmas above.
-- Then try again using these more powerful lemmas:
#check Continuous.dist
#check Continuous.fst
#check Continuous.snd
#check Continuous.prod_map

example {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist <;> apply Continuous.comp
  · assumption
  · apply continuous_fst
  · assumption
  · apply continuous_snd

-- Remember that `E` is a normed vector space over `ℝ`.
-- example : Continuous fun p : ℝ × E × E ↦ p.1 • (p.2.1 - p.2.2) := by
--   change Continuous
--     ((λ p ↦ p.1 • p.2) ∘ (λ p : ℝ × E × E ↦ (⟨p.1, p.2.1 - p.2.2⟩ : ℝ × E)))
--   apply Continuous.comp
--   · apply continuous_smul
--   · for some reason, Continuous.prod_map cannot be applied

-- One more exercise...
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
  apply Continuous.comp; assumption; apply Continuous.add
  apply continuous_pow; apply continuous_id

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
    (hu : Tendsto f (𝓝 b) (𝓝 a)) (hus : ∀ y, f y ∈ s) : a ∈ s := by
  apply hs.mem_of_tendsto hu
  apply Eventually.of_forall
  exact hus

example {s : Set X} : a ∈ closure s ↔
    ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X}
    (hs : ∀ n, u n ∈ s) : a ∈ closure s := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  rw [Metric.tendsto_atTop] at hu
  cases (hu ε hε) with
  | intro N hu => use (u N); constructor
                  · apply hs
                  · rw [dist_comm]; apply hu; trivial

-- (Don't use `mem_closure_iff_seq_limit`, it would make it too easy.)

/- "Remember" that a topological space `X` is called compact if
any covering of `X` by open subsets has a finite subcovering,
i.e. if `X = ⋃ i in I, Uᵢ` with the `Uᵢ` open, there these
exists a finite set `J` in `I` such that `X = ⋃ i in J, Uᵢ`.

Note that some authors (not mathlib) also require X to be
Hausdorff (aka T₂): for any `a,b` in `X` such that `a ≠ b,
there exist a neighborhood `U` of `a` and a neighborhood `V` of `b`
such that `U ∩ V = ∅`.
(This condition is automatic if `X` is a metric space.)
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

/- Metric notions: uniform continuity and Cauchy
sequences.

The notions we saw so far are purely topological,
that is, they can be expressed using only the notion
of open sets. Now we will discuss some notions that
require more: a way to express that "the points `x` and
`y` are as close to each other as the points `a` and `b`".
We can do this in a metric space using the distance, and
also in something like a topological vector space (using
the translations to compare degrees of closeness). The
most general structure where this makes sense is a
uniform space; we won't discuss them today, but you will
run into them in mathlib and in the names of lemmas (like
`UniformSpace.isCompact_iff_isSeqCompact` above).

All the notions that we discuss now make sense in a
general uniform space.
-/

/- We start with uniformly continuous functions.-/

example {f : X → Y} : UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff

#print UniformContinuous -- uh oh

/- Exercise: every continuous function from a compact metric
space `X` to a metric space `Y` is uniformly continuous.-/

example [CompactSpace X] {f : X → Y} (hf : Continuous f) :
    UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  let K := { p : X × X | ε ≤ dist (f p.1) (f p.2) }
  have hcK : IsClosed K := by  
    apply isClosed_le; apply continuous_const
    apply Continuous.dist <;> apply Continuous.comp
    assumption; apply continuous_fst; assumption; apply continuous_snd
  have hcomp : IsCompact K := IsClosed.isCompact hcK
  by_cases e : (K = ∅)
  · use 1; constructor; linarith; intro a b h; rw [eq_empty_iff_forall_not_mem] at e
    aesop
  · have h : ∃ x ∈ K, IsMinOn (λ x ↦ dist x.1 x.2) K x := by
         apply IsCompact.exists_isMinOn; assumption; rw[← not_nonempty_iff_eq_empty] at e
         push_neg at e; assumption; rw [continuousOn_iff_continuous_restrict]
         unfold restrict; simp; apply Continuous.dist; apply Continuous.comp
         apply continuous_fst; apply continuous_subtype_val
         apply Continuous.comp; apply continuous_snd; apply continuous_subtype_val
    cases h with
    | intro x h => use (dist x.1 x.2); constructor
                   · aesop; linarith
                   · intro a b h'; unfold IsMinOn at h; unfold IsMinFilter at h
                     rw [eventually_principal] at h; simp at h
                     have hnin : (a, b) ∉ K := by 
                       intro hin; cases h with
                       | intro left right => specialize right a b hin
                                             rw [lt_iff_not_le] at h'; apply h'; assumption
                     aesop

/-
Sketch of proof: we need to check that
`∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε`.

So we fix `ε > 0` and let `K := { p : X × X | ε ≤ dist (f p.1) (f p.2)}`.

(1) We prove that `K` is compact. Indeed, it suffices to prove
that `K` is closed. For this, use `isClosed_le` and the fact that
`K` is of the form `{p : X × X | ε ≤ φ p}` where `φ` is a continuous
function (hint: we already met the function `φ` today).

(2) By `eq_empty_or_nonempty`, we know that `K` is either empty or
nonempty. If `K` is empty, we are done; take `δ = 1` for example.

(3) Assume that `K` is nonempty. As it is compact, and as `dist`
is a continuous function, the minimum of `dist` on `K` is attained
(`IsCompact.exists_isMinOn`), say at `⟨x₀, x₁⟩`. Then we can
take `δ = dist x₀ x₁`.
-/

/- We now discuss Cauchy sequences. There are two equivalent
ways to define them in metric spaces.-/

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
    dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

-- Again, let's have a look at the general definition:
#print CauchySeq -- of course it uses filters...
#print Cauchy

/- A metric space is called complete if every Cauchy
sequence converges.-/

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

/- A criterion for a sequence to be Cauchy:-/
open Finset in
theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by 
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by 
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n > 2/ε := by exact exists_nat_gt (2 / ε)
    use n
    have hε : (2 : ℝ) / (n : ℝ) < ε := by sorry -- easy to see but I don't know the right lemmas to show it and it takes too much time to search for it.
    have ho : 1 / 2 ^ n * 2 ≤ (2 : ℝ) / (n : ℝ) := by sorry -- same
    apply lt_of_le_of_lt ho hε
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by rw [Nat.add_zero, dist_comm]
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := by
        induction' k with k ih
        · rw [dist_self]; simp
        · rw [sum_range_add]; simp
          trans (dist (u N) (u (N + k)) + dist (u (N + k)) (u (N + (k + 1))))
          · apply dist_triangle
          · apply add_le_add_right; apply ih; linarith
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := by apply sum_le_sum; intro i hi; apply hu
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by 
        rw [mul_sum, sum_eq_sum_iff_of_le]; intro i hi; simp; rw [npow_add, mul_inv]
        intro i hi; simp; rw [npow_add, mul_inv]
    _ ≤ 1 / 2 ^ N * 2 := by 
        apply mul_le_mul 
        · linarith
        · exact sum_geometric_two_le k
        · apply sum_nonneg; intro i hi; have : i ≥ 0 := by omega
          simp
        · simp
    _ < ε := hN
-- Note that `range` stands for `Finset.range`:
#check Finset.range -- `Finset.range n` of natural numbers `< n`.

-- Helper lemmas:
#check tendsto_pow_atTop_nhds_zero_of_lt_one
-- if `r < 1`, then the geometric sequence `(r^n)` tends to `0`
#check Tendsto.mul -- limit of a product of functions
#check dist_le_range_sum_dist --generalized triangle inequality

/- Let's prove Baire's theorem! ("In a complete metric, a
countable intersection of open dense subsets is dense.")-/

-- Note the use of `Nat.recOn` to construct a function
-- using recursion in the middle of a proof.
#check Nat.recOn
/-
  Nat.recOn.{u} {motive : ℕ → Sort u} (t : ℕ)
  (zero : motive Nat.zero)
  (succ : (n : ℕ) → motive n → motive n.succ) :
  motive t
  -/

open Metric

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n := by intro n; aesop
  /- Translate the density assumption into two functions `center` and
     `radius` associating to any `n, x, δ, δpos` a center and a positive
     radius such that `closedBall center radius` is included both in
     `f n` and in `closedBall x δ`.
     We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a
     Cauchy sequence later. -/
  have : ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧
      closedBall y r ⊆ closedBall x δ ∩ f n := by 
        intro n x δ hδ; specialize (hd n); specialize (ho n)
        have hox : IsOpen (ball x δ) := by exact isOpen_ball
        rw [dense_iff] at hd; rw [isOpen_iff] at ho; rw [isOpen_iff] at hox
        specialize (hd x δ hδ); rw [inter_nonempty_iff_exists_right] at hd
        cases hd with
        | intro y h => specialize (ho y h.left); cases ho with
          | intro r h' => specialize (hox y h.right); cases hox with
            | intro r' h'' => use y; let ε := (min (B (n + 1)) ((min r r')/2)); use ε
                              constructor
                              · unfold_let; simp; constructor; exact h'.left; exact h''.left
                              · constructor
                                · unfold_let; simp
                                · have hincx : closedBall y ε ⊆ closedBall x δ := by 
                                       trans (ball y r'); apply closedBall_subset_ball
                                       unfold_let; simp; right
                                       by_cases h : r ≤ r'
                                       · aesop; apply lt_of_le_of_lt (b := r' / 2); linarith
                                         exact div_two_lt_of_pos left_2
                                       · have e : (min r r' = r') := by rw [min_eq_right_iff]
                                                                        linarith
                                         rw [e]; exact div_two_lt_of_pos h''.left
                                  have hincf : closedBall y ε ⊆ f n := by
                                        trans (ball y r); apply closedBall_subset_ball
                                        unfold_let; simp; right
                                        by_cases h : r ≤ r'
                                        · have e : (min r r' = r) := by rw [min_eq_left_iff]
                                                                        linarith
                                          rw [e]; exact div_two_lt_of_pos h'.left
                                        · have e : (min r r' = r') := by rw [min_eq_right_iff]
                                                                         linarith
                                          rw [e]; apply lt_of_lt_of_le (b := r / 2);
                                          linarith; apply half_le_self; linarith [h'.left]
                                  rw [subset_inter_iff]; constructor <;> assumption
  choose! center radius Hpos HB Hball using this
  /- The tactic `choose` creates a function from statements of the
     form `∀ x, ∃ y, P x y`. More precisely, `choose a b h h' using hyp`
     takes a hypothesis `hyp` of the form
     `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
xm     for some `P Q : X → Y → A → B → Prop` and outputs into
     context functions  `a : X → Y → A`, `b : X → Y → B`
     and two assumptions:
     `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
     `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`.
    The tactic `choose!` does the same, except that it tries to
    make the functions not depend on the propositional arguments.

    Check out what happens if we use `choose` instead in the line
    above.
  -/
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` is positive. We have to find a point in the ball of
      radius `ε` around `x` belonging to all `f n`. For this,
      we construct inductively a sequence `F n = (c n, r n)` such
      that the closed ball `closedBall (c n) (r n)` is included
      in the previous ball and in `f n`, and such that `r n` is
      small enough to ensure that `c n` is a Cauchy sequence.
      Then `c n` converges to a limit which belongs to all
      the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n; induction' n with n ih
    · unfold_let r; unfold_let F; simp; constructor; assumption; apply Bpos
    · unfold_let r; unfold_let F; simp; apply Hpos; assumption
  have rB : ∀ n, r n ≤ B n := by
    intro n; induction' n with n ih
    · unfold_let r; unfold_let F; simp
    · unfold_let r; unfold_let F; simp; apply HB; apply rpos
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆
      closedBall (c n) (r n) ∩ f n := by
    intro n; apply Hball; apply rpos
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by
    intro n; specialize incl n
    have h : c (n + 1) ∈ closedBall (c n) (r n) := by 
      rw [subset_inter_iff] at incl; apply incl.left; rw [mem_closedBall, dist_self]
      apply le_of_lt; exact (rpos (n + 1))
    unfold closedBall at h; rw [mem_setOf] at h; trans (r n); rw [dist_comm]; assumption
    apply rB
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space,
  -- it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check
  -- that it belongs to all `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆
      closedBall (c n) (r n) := by 
    intro n m h; induction' h with k hk ih
    · intro x; tauto
    · trans (closedBall (c k) (r k)); specialize (incl k); rw [subset_inter_iff] at incl
      apply incl.left; assumption
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by 
    intro n
    have hc : ∀ n m, m ≥ n → c m ∈ closedBall (c n) (r n) := by
      intro n m hmn; apply I; assumption; unfold closedBall; rw [mem_setOf, dist_self]
      apply le_of_lt; apply rpos
    have hclosed : IsClosed (closedBall (c n) (r n)) := by exact isClosed_ball
    apply IsClosed.mem_of_tendsto hclosed ylim; rw [eventually_atTop]; use n; intro m hm
    apply hc; assumption
  constructor
  · rw [mem_iInter]; intro n; have h : y ∈ closedBall (c (n + 1)) (r (n + 1)) := yball (n + 1)
    specialize incl n; rw[subset_inter_iff] at incl; apply incl.right; assumption
  · specialize Hball 0 x (min ε (B 0)); rw [subset_inter_iff] at Hball
    have h : min ε (B 0) > 0 := by apply lt_min; assumption; apply Bpos
    specialize Hball h; have h' : closedBall x (min ε (B 0)) ⊆ closedBall x ε := by
      intro z; unfold closedBall; rw [mem_setOf, mem_setOf]; intro hz; trans (min ε (B 0))
      assumption; rw [min_le_iff]; left; linarith
    apply h'; apply (yball 0)

end MetricSpaces

section TopologicalSpaces

variable {X : Type*} [TopologicalSpace X]

/- Topological spaces: this is what you get when you
take a metric space and forget everything except the
notion of open subsets.

There are two ways to think of topological spaces:
(1) As a type equipped with a family of open sets,
such that:
- `⊥` and `⊤` are open;
- an arbitrary union of open sets is open;
- the intersection of two open sets is open.

(2) As a type `X` equipped, for every `x : X`, with
a neighborhood filter `𝓝 x`, such that:
- for every `x`, the principal filter generated by `{x}`
is `≤ 𝓝 x`;
- if `P : X → Prop` and `x : X`, if `P y` holds for `y`
close to `x`, then, for `y` close to `x` and `z` close
to `y`, `P x` also holds. In symbols:
-/
example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) :
    ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
  eventually_eventually_nhds.mpr h

/- In practice, we use whichever point of view is most
convenient for our particular goal.-/

/- So why topological spaces? One reason is that a lot
of definitions and results (about continuity, convergence etc)
are true in that setting, and we like to write in the most
general setting possible. But another reason is that
topological spaces are more flexible than metric spaces.

For example, we can put a distance on a product of two
metric spaces, and even on a countable product (in a less
canonical way), but there is no reasonable way to do so
on an arbitrary product. There is also no canonical way
to put a distance on the quotient of a metric space by
an equivalence relation.

For topological spaces, all these and more are available.
-/

/- The first basic notion is the order on `TopologicalSpace`
structures on a type `A`.

The idea is this: if `t₁` and `t₂` are two topological space
structures on `A`, we say that `t₁` is finer than `t₂`, and
write `t₁ ≤ t₂`, if the identity map from `A` equipped with `t₁`
to `A` equipped with `t₂` is continuous. This means that every
set that is open for `t₂` is also open for `t₁`.
-/

variable {A : Type*}

example {t₁ t₂ : TopologicalSpace A} :
    t₁ ≤ t₂ ↔ ∀ s, IsOpen[t₂] s → IsOpen[t₁] s := Iff.rfl

/- Note that, for every `a : A`, the function
`fun (t : TopologicalSpace A) ↦ @nhds A t a` sending
a topological space structure to its filters of neighborhoods
of `a` is order-preserving.
-/

example {a : A} :
    Monotone (fun (t : TopologicalSpace A) ↦ @nhds A t a) := by
  intro t₁ t₂ h; rw [le_nhds_iff]; intro s hin hop
  rw [@_root_.mem_nhds_iff]; use s; constructor; tauto; constructor
  rw [TopologicalSpace.le_def] at h; apply h; assumption; assumption

#check TopologicalSpace.le_def
#check le_nhds_iff
#check mem_nhds_iff
#check IsOpen.mem_nhds

/- Next we have that `TopologicalSpace A` is a complete lattice,
which means that an arbitrary family of topological space
structures on `A` has both an `inf` and a `sup`. (The construction
is somewhat similar to that of the `inf` and `sup` for filters.)

In particular, there is a smallest (= fines) topological
space structure on `A`, called the discrete topology;
there is also a biggest (= coarsest) topological space structure,
sometimes called the discrete topology.
-/
#check TopologicalSpace.isOpen_top_iff
#check DiscreteTopology


/- The next important construction is that of the
induced and coinduced topology.-/

variable {B : Type*}

-- Coinduction:
example (f : A → B) : TopologicalSpace A → TopologicalSpace B :=
  TopologicalSpace.coinduced f

#print TopologicalSpace.coinduced
-- If `t` is a topology on `A` and `f : A → B`, then
-- `t.coinduced f` is the coarsest topology on `B` that
-- makes `f` continuous. So a set of `B` is open if and
-- only its preimage by `f` is an open set of `A`.

-- For example, this gives the quotient topology.

-- Induction:
example (f : A → B) : TopologicalSpace B → TopologicalSpace A :=
  TopologicalSpace.induced f

#print TopologicalSpace.induced
-- If `t` is a topology on `B` and `f : A → B`, then
-- `t.induced f` is the coarsest topology on `A` that
-- makes `f` continuous. So a set of `A` is open if and
-- only if it is the preimage by `f` of an open set of `B`.

-- This gives the induced topology on a subtype, for example.

-- These two operations form a Galois connection:
example (f : A → B) (T_A : TopologicalSpace A) (T_B : TopologicalSpace B) :
    TopologicalSpace.coinduced f T_A ≤ T_B ↔
    T_A ≤ TopologicalSpace.induced f T_B :=
  coinduced_le_iff_le_induced

/- Induction and coinduction are compatible with the composition
of maps (but induction reverses order):-/
#check induced_compose
#check coinduced_compose

/- They are also monotone:-/
#check induced_mono
#check coinduced_mono

-- Exercise: expressing continuity using order and coinduction
-- (we could also use induction (how?)):
example (T_A : TopologicalSpace A) (T_B : TopologicalSpace B)
    (f : A → B) :
    Continuous f ↔ TopologicalSpace.coinduced f T_A ≤ T_B := by
  constructor
  · intro hf; apply hf.isOpen_preimage
  · intro h; exact { isOpen_preimage := h }

#check Continuous.isOpen_preimage -- the definition of continuity

#check continuous_iff_coinduced_le -- this is the answer, don't use it!


/- Now we will see how to define product topologies using
these notions. Even if you didn't study general topology,
you might have met some product topologies: for example,
we can see the space of functions `[0,1] → ℝ` as the product
of copies of `ℝ` indexed by elements of `[0,1]`. The product
topology on this is also called "the topology of pointwise
convergence" ("convergence simple" in French).
-/

/- Coming back to the general case, we fix a type `ι` and
a function `A : ι → Type*`. Suppose that we have
`T i : TopologicalSpace (A i)` for every `i : ι`.

We want the topology on `Π i, A i` to make all the
projection maps `fun x ↦ xi` continuous, i.e. to be
`≤ TopologicalSpace.induced (fun x ↦ x i)`.

In fact, we want  a function `f : B → Π i, A i` to be
continuous if and  only if all the
`(fun x ↦ x i) ∘ f : B → A i` are continuous.
This means that the product topology on `Π i, A i` is
the coarsest that makes all the projections continuous,
i.e. the sup of all the
`TopologicalSpace.induced (fun x ↦ x i)`.
-/

example (ι : Type*) (A : ι → Type*) (T : ∀ i, TopologicalSpace (A i)) :
    (Pi.topologicalSpace : TopologicalSpace (∀ i, A i)) =
      ⨅ i, TopologicalSpace.induced (fun x ↦ x i) (T i) :=
  rfl

/- Compactness: the definition of a compact space only uses
open sets, so it makes sense for a tgeneral topological space.

We can, of course, reformulate it using filters. We need the
notion of cluster point of a filter: `x` is a cluster point of
`F` is the generalized sets `F` and `𝓝 x` have a nontrivial
intersection.
-/

example {F : Filter X} {x : X} : ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) :=
  Iff.rfl

/- For example, if we have a sequence `u : ℕ → X` and `F` is the
filter `map u atTop` (i.e. the filter with basis the sets `u '' [n, + ∞)`,
for n` in `ℕ`), then 'x' is a cluster point of `F` if and only, for every
neighborhood `U` of `x` and every `n` in `ℕ`, there exists `m ≥ n` such
that `u m ∈ U`.
If `𝓝 x` has a countable basis, we can use this property to construct
a subsequence of `u` converging to `x` (but this is not possible in general):
-/
example [FirstCountableTopology X] {u : ℕ → X} {x : X} (h : ClusterPt x (map u atTop)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  TopologicalSpace.FirstCountableTopology.tendsto_subseq h

/- Compactness of `s` then is equivalent to saying that every "contained in `s`"
has a cluster point on `s`.-/
example {s : Set X} :
    IsCompact s ↔ ∀ (F : Filter X) [NeBot F], F ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a F :=
  Iff.rfl

/- If every neighborhood filter of `X` has a countable basis (= if `X` is first
countable), then we recover the property that every sequence in a compact set of
`X` has a converging subsequence.-/
example [FirstCountableTopology X] {s : Set X} {u : ℕ → X} (hs : IsCompact s)
    (hu : ∀ n, u n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ,
    StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu
-- Note that this property is false in general, for example for the
-- product space `[0,1] → [0,1]` (which is compact by Tychonoff's theorem).


/- We have that the `FirstCountable` property is a property that we can impose
on a topological space to make it behave more like a metric space.
-/
-- Metric spaces are first countable:
example [MetricSpace A] : FirstCountableTopology A := UniformSpace.firstCountableTopology A

/- Other such properties are the separation properties, for example:-/
#print T2Space -- If `x` and `y` are distinct points, there exist disjoint
-- open sets `U` and `V` such that `x ∈ U` and `y ∈ V`.
#print T3Space -- every point has a basis of closed neighborhoods


end TopologicalSpaces
