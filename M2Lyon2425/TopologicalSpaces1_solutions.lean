import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Filter Set Topology

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
--instance instMembership : Membership (Set α) (Filter α) :=
--  ⟨fun U F => U ∈ F.sets⟩
-- NB: comment this, this is already declare in mathlib.

-- Examples:

-- If `a : α`, the set of sets containing `a` is a filter,
-- (and even an ultrafilter).
example (a : α) : Filter α where
  sets := {A | a ∈ A}
  univ_sets := mem_univ a
  sets_of_superset h h' := h' h
  inter_sets h h' := mem_inter h h'

-- More generally, if `s : Set α`, the set of sets containing `s`
-- is a filter.
example (s : Set α) : Filter α where
  sets := {A : Set α | s ⊆ A}
  univ_sets := subset_univ s
  sets_of_superset h h' := subset_trans h h'
  inter_sets h h' := subset_inter h h'

-- This is called a principal filter, `Filter.principal` in mathlib:
#print Filter.principal

-- The set of sets of natural integers (or real numbers, or
-- rational numbers...) that are "big enough" is a filter.
example : Filter ℕ where
  sets := {A | ∃ n, Set.Ici n ⊆ A}
  univ_sets := by
    use 0, subset_univ _
  sets_of_superset h h' := by
    obtain ⟨n, hn⟩ := h
    use n, fun _ hx ↦ (subset_trans hn h') hx
  inter_sets h h' := by
    obtain ⟨n, hn⟩ := h
    obtain ⟨m, hm⟩ := h'
    use max n m
    erw [← Ici_inter_Ici]
    exact fun _ hx ↦ (inter_subset_inter hn hm) hx

-- Set.Ici a = [a, + ∞)
-- Set.Ioo a b a b = (a, b)
-- Set.Ixx where x is o, c or i; o = open, c = closed, i = infinite
-- Set.Iio a = (- ∞, a)

-- This filter is called `Filter.atTop`:
#print Filter.atTop
#check atTop
#print Filter.mem_atTop

-- There is also a filter for "small enough" elements, called
-- `Filter.atBot`.


-- The neighborhoods of a point in `ℝ` (or any metric or more
-- generally topological space):
example (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Set.Ioo (a - ε) (a + ε) ⊆ A}
  univ_sets := by
    use 1, zero_lt_one, subset_univ _
  sets_of_superset h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    use ε, hpos, subset_trans h h'
  inter_sets h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    obtain ⟨ε', hpos', h'⟩ := h'
    use min ε ε', lt_min_iff.mpr ⟨hpos, hpos'⟩
    intro z hz
    apply (inter_subset_inter h h')
    rw [Ioo_inter_Ioo]
    change z ∈ Ioo (max (a - ε) (a - ε')) (min (a + ε) (a + ε'))
    rw [max_sub_sub_left a ε ε', min_add_add_left a ε ε']
    exact hz

example (a : ℝ) : Filter ℝ where
  sets := {A | ∃ (U : Set ℝ), IsOpen U ∧ a ∈ U ∧ U ⊆ A}
  univ_sets := by
    use univ, isOpen_univ, mem_univ a, subset_refl _
  sets_of_superset h h' := by
    obtain ⟨U, hopen, ha, hsub⟩ := h
    use U, hopen, ha, subset_trans hsub h'
  inter_sets h h' := by
    obtain ⟨U, hopen, ha, hsub⟩ := h
    obtain ⟨U', hopen', ha', hsub'⟩ := h'
    use U ⊓ U', IsOpen.inter hopen hopen', mem_inter ha ha', inter_subset_inter hsub hsub'

-- This filter is called `nhs` or `𝓝` (\ + nhds):
#print nhds

-- If `a : ℝ`, we can also look at the set of subsets of `ℝ`
-- that contain an interval `(a-ε,a]` with `ε > 0`, and this is
-- still a filter.
def nhds_left (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Ioc (a - ε) a ⊆ A}
  univ_sets := by
    use 1, zero_lt_one, subset_univ _
  sets_of_superset h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    use ε, hpos, subset_trans h h'
  inter_sets h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    obtain ⟨ε', hpos', h'⟩ := h'
    use min ε ε', lt_min_iff.mpr ⟨hpos, hpos'⟩
    intro z hz
    apply (inter_subset_inter h h')
    rw [Ioc_inter_Ioc]
    change z ∈ Ioc (max (a - ε) (a - ε')) (min a a)
    rw [max_sub_sub_left a ε ε', min_self]
    exact hz

/- If `α` has a measure `μ`, then we have a filter
`MesureTheory.ae μ` whose elements are co-null sets (i.e.
measurable sets whose complement has measure zero). This
is "the set of almost all elements of `α`".
-/
#print MeasureTheory.ae -- ae = almost everywhere

open MeasureTheory in
#check ae (volume : Measure ℝ)


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
means: `∀ (U : nhds b), f ⁻¹' U ∈ nhds a`.

But now suppose to say that `f(x)` tends to `b` as `x` tends to
`a` on the left. This means that for every `ε > 0`, there exists
`δ > 0` such that `f` sends `(a - δ, a]` to `(b - ε, b + ε)`.
With filters, this becomes: `∀ (U : nhds b), f ⁻¹'U ∈ nhds_left a`.

We can similarly express things like "`f(x)` approaches `b`
on the right when `x` approaches `a` on the left", etc.

Now suppose that we want to say `f(x)` tends to `b` as `x`
tends to `+ ∞`. This means that, for every `ε > 0`, there
exists `M : ℝ` such that `f` sends `[M, + ∞)` to
`(b - ε, b + ε)`. Or, with filters:
`∀ (U : nhds b), f ⁻¹' U ∈ Filter.atTop`.
We could similarly express the fact that `f(x)` approaches
`b` from the left as `x` tends to `+ ∞`, by using `nhds_left b`
instead of `nhds`.
`∀ (U : nhds_left b), f ⁻¹' U ∈ Filter.atTop`.


Similarly, if `u : ℕ → ℝ` is a sequence (here with real values,
but it could have values in any topological space), we can
express the fact that `u` converges to `b : ℝ` with filters:
`∀ (U : nhds b), f ⁻¹' U ∈ Filter.atTop`. --i.e. f ⁻¹' U contains
-- an interval [n, +∞).

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
    Tendsto₁ f F G → Tendsto₁ g G H → Tendsto₁ (g ∘ f) F H := by
  intro h h' U hU
  rw [preimage_comp]
  apply h
  apply h'
  exact hU

#check Set.preimage_comp

/- An intuitive way to think about filters, and a reformulation
of convergence.

Remember that, for every `s : Set α`, we have the principal filter
generated by `s`: it is the filter whose elements are sets
containing `s`.

We think of this filter as standing in for `s`, and we think of
more general filters as "generalized sets" of `α`. With this
point of view, if `F` is a filter on `α` and `s : Set α`, saying
that `s ∈ F` means that `s` "contains" the corresponding
"generalized set".

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
of the discrete space `X`. If you don't know what this means,
don't worry.)
-/

/- Now that we think of filters as generalized sets,
let's extend some set notions to them.

The first is the order relation: sets on `α` are
ordered by inclusion. How does it translate to filters?
Well, it means that every set that contains `t` also
contains `s`:
-/

example (s t : Set α) : s ⊆ t ↔
    (Filter.principal t).sets ⊆ (Filter.principal s).sets := by
  constructor
  · exact fun h _ hA ↦ le_trans h hA
  · exact fun h ↦ h (mem_principal_self t)

-- So this is how we define order on filters:
#print Filter.le_def  -- F ≤ G ↔ ∀ x ∈ G, x ∈ F

example (F : Filter α) (s : Set α) :
    𝓟 s ≤ F ↔ ∀ A ∈ F, s ⊆ A := by
  constructor
  · exact fun h _ hA ↦ h hA
  · exact fun h A hA ↦ h A hA

example (F : Filter α) (s : Set α) :
    F ≤ Filter.principal s ↔ s ∈ F := by
  constructor
  · exact fun h ↦ h (mem_principal_self s)
  · exact fun h _ hA ↦ F.sets_of_superset h hA

/- The second notion is the image of a filter by
a function `f : α → β`. This operation is called
`Filter.map`. The idea is that, if `F : Filter α`
and `V : Set β`, the statement
`V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F` should be true
by definition.-/

#print Filter.map

-- This is compatible to the definition for sets.
example {s : Set α} (f : α → β) :
    Filter.map f (Filter.principal s) = Filter.principal (f '' s) := by
  ext A
  change f ⁻¹'A ∈ 𝓟 s ↔ A ∈ 𝓟 (f '' s) -- 𝓟 = \ + MCP
  rw [mem_principal, mem_principal]
  exact Set.image_subset_iff.symm

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
-- This is the mathlib definition.
-- Tendsto₁ : ∀ U ∈ G, f ⁻¹' U ∈ F i.e.

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

/- Now to prove the compatibility of limits with compositions,
we use the properties of `Filter.map`.-/
#print Filter.map_mono -- `Filter.map f` is monotone.
-- If F ≤ F', then map f F ≤ map f F'.
#print Filter.map_map -- `Filter.map (g ∘ f) = Filter.map g ∘ Filter.map f`

-- Compatibility with composition.
example {X Y Z : Type*} (f : X → Y) (g : Y → Z) (F : Filter X)
    (G : Filter Y) (H : Filter Z) :
    Tendsto₂ f F G → Tendsto₂ g G H → Tendsto₂ (g ∘ f) F H := by
  intro h h'
  change map (g ∘ f) F ≤ H
  rw [← map_map]
  refine le_trans ?_ h'
  apply map_mono
  exact h

/- Among the other "set" operations, we have preimages, which
are called `Filter.comap` for filters.-/
#print Filter.comap --why this definition?
-- f : α → β and G a filter on β
-- s ∈ comap f G ↔ ∃ t ∈ G, f ⁻¹' t ⊆ s

example (s : Set β) (f : α → β) : comap f (𝓟 s) = 𝓟 (f ⁻¹' s) := by
  simp only [comap_principal]

/- If `f : α → β` is a function and `s : Set α`, `t : Set β`, then
we have `f '' s ⊆ t` if and only if `s ⊆ f ⁻¹' t`. We want to
have the same property for filters, i.e. for `F : Filter α` and
`G : Filter β`, we want `Filter.map f F ≤ G ↔ F ≤ Filter.comap f G`.
(In technical terms, this means that `Filter.map f` and `Filter.comap f`
form a Galois connection, i.e. an adjunction between poset categories.)
-/
#check Filter.map_le_iff_le_comap

example {f : α → β} {F : Filter α} {G : Filter β} :
    Filter.map f F ≤ G ↔ F ≤ Filter.comap f G := by
  constructor
  · intro h A hA
    rw [Filter.mem_comap] at hA
    obtain ⟨B, hb⟩ := hA
    have := h hb.1
    rw [Filter.mem_map] at this
    exact Filter.mem_of_superset this hb.2
  · intro h B hB
    rw [Filter.mem_map]
    apply h
    rw [Filter.mem_comap]
    use B

#print Tendsto₂

/- Using `Filter.comap`, we can give an equivalent definition
of `Tendsto`.-/

def Tendsto₃ {X Y : Type*} (f : X → Y) (F : Filter X)
    (G : Filter Y) := F ≤ Filter.comap f G
-- But mathlib uses the definition with `Filter.map`.

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₃ f F G := by
  rw [Tendsto₂, Tendsto₃, map_le_iff_le_comap]

/- `Filter.comap` is also compatible with composition of
functions, but just like for preimages, this reverses the
order:-/
#print Filter.comap_comap
-- Filter.comap m (Filter.comap n F) = Filter.comap (n ∘ m) F

/- We can use `Filter.comap` to define the intersection of a
filter with a set of `α`. For example, our `nhds_left a` at the
start is the intersection of `nhds a` and of `Set.Iic a`
(well, almost... this intersection would be a filter on
`Set.Iic a`).-/
example (a : ℝ) : nhds_left a = Filter.map Subtype.val
    (Filter.comap (Subtype.val : Set.Iic a → ℝ) (nhds a)) := by
  ext A
  simp only [nhds_left, gt_iff_lt, Filter.mem_mk, mem_setOf_eq, mem_map, mem_comap]
  constructor
  · intro ⟨ε, hpos, h⟩
    use Ioo (a - ε) (a + ε)
    constructor
    · rw [(nhds_basis_Ioo_pos a).mem_iff]
      use ε, hpos
    · intro ⟨x, hx⟩
      simp only [mem_preimage, mem_Ioo, and_imp]
      intro hleft _
      exact h ⟨hleft, hx⟩
  · intro ⟨U, hU₁, hU₂⟩
    rw [(nhds_basis_Ioo_pos a).mem_iff] at hU₁
    obtain ⟨ε, hpos, h⟩ := hU₁
    use ε, hpos
    intro x ⟨hx₁, hx₂⟩
    have : ⟨x, hx₂⟩ ∈ (Subtype.val : Iic a → ℝ) ⁻¹' U := by
      simp only [mem_preimage]
      exact h ⟨hx₁, lt_of_le_of_lt hx₂ ((lt_add_iff_pos_right _).mpr hpos)⟩
    exact mem_preimage.mp (hU₂ this)

example (s : Set α) (F : Filter α) : Filter s :=
  comap Subtype.val F
  -- Subtype.val : s → α
-- If t : Set s, t ∈ comap Subtype.val F ↔ ∃ u ∈ F, s ∩ u ⊆ t

/-
Other operations that we can expect to have on filters
if they are "generalized sets" are `sup` and `inf`, even
for infinite families.

(Remark: filters actually correspond to closed sets in some
compact topological space. The `inf` operations is just the
intersection, and the `sup` of a family of closed sets is the
closure of its union. But this shows that we cannot expect an
operation corresponding to the complement on sets.)
-/

-- The `sup` and `inf` for two filters.
#print Filter.mem_sup -- s ∈ F ⊔ G ↔ s ∈ F ∧ s ∈ G
#print Filter.mem_inf_iff -- s ∈ F ⊓ G ↔ ∃ t₁ ∈ F, ∃ t₂ ∈ G, s = t₁ ∩ t₂

-- The case of an arbitrary family:
#check Filter.mem_iSup -- indexed Sup
-- ∀ {α : Type u} {ι : Sort x} {x : Set α} {f : ι → Filter α},
--  x ∈ ⨆ f ↔ ∀ (i : ι), x ∈ f i -- \ + bigsup
#check Filter.mem_iInf
--∀ {α : Type u} {ι : Type u_2} {f : ι → Filter α} {U : Set α},
--  U ∈ ⨅ i, f i ↔ ∃ I : Set ι, I.Finite ∧
-- ∃ V : ↑I → Set α, (∀ (i : ↑I), V i ∈ f ↑i) ∧ U = ⋂ i, V i -- \ + biginf

-- What happens if we allow infinite intersections?

-- F ≤ 𝓟 s ↔ s ∈ F

example (F : Filter α) :
    F = ⨅ (s : F.sets), 𝓟 s := by  -- F is the inf of the family of
    -- principal filters greater than or equal to F
  apply le_antisymm
  · simp only [le_iInf_iff, le_principal_iff, Subtype.forall, Filter.mem_sets, imp_self,
    implies_true]
  · intro s hs
    rw [mem_iInf]
    use {⟨s, hs⟩} -- ok because ⟨s, hs⟩ : F.sets
    constructor
    · simp only [finite_singleton]
    · use fun p ↦ p.1
      constructor
      · simp only [mem_principal, subset_refl, implies_true]
      · simp only [iInter_coe_set, mem_singleton_iff, iInter_iInter_eq_left]


-- A finite intersection of members of a filter is in the
-- the filter. These are both `simp` lemmas.
#print Filter.sInter_mem
#print Filter.iInter_mem


/- We also have a smallest filter `⊥` (the principal filter
generated by the empty set, also called the trivial filter)
and a biggest filter `⊤` (generated by the universal set).-/

example (s : Set α) : s ∈ (⊥ : Filter α) := Filter.mem_bot

example (s : Set α) : s ∈ (⊤ : Filter α) ↔ s = univ := by
  simp only [mem_top]

/- Some lemmas require filters to be nontrivial, so there is
a class `Filter.NeBot`, and these lemma take `F.NeBot` as an
instance parameter.-/

#print Filter.NeBot

-- Mathlib knows that a lot of filters are not trivial.
#synth Filter.NeBot (Filter.atTop (α := ℕ))
#synth Filter.NeBot (nhds (1 : ℝ))

#print Filter.map_neBot
-- This is an instance, so mathlib automatically knows that,
-- if `F` is not trivial, then so is its `map` by any function.

/- If `F : Filter α` and `G : Filter β`, we can define the
product of `F` and `G`, which is a filter on `α × β`. We
write this `Filter.prod F G` or `F ×ˢ G`.
For example, if `a,b : ℝ`, then `nhds a ×ˢ nhds b` will
be `nhds ⟨a, b⟩`, the filter of neighborhoods of `⟨a, b⟩`
in `ℝ × ℝ`.-/

#print Filter.prod
-- F ×ˢ G = (Filter.comap Prod.fst F) ⊓ (Filter.comap Prod.snd G)
-- This means that `F ×ˢ G` is the biggest filter `H` on
-- `α × β` such that `Filter.map Prod.fst H ≤ F` and
-- `Filter.map Prod.snd H ≤ G`.

#check Filter.mem_prod_iff
-- s ∈ f ×ˢ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s

example (s : Set α) (t : Set β) : Set (α × β) := s ×ˢ t -- \ + x + \ + ^s
example (F : Filter α) (G : Filter β) : Filter (α × β) := F ×ˢ G

/- Actually, we also have arbitrary products of filters.-/
#print Filter.pi -- same formula as for `Filter.prod`:
-- ⨅ i, Filter.comap (Function.eval i) (f i)

/- Filter bases:
This is a generalization of principal filters. If `F : Filter α`
and `s : ι → Set α` is a family of sets of `α`, then we say
that `s` is a basis of `F` if
`∀ (t : Set α), t ∈ F ↔ ∃ (i : ι), s i ⊆ t`.

This is expressed by a `Prop`-valued structure `Filter.HasBasis`.
-/

#print Filter.HasBasis
/-
/-- We say that a filter `l` has a basis `s : ι → Set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
structure HasBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- A set `t` belongs to a filter `l` iff it includes an element of the basis. -/
  mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t

-/

-- Note the arguments: we don't just give `s : ι → Set α`, but
-- also a `p : ι → Prop` and only use as basis  the `s i`
-- for the `i : ι` such that `p i` holds. This is convenient
-- because `s` can then be defined on a more natural type, as in
-- the following example.
example (x₀ : ℝ) : HasBasis (𝓝 x₀) (p := fun ε : ℝ ↦ 0 < ε)
    (s := fun ε ↦ Ioo (x₀ - ε) (x₀ + ε)) :=
  nhds_basis_Ioo_pos x₀

example : HasBasis (atTop : Filter ℕ) (fun _ : ℕ ↦ True) (fun n ↦ Ici n) :=
  atTop_basis

-- Now to check convergence along filters, it suffices to
-- use the sets in the basis.
#check Filter.HasBasis.tendsto_iff  -- very useful result!

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔
    ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  rw [Filter.HasBasis.tendsto_iff atTop_basis (nhds_basis_Ioo_pos x₀)]
  simp

example (f : ℝ → ℝ) (a b : ℝ) :
    Tendsto f (𝓝 a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Ioo (a - δ) (a + δ) →
    f x ∈ Ioo (b - ε) (b + ε) := by
  rw [Filter.HasBasis.tendsto_iff (nhds_basis_Ioo_pos a) (nhds_basis_Ioo_pos b)]

#check nhds_basis_Ioo -- basis is (b, c) with b < a < c
#check nhds_basis_Ioo_pos  -- basis is (a - ε, a + ε) with ε > 0

example (f : ℝ → ℝ) (a b : ℝ) :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ (U : Set ℝ), b ∈ U ∧ IsOpen U →
    ∃ (V : Set ℝ), (a ∈ V ∧ IsOpen V) ∧ (∀ x ∈ V, f x ∈ U) := by
  rw [HasBasis.tendsto_iff (nhds_basis_opens a) (nhds_basis_opens b)]
-- I had switched `U` and `V` in `∀ x ∈ V, f x ∈ U`

#check nhds_basis_opens

-- If we know a basisof a filter, it is easy to describe
-- its members.
#check Filter.HasBasis.mem_iff

example (A : Set ℕ) : A ∈ atTop ↔ ∃ n, Set.Ici n ⊆ A := by
  rw [Filter.HasBasis.mem_iff (atTop_basis)]
  simp

/- Another use of filters is that they give a convenient
way to talk about properties that are true for `x` big enough,
for `x` close enough to a fixed point, for almost all `x` etc.

For this, we use the function `Filter.Eventually`. If
`p : α → Prop` and `F : Filter α`, then `Filter.Eventually p F`
(or `F.Eventually p`)
means that `{x | p x}` is an element of `F`. Intuitively, this
means that `p` is true on the "set" corresponding to `F`.

The notation for this is:
`∀ᶠ x in F, p x`. (\ + forall + \ + ^f)
-/

example : ∀ᶠ n in atTop (α := ℕ), 2 ≤ n := by
  dsimp [Filter.Eventually]
  simp
  use 2
  simp

example : ∀ᶠ x in nhds (0 : ℝ), |x| ≤ 1/2 := by
  dsimp [Filter.Eventually]
  rw [(nhds_basis_Ioo_pos 0).mem_iff]
  use 1/2
  constructor
  · simp only [one_div, inv_pos, Nat.ofNat_pos]
  · simp only [zero_sub, zero_add]
    intro x ⟨hx₁, hx₂⟩
    rw [mem_setOf_eq, abs_le]
    exact ⟨le_of_lt hx₁, le_of_lt hx₂⟩

/- Now let's see what the properties of a filter say about `∀ᶠ`:

(1) `⊤ ∈ F` means that: `∀ x, p x → ∀ᶠ x in F, p x`.-/
#check Eventually.of_forall

/-(2) The stability of `F` by taking a superset means that, if
`q : α → Prop` is another function, and if
`∀ᶠ x, p x` and `∀ x, p x → q x`, then `∀ᶠ x, q x`.-/
#check Eventually.mono

/-(3) The stability of `F` by intersections means that, if
`∀ᶠ x in F, p x` and `∀ᶠ x in F, q x`, then
`∀ᶠ x in F, p x ∧ q x`.-/
#check Filter.Eventually.and

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  dsimp [Filter.Eventually] at hP hQ ⊢
  exact atTop.inter_sets hP hQ

/- There are two special cases of `Filter.Eventually` for equalities
and inequalities:-/
#print Filter.EventuallyEq
#print Filter.EventuallyLE


/- They have special notation too:-/
example (u v : ℕ → ℝ) : (∀ᶠ n in atTop, u n = v n) ↔ u =ᶠ[atTop] v := Iff.refl _

example (u v : ℕ → ℝ) : (∀ᶠ n in atTop, u n ≤ v n) ↔ u ≤ᶠ[atTop] v := Iff.refl _

-- For example, two sequences that are eventually equal
-- for the filter `atTop` have the same limit.
example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

/- There is a tactic called `filter_upwards` to deal with goals
of the `∀ᶠ s in F, ...`.-/

/-- From the documentation:
`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intros a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing
`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/

-- Without `filter_upwards`.
example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  have := hP.and (hQ.and hR)
  apply Eventually.mono this
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h'' using h'' ⟨h, h'⟩

-- An exercise: if the sequence `u` converges to `x` and
-- `u n` is in `M` for `n` big enough, then `x` is in the closure
-- of `M`.

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := by
  rw [mem_closure_iff_clusterPt]
  change (𝓝 x ⊓ 𝓟 M).NeBot
  apply neBot_of_le (f := map u atTop)
  rw [le_inf_iff]
  refine ⟨hux, ?_⟩
  refine le_trans (map_mono (m := u) (le_principal_iff.mpr huM)) ?_
  simp only [map_principal, le_principal_iff, mem_principal, image_subset_iff]
  intro x
  simp

--Useful lemmas for the exercise:
#check mem_closure_iff_clusterPt
#print ClusterPt -- note that `ClusterPt x F` means by definition
                 -- that `𝓝 x ⊓ F` is not the `⊥` filter
#check le_principal_iff
#check neBot_of_le

/- Another filter notion is `Filter.Frequently`. You
would use it for example to express something like
"there exist arbitrarily large `n` in `ℕ` such that so and so".-/

#print Filter.Frequently
-- `Filter.Frequently p F` means `¬∀ᶠ (x : α) in f, ¬p x` i.e.
-- `{x | ¬p x} ∉ F`. It is written `∃ᶠ x in F, p x`.
-- This is actually equivalent to saying that, for every `A ∈ F`,
-- there exists `x ∈ A` such that `p x`. Don't believe me?

example (p : α → Prop) (F : Filter α) :
    (∃ᶠ x in F, p x) ↔ ∀ A ∈ F, ∃ x ∈ A, p x := by
  constructor
  · intro h A hA
    by_contra habs
    push_neg at habs
    have hsub : A ⊆ {x | ¬p x} := by
      intro x hx
      simp only [mem_setOf_eq, habs x hx, not_false_eq_true]
    have := F.mem_of_superset hA hsub
    exact h this
  · dsimp [Filter.Frequently]
    intro h habs
    obtain ⟨x, hx₁, hx₂⟩ := h _ habs
    simp only [mem_setOf_eq] at hx₁
    exact hx₁ hx₂

-- Of course, this result is already in mathlib:
#check Filter.frequently_iff

example : ∃ᶠ n in atTop (α := ℕ), Nat.Prime n := by
  rw [frequently_atTop]
  intro a
  obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes a
  use p
