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
-- instance instMembership : Membership (Set α) (Filter α) :=
--   ⟨fun U F => U ∈ F.sets⟩
-- NB: comment this, this is already declare in mathlib.

-- Examples:

-- If `a : α`, the set of sets containing `a` is a filter,
-- (and even an ultrafilter).
example (a : α) : Filter α where
  sets := {A | a ∈ A}
  univ_sets := by trivial
  sets_of_superset := by intro x y hin hsub; exact hsub hin
  inter_sets := by intro x y hx hy; constructor <;> trivial

-- More generally, if `s : Set α`, the set of sets containing `s`
-- is a filter.
example (s : Set α) : Filter α where
  sets := {A : Set α | s ⊆ A}
  univ_sets := by simp
  sets_of_superset := by intro x y hx hxy a hs; exact hxy (hx hs)
  inter_sets := by intro x y hx hxy; simp; constructor <;> trivial

-- This is called a principal filter, `Filter.principal` in mathlib:
#print Filter.principal

-- The set of sets of natural integers (or real numbers, or
-- rational numbers...) that are "big enough" is a filter.
example : Filter ℕ where
  sets := {A | ∃ n, Set.Ici n ⊆ A}
  univ_sets := by simp
  sets_of_superset := by intro x y ⟨ n, hn ⟩ hxy; use n; intro m h; apply hxy; exact hn h
  inter_sets := by intro x y ⟨ nx, hnx ⟩ ⟨ ny, hny ⟩; simp
                   cases Nat.decLe nx ny 
                   · use nx
                     have : Ici nx ⊆ Ici ny := by intro m hnx; apply mem_Ici.mpr
                                                  apply mem_Ici.mp at hnx; omega
                     constructor <;> intro m h
                     apply hnx; trivial; apply hny; apply this; trivial
                   · use ny
                     have : Ici ny ⊆ Ici nx := by intro m hny; apply mem_Ici.mpr
                                                  apply mem_Ici.mp at hny; omega
                     constructor <;> intro m h
                     apply hnx; apply this; trivial; apply hny; trivial

-- This filter is called `Filter.atTop`:
#print Filter.atTop
#print Filter.mem_atTop

-- There is also a filter for "small enough" elements, called
-- `Filter.atBot`.

-- The neighborhoods of a point in `ℝ` (or any metric or more
-- generally topological space):
example (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Set.Ioo (a - ε) (a + ε) ⊆ A}
  univ_sets := by simp; use 1; aesop
  sets_of_superset := by intro x y ⟨ ε, ⟨ hε, hx ⟩ ⟩ hs; simp; use ε; constructor
                         trivial; intro a h; apply hs; apply hx; exact h
  inter_sets := by intro x y ⟨ εx, ⟨ hεx, hx ⟩ ⟩ ⟨ εy, ⟨ hεy, hy ⟩ ⟩; simp
                   cases Real.decidableLE εx εy
                   · use εy; constructor; trivial; constructor <;> intro b h
                     · apply hx; rw [mem_Ioo]; rw [mem_Ioo] at h;
                       constructor <;> linarith
                     · apply hy; exact h
                   · use εx; constructor; trivial; constructor <;> intro b h
                     · apply hx; exact h
                     · apply hy; rw [mem_Ioo]; rw [mem_Ioo] at h
                       constructor <;> linarith

example (a : ℝ) : Filter ℝ where
  sets := {A | ∃ (U : Set ℝ), IsOpen U ∧ a ∈ U ∧ U ⊆ A}
  univ_sets := by simp; use univ; constructor; exact isOpen_univ; trivial
  sets_of_superset := by intro x y ⟨ U, ⟨ hU, ⟨ ha, hx ⟩ ⟩ ⟩ hxy; use U; constructor
                         trivial; constructor; trivial; intro z hz; apply hxy; exact hx hz
  inter_sets := by intro x y ⟨ U, ⟨ hU, ⟨ ha, hx ⟩ ⟩ ⟩ ⟨ V, ⟨ hV, ⟨ ha', hy ⟩ ⟩ ⟩
                   use (U ∩ V); constructor; exact IsOpen.inter hU hV; constructor
                   constructor <;> assumption; intro a h; constructor; apply hx
                   exact h.left; apply hy; exact h.right

-- This filter is called `nhs` or `𝓝` (\ + nhds):
#print nhds

-- If `a : ℝ`, we can also look at the set of subsets of `ℝ`
-- that contain an interval `(a-ε,a]` with `ε > 0`, and this is
-- still a filter.
def nhds_left (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Set.Ioc (a - ε) a ⊆ A}
  univ_sets := by simp; use 1; linarith
  sets_of_superset := by intro x y ⟨ ε, ⟨ hε, h ⟩ ⟩ hxy; use ε; constructor
                         assumption; intro b hb; apply hxy; apply h; rw [mem_Ioc]
                         rw [mem_Ioc] at hb; assumption
  inter_sets := by intro x y ⟨ εx, ⟨ hεx, h ⟩ ⟩ ⟨ εy, ⟨ hεy, h' ⟩ ⟩
                   cases Real.decidableLE εx εy
                   · use εy; constructor; assumption; intro b hb; constructor
                     · apply h; rw [mem_Ioc]; rw [mem_Ioc] at hb; constructor
                       linarith; exact hb.right
                     · apply h'; assumption                       
                   · use εx; constructor; assumption; intro b hb; constructor
                     · apply h; assumption
                     · apply h'; rw [mem_Ioc]; rw [mem_Ioc] at hb; constructor
                       linarith; exact hb.right

/- If `α` has a measure `μ`, then we have a filter
`MesureTheory.ae μ` whose elements are co-null sets (i.e.
measurable sets whose complement has measure zero). This
is "the set of almost all elements of `α`".
-/
#print MeasureTheory.ae

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
express the fact that `u` converges to `b : ℝ` with filters:
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
    Tendsto₁ f F G → Tendsto₁ g G H → Tendsto₁ (g ∘ f) F H := by
  intro hf hg U hU; rw [preimage_comp]; apply hf; apply hg; assumption

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
  · intro h X ht a hs; apply ht; apply h; assumption
  · intro h x hs; apply h; simp; assumption

-- So this is how we define order on filters:
#print Filter.le_def  -- F ≤ G ↔ ∀ x ∈ G, x ∈ F

example (F : Filter α) (s : Set α) :
    Filter.principal s ≤ F ↔ ∀ A ∈ F, s ⊆ A := by
  rw [Filter.le_def]; constructor
  · intro h A hA x hs
    have := (h A hA)
    apply this; assumption
  · intro h A hA x hs; apply h <;> assumption

example (F : Filter α) (s : Set α) :
    F ≤ Filter.principal s ↔ s ∈ F := by
  rw [Filter.le_def]; constructor
  · intro h; apply h; simp
  · intro h A hA; exact mem_of_superset h hA

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
  ext X; constructor
  · intro h y ⟨ x, ⟨ hx, e ⟩ ⟩; simp at h; rw [←e]; apply h; assumption
  · intro h x hx; apply h; use x

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
    Tendsto₂ f F G → Tendsto₂ g G H → Tendsto₂ (g ∘ f) F H := by
  intros hf hg; unfold Tendsto₂; rw [←map_map]
  have : map g (map f F) ≤ map g G := by apply map_mono; assumption
  apply le_trans; assumption; assumption

/- Among the other "set" operations, we have preimages, which
are called `Filter.comap` for filters.-/
#print Filter.comap --why this definition?

/- If `f : α → β` is a function and `s : Set α`, `t : Set β`, then
we have `f '' s ⊆ t` if and only if `s ⊆ f ⁻¹' t`. We want to
have the same property for filters, i.e. for `F : Filter α` and
`G : Filter β`, we want `Filter.map f F ≤ G ↔ F ≤ Filter.comap f G`.
(In technical terms, this means that `Filter.map f` and `Filter.comap f`
form a Galois connection, i.e. an adjunction between poset categories.)
-/
#print Filter.map_le_iff_le_comap

example {f : α → β} {F : Filter α} {G : Filter β} :
    Filter.map f F ≤ G ↔ F ≤ Filter.comap f G := by
  constructor
  · intro h x ⟨ y, ⟨ ht, hs ⟩ ⟩; apply mem_of_superset; exact (h ht); assumption
  · intro h x hx; apply h; use x

/- Using `Filter.comap`, we can give an equivalent definition
of `Tendsto`.-/

def Tendsto₃ {X Y : Type*} (f : X → Y) (F : Filter X)
    (G : Filter Y) := F ≤ Filter.comap f G
-- But mathlib uses the definition with `Filter.map`.

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₃ f F G := by
  unfold Tendsto₂; unfold Tendsto₃; exact map_le_iff_le_comap

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
  ext X; constructor
  · intro ⟨ ε, ⟨ hε, h ⟩ ⟩; simp; use (Icc (a - (ε/2)) (a + ε)); constructor
    rw [Icc_mem_nhds_iff, mem_Ioo]; constructor <;> linarith
    intro ⟨ x, hx ⟩ hin; rw [mem_Iic] at hx; simp at hin; simp; apply h
    rw [mem_Ioc]; constructor <;> linarith
  · intro ⟨ Y, ⟨ hY, hs ⟩ ⟩; rw [← exists_mem_subset_iff]
    rw [mem_nhds_iff_exists_Ioo_subset] at hY
    cases hY with
    | intro x h => cases h with
      | intro y h => use (Ioc x a); constructor; use (a - x); constructor
                     simp at h; linarith; simp; intro z h'; rw [mem_Ioc] at h'
                     simp at h; have := h.right
                     rw [Subtype.preimage_val_subset_preimage_val_iff] at hs
                     simp at hs; apply hs; constructor
                     · rw [mem_Iic]; exact h'.right
                     · apply this; rw [mem_Ioo]; constructor; exact h'.left; linarith
    
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
#print Filter.mem_iSup
-- ∀ {α : Type u} {ι : Sort x} {x : Set α} {f : ι → Filter α},
--  x ∈ iSup f ↔ ∀ (i : ι), x ∈ f i
#print Filter.mem_iInf
--∀ {α : Type u} {ι : Type u_2} {s : ι → Filter α} {U : Set α},
--  U ∈ ⨅ i, s i ↔ ∃ I, I.Finite ∧
-- ∃ V, (∀ (i : ↑I), V i ∈ s ↑i) ∧ U = ⋂ i, V i

-- What happens if we allow infinite intersections?

example (F : Filter α) :
    F = ⨅ (s : F.sets), Filter.principal s := by
  apply le_antisymm
  simp only [le_iInf_iff, le_principal_iff, Subtype.forall, Filter.mem_sets]
  intro; tauto
  intro s hs; rw [mem_iInf]; use {⟨s, hs⟩}; constructor
  · simp only [finite_singleton]
  · use (λ p ↦ p.1); constructor
    · simp
    · simp

-- A finite intersection of members of a filter is in the
-- the filter. These are both `simp` lemmas.
#print Filter.sInter_mem
#print Filter.iInter_mem

/- We also have a smallest filter `⊥` (the principal filter
generated by the empty set, also called the trivial filter)
and a biggest filter `⊤` (generated by the universal set).-/

example (s : Set α) : s ∈ (⊥ : Filter α) := Filter.mem_bot

example (s : Set α) : s ∈ (⊤ : Filter α) ↔ s = (⊤ : Set α) := by
  simp only [Filter.mem_top, Set.top_eq_univ]

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
write this `Filter.prod F G` or `F × G`.
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

/- Actually, we also have arbitrary products of filters.-/
#check Filter.pi -- same formula as for `Filter.prod`:
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
example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε)
    fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀

example : HasBasis (atTop : Filter ℕ) (fun _ : ℕ ↦ True) Ici := atTop_basis

-- Now to check convergence along filters, it suffices to
-- use the sets in the basis.
#check Filter.HasBasis.tendsto_iff  -- very useful result!

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔
    ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp

example (f : ℝ → ℝ) (a b : ℝ) :
    Tendsto f (𝓝 a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Ioo (a - δ) (a + δ) → f x ∈ Ioo (b - ε) (b + ε) := by
  have ha := nhds_basis_Ioo_pos a
  have hb := nhds_basis_Ioo_pos b
  rw [HasBasis.tendsto_iff ha hb]

#check nhds_basis_opens

example (f : ℝ → ℝ) (a b : ℝ) :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ (U : Set ℝ), IsOpen U ∧ b ∈ U →
    ∃ (V : Set ℝ), IsOpen V ∧ a ∈ V ∧ V ⊆ f ⁻¹' U := by
  have ha := nhds_basis_opens a
  have hb := nhds_basis_opens b
  rw [HasBasis.tendsto_iff ha hb]
  simp; constructor
  · intro h U hU hb
    cases (h U hb hU) with
    | intro V h => use V; constructor; exact h.left.right; constructor; exact h.left.left
                   exact h.right
  · intro h U hb hU
    cases (h U hU hb) with
    | intro V h => use V; constructor; constructor; exact h.right.left; exact h.left
                   exact h.right.right

-- If we know a basis of a filter, it is easy to describe
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
means that `{x | p x}` is an element of `F`. Intuitively, this
means that `p` is true on the "set" corresponding to `F`

The notation for this is:
`∀ᶠ x in F, p x`. (\ + forall + \ + ^f)
-/

example : ∀ᶠ n in atTop (α := ℕ), 2 ≤ n := by simp; use 2; intros; assumption

example : ∀ᶠ x in nhds (0 : ℝ), |x| ≤ 1/2 := by 
  rw [eventually_nhds_iff]; use (Ioo (-2⁻¹) (2⁻¹)); constructor
  · intro y hy; simp at hy; rw [abs_le]; simp; constructor <;> linarith
  · constructor; exact isOpen_Ioo; simp

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
  apply Eventually.and <;> assumption

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
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩

-- An exercise: if the sequence `u` converges to `x` and
-- `u n` is in `M` for `n` big enough, then `x` is in the closure
-- of `M`.

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := by
  rw [mem_closure_iff_clusterPt]
  have : map u atTop ≤ (Filter.principal M) := by
    rw [le_principal_iff]; simp; rw [eventually_atTop] at huM; assumption
  have hle : map u atTop ≤ (nhds x ⊓ (Filter.principal M)) := 
    Lattice.le_inf (map u atTop) (𝓝 x) (𝓟 M) hux this
  have hmap : (map u atTop).NeBot := by
    exact map_neBot
  unfold ClusterPt
  have := by exact neBot_of_le hle
  assumption

--Useful lemmas for the exercise:
#check mem_closure_iff_clusterPt
#print ClusterPt -- note that `ClusterPt F x` means by definition
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
  · intro h A hA; by_contra h'; apply h; filter_upwards [hA]; intro x hp hp'; apply h'; use x
  · intro h h'; rw [eventually_iff] at h'; simp at h'
    rw [← exists_mem_subset_iff] at h'; cases h' with
    | intro A h' => cases (h A h'.left) with
      | intro x hp => have : x ∈ {x | ¬ p x} := by apply h'.right; exact hp.left
                      simp at this; apply this; exact hp.right
                      
