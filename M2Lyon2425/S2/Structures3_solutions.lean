import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Topology.MetricSpace.Basic

-- import Mathlib.Data.NNReal.Basic


noncomputable section

open Classical

section LocalInstances

open scoped Filter Uniformity

#print UniformSpace
-- One constructor and four fields

example : instUniformSpaceNat = ⊥ := rfl

example : (uniformity ℕ) = (𝓟 idRel) := rfl -- this is the "trivial" or "discrete" uniformity.

#synth UniformSpace ℕ -- instUniformSpaceNat
attribute [- instance] instUniformSpaceNat --this is local, it only applies to the current section

#synth UniformSpace ℕ -- failed to synthesize

def PSM_Nat : PseudoMetricSpace ℕ where --use the 💡-action
  dist := fun n m ↦ |2 ^ (- n : ℤ) - 2 ^ (- m : ℤ)|
  dist_self := by simp only [zpow_neg, zpow_natCast, sub_self, abs_zero, implies_true]
  dist_comm := fun _ _ ↦ abs_sub_comm _ _
  dist_triangle := fun _ _ _ ↦ abs_sub_le .. -- a word about `..`

attribute [instance] PSM_Nat

-- local instance : PseudoMetricSpace ℕ where
--   dist := fun n m ↦ |2 ^ (- n : ℤ) - 2 ^ (- m : ℤ)|
--   dist_self := by simp only [zpow_neg, zpow_natCast, sub_self, abs_zero, implies_true]
--   dist_comm := fun _ _ ↦ abs_sub_comm ..
--   dist_triangle := fun _ _ _ ↦ abs_sub_le _ _ _

#synth UniformSpace ℕ -- PseudoMetricSpace.toUniformSpace

/-! This is actually true! See `Counterexamples/DiscreteTopologyNonDiscreteUniformity.lean`-/
lemma idIsCauchy : CauchySeq (id : ℕ → ℕ) := by sorry

example : CauchySeq (id : ℕ → ℕ) := idIsCauchy

end LocalInstances

-- This does not work, since we have quit the `LocalInstance` section
example : CauchySeq (id : ℕ → ℕ) := idIsCauchy


-- `⌘`


noncomputable section Synonyms

notation "𝒩" => ℕ
#check (37 : 𝒩)

abbrev AbbNat := ℕ
#check (37 : AbbNat)

def DefNat := ℕ
#check (37 : DefNat)

def DefSucc (a : ℤ) := a + 1 --definition as in Mathlib
abbrev AbbSucc (a : ℤ) := a + 1 --

example (a : ℤ) : DefSucc (DefSucc a) = a + 2 := by simp only [add_assoc, Int.reduceAdd]

example (a : ℤ) : AbbSucc (AbbSucc a) = a + 2 := by simp only [add_assoc, Int.reduceAdd]


-- `⌘`


abbrev 𝓡 := ℝ --type 𝓡 with \MCR
#synth TopologicalSpace 𝓡

attribute [-instance] UniformSpace.toTopologicalSpace
#synth TopologicalSpace ℝ

instance TopSpace𝓡 : TopologicalSpace 𝓡 := ⊥
#synth TopologicalSpace 𝓡
#synth TopologicalSpace ℝ

example : Continuous (fun x : ℝ ↦ if x < 0 then (0 : ℝ) else 1) := by
  apply continuous_bot
/-`continuous_bot` is the statement saying that every function leaving from a discrete space
is automatically continuous. -/


def ℛ := ℝ --type ℛ with \McR

#synth TopologicalSpace ℛ
#synth Field ℛ

instance : TopologicalSpace ℛ := ⊥

instance : Field ℛ := inferInstanceAs (Field ℝ)

#synth CommRing ℛ
#synth CommRing 𝓡

instance : LT ℛ := inferInstanceAs <| LT ℝ -- a word about `<|`

lemma ContJump : Continuous (fun x : ℛ ↦ if x < 0 then (0 : ℛ) else 1) := by
  apply continuous_bot

lemma ContJump' : Continuous (fun x : 𝓡 ↦ if x < 0 then (0 : 𝓡) else 1) := by
  apply continuous_bot

-- This might be a problem!
lemma ContJump'' : Continuous (fun x : ℝ ↦ if x < 0 then (0 : ℝ) else 1) := by
  apply continuous_bot

end Synonyms

-- Even leaving the `Synonyms` section, the following still works.
example : Continuous (fun x : ℛ × ℛ ↦ if x.1 < 0 then (0 : ℛ) else 1) := by
  exact ContJump.comp continuous_fst


-- `⌘`


section Structures


structure OneNat where
  fst : ℕ

structure TwoNat where
  pair ::
  fst : ℕ
  snd : ℕ

whatsnew in
@[ext]
structure Couple where
  left : ℕ
  right : ℕ

whatsnew in
@[class]
structure OrderedPairs where
  fst : ℕ
  snd : ℕ
  order : fst ≤ snd -- this field depends upon the previous two.

#check OneNat.mk
#check TwoNat.mk
#check TwoNat.pair
#check OrderedPairs.mk
#check order
#check OrderedPairs.order


structure TwoTerms (α : Type) where
  fst : α
  snd : α

structure Mess (α β γ : Type) [Zero α] [TopologicalSpace β] [UniformSpace γ] :=--`where` or `:=`
  a : α := 0
  f : α → β → γ → γ
  cont : Continuous (f a)

#print Mess


-- `⌘`


attribute [-instance] TopSpace𝓡
-- ## Constructing terms

example : TwoNat := sorry --farlo con `:=`, poi aggiungere _, lampadina, etc...

open Real

-- What happens if we have a default value?
def x1 : Mess ℕ ℝ ℝ where
  f := fun n x y ↦ n + x + y
  cont := by
    simp only [CharP.cast_eq_zero, zero_add]
    apply continuous_pi
    exact fun i ↦ continuous_add_right i

def x2 : Mess ℕ ℕ ℕ where
  a := 37
  f := fun n x y ↦ n + x + y
  cont := by
    apply continuous_bot

example (x : TwoNat) : Couple where
  left := x.fst
  right := x.snd

-- Same construction, different syntax
example (x : TwoNat) : Couple := {left := x.fst, right := x.snd}

example : Couple := ⟨3, 2⟩

example (x : OneNat) : Couple :=
  {left := x.1, right := x.1}


-- `⌘`


-- This forgets the label and takes it back.
example (x : OneNat) : TwoNat :=
  {x with snd := x.1}

-- another syntax
example (x : OneNat) : TwoNat where
  __ := x
  snd := x.1

example (x : TwoNat) : OneNat := {x with} --without the `with` the extra-field is not thrown away

example (x : TwoNat) : OneNat where
 __ := x

example (x : TwoNat) : Couple := x

example (x : OneNat) : Couple := sorry
  -- {x with left := x.1} fields missing: 'right'
--so, it does not "populate missing fields with the first available type-correct term: labels matter"

example (x : OneNat) : ℕ := sorry--{x with}

structure Mix where
  fst : ℕ
  right : ℕ

#check Mix.mk

def mix1 (x : TwoNat) (y : Couple) : Mix :=
  {x, y with}
/- remember that `x := {x.fst, x.snd}`, `y = {y.left, y.right}`
  and `Mix.mk` takes a `fst : ℕ` and `right : ℕ`: se we need to throw away `x.snd` and `y.left`-/

def mix1' (x : TwoNat) (y : Couple) : Mix where
  __ := x
  __ := y

-- the order does not really matter, it "destructs and reconstructs".
def mix2 (x : TwoNat) (y : Couple) : Mix :=
  {y, x with}


example : mix1 = mix1' := rfl

example : mix1 = mix2 := rfl


-- An example with structures having three terms.
structure Mix' where
  snd : ℕ
  left : ℕ

structure ThreeNat where
  fst : ℕ
  snd : ℕ
  thrd : ℕ

structure Mix₃ where
  right : ℕ
  left : ℕ
  thrd : ℕ

/- `x := {x.fst, x.right}`, `y := {y.snd, y.left}`, `z := {z.fst, z.snd, z.thrd}` and `Mix.mk` takes
a `fst : ℕ` and a `right : ℕ`: we need to throw away `x.left`, `y.left`, `z.snd` and `z.thrd`-/
example (x : Mix) (y : Mix') (z : ThreeNat) : Mix₃ :=
  {x, y, z with}

-- A final example with a `Prop`-valued field:

def f₁ : Mess ℕ ℕ ℕ where
  f := fun a b ↦ a + b
  cont := {isOpen_preimage := fun _ _ ↦ trivial}
  -- cont := ⟨fun _ _ ↦ trivial⟩

def f₂ : Mess ℕ ℕ ℕ where
  f := fun a b ↦ a + b
  cont := continuous_of_discreteTopology

-- `Prop`-valued fields disappear by proof irrelevance
example : f₁ = f₂ := rfl


-- `⌘`


-- ## Extends


structure TwoNatExt extends OneNat where
  snd : ℕ

structure OneNatOneInt where
  fst : ℕ
  snd : ℤ

structure Blob extends OneNatOneInt, OneNat
structure Blob' extends OneNatOneInt, TwoNat


/- Under the hood, Lean destructs all these terms and reconstructs them "in the right order" --- but
keeping labels. -/

def TwoExtToCouple : TwoNatExt → Couple := by --fun x ↦ {left := x.1, right := x.2} -- error! why?
  rintro ⟨x, y⟩ -- by def, `TwoNatExt` extends `OneNat`, so `x : OneNat`. So,
  exact {left := x.1, right := y}

def TwoNatToCouple : TwoNat → Couple := fun x ↦ {left := x.1, right := x.2}

/- And if there are duplicates? Remember that
  `structure Mix where`
      `fst : ℕ`
      `right : ℕ`     -/

structure ThreeNatExt extends TwoNat, Mix

#print ThreeNatExt

/- Overlapping fields are not duplicated; moreover, whenever possible, fields will coincide with
constructors of the parent structure; in case of overlapping fields, things are destructured. -/


def TwoNatToExt : TwoNat → TwoNatExt := fun x ↦ {x with}

/- `with` is able to
1. Destruct `x` into `x.fst` and get a `OneNat`
2. Out of the `OneNat` reuire another `ℕ` to define a `TwoNatExt`
3. Destruct `x` into `x.snd` and get the missing field. -/

example (x : TwoNat) : TwoNatToExt x = ⟨⟨x.fst⟩, x.snd⟩ := rfl


/- Remember
    `mix1 (x : TwoNat) (y : Couple) : Mix := {x, y with}` and
    `mix2 (x : TwoNat) (y : Couple) : Mix := {y, x with}` -/

def mix3 (x : TwoNatExt) (y : Couple) : Mix :=
  {x, y with}

example (x : TwoNat) (y : Couple) : mix1 x y = mix3 (TwoNatToExt x) y := rfl


/- Remember that `ThreeNatExt extends TwoNat, Mix` and
  `structure Mix where`
        `fst : ℕ`
        `right : ℕ`     -/

def M₁ : Mix := {fst := 17, right := 11}
def two : TwoNat := {fst := 1, snd := 2}

def three₁ : ThreeNatExt := {M₁, two with}
def three₁' : ThreeNatExt := {two, M₁ with}

example : three₁.fst = 17 := by rfl
example : three₁'.fst = 1 := by rfl

/- So in reality Lean is first using the first variable (`M` or `two`), possibly throwing away
useless stuff, and then using what follows to complete them -/

example : three₁ = three₁' := sorry--rfl -- (they're even different, not simply not `defeq`..._
--  indeed, `three₁={fst = 17, snd = 2, right = 11}` while `three₁'={fst = 1, snd = 2, right = 11}`-/


def M₂ : Mix := {fst := 13, right := 11}
def three₂' : ThreeNatExt := {two, M₂ with}

example : three₂'.fst = 1 := rfl
example : three₁' = three₂' := rfl -- one uses `M₁`, and the other uses `M₂`.
/- both are `{fst = 1, snd = 2, right = 11}` (the field `left` has been discharged) . -/

structure TwoNatExtLeft extends TwoNat where
  left : ℕ

example (x : ThreeNat) (y : Couple) : TwoNatExtLeft := sorry


-- `⌘`


/- ### In True Math
Remember the piece of code-/

-- We can now go back to what we saw last week: remember that we defined
class AddMonoidBad (M : Type) extends Add M, AddZeroClass M

instance : AddMonoidBad ℕ where --created using `:=` → `_` → 💡
  add := Nat.add
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero

instance : AddMonoidBad ℕ := ⟨Nat.zero_add, Nat.add_zero⟩
-- instance : AddMonoidBad ℕ := ⟨Nat.add_zero, Nat.zero_add⟩ -- order matters!

instance : AddMonoidBad ℕ := {Nat.instAddMonoid with}

instance : AddMonoidBad ℕ where
  __ := Nat.instAddMonoid

end Structures

section Exercises
attribute [-instance] TopSpace𝓡

/- ## Exercise 1
Define the class of metric spaces (but call them `SpaceWithMetric` to avoid conflict with the
existing library) as defined in https://en.wikipedia.org/wiki/Metric_space#Definition, and deduce
an instance of `TopologicalSpace` on every `SpaceWithMetric`.

Explain why this is the *wrong* choice, on an explicit example, and fix this.
-/

@[ext]
class SpaceWithMetric (X : Type) where
  d : X → X → ℝ
  dist_eq_zero (x : X) : d x x = 0
  dist_pos (x y : X) : x ≠ y → 0 < d x y
  symm (x y : X) : d x y = d y x
  triangle (x y z : X) : d x z ≤ d x y + d y z

@[simp]
instance (X : Type) [SpaceWithMetric X] : TopologicalSpace X where
  IsOpen := by
    intro S
    exact ∀ x ∈ S, ∃ ρ : ℝ, 0 < ρ ∧ {y | SpaceWithMetric.d x y < ρ} ⊆ S
  isOpen_univ := by
    by_cases hX : Nonempty X
    · rintro x -
      use 1
      simp
    · tauto
  isOpen_inter := by
    intro S T hS hT x ⟨hxS, hxT⟩
    let ρS := (hS x hxS).choose
    let ρT := (hT x hxT).choose
    use min ρS ρT
    constructor
    · apply lt_min
      exact (hS x hxS).choose_spec.1
      exact (hT x hxT).choose_spec.1
    apply Set.subset_inter
    · apply subset_trans _ (hS x hxS).choose_spec.2
      intro _ hy
      simp only [lt_min_iff, Set.mem_setOf_eq] at hy
      exact hy.1
    · apply subset_trans _ (hT x hxT).choose_spec.2
      intro _ hy
      simp only [lt_min_iff, Set.mem_setOf_eq] at hy
      exact hy.2
  isOpen_sUnion := by
    intro Ω hΩ x ⟨T, hT, hx⟩
    use (hΩ T hT x hx).choose
    constructor
    · exact (hΩ T hT x hx).choose_spec.1
    apply subset_trans (hΩ T hT x hx).choose_spec.2
    exact Set.subset_sUnion_of_subset Ω T (by rfl) hT

@[simp]
instance : SpaceWithMetric ℝ where
  d := fun x y ↦ dist x y
  dist_eq_zero := by simp
  dist_pos := fun x y ↦ (dist_pos).mpr
  symm := dist_comm
  triangle := by exact fun x y z ↦ dist_triangle x y z


#synth TopologicalSpace ℝ

example : Continuous (fun x : ℝ ↦ x + 1 ) := by
  sorry
  -- exact continuous_add_right 1

example : instTopologicalSpaceOfSpaceWithMetric ℝ = UniformSpace.toTopologicalSpace := by
  ext U
  rw [Metric.isOpen_iff, IsOpen]
  simp only [instTopologicalSpaceOfSpaceWithMetric, dist_comm, Metric.ball, instSpaceWithMetricReal,
    gt_iff_lt]

@[ext]
class SpaceWithMetricRight (X : Type) extends TopologicalSpace X where
  d : X → X → ℝ
  dist_eq_zero (x : X) : d x x = 0
  dist_pos (x y : X) : x ≠ y → 0 < d x y
  symm (x y : X) : d x y = d y x
  triangle (x y z : X) : d x z ≤ d x y + d y z
  top_eq : ∀ S : Set X, _root_.IsOpen S ↔ ∀ x ∈ S, ∃ ρ : ℝ, 0 < ρ ∧ {y | d x y < ρ} ⊆ S

instance (X : Type) [SpaceWithMetricRight X] : TopologicalSpace X := inferInstance

attribute [-instance] instTopologicalSpaceOfSpaceWithMetric

instance : SpaceWithMetricRight ℝ where
  d := fun x y ↦ dist x y
  dist_eq_zero := by simp
  dist_pos := fun x y ↦ (dist_pos).mpr
  symm := dist_comm
  triangle := by exact fun x y z ↦ dist_triangle x y z
  top_eq := by
    intro S
    rw [Metric.isOpen_iff]
    simp only [instTopologicalSpaceOfSpaceWithMetric, dist_comm, Metric.ball, instSpaceWithMetricReal,
      gt_iff_lt]

#synth TopologicalSpace ℝ

example : Continuous (fun x : ℝ ↦ x + 1 ) := by
  exact continuous_add_right 1

example : instTopologicalSpaceOfSpaceWithMetricRight ℝ = UniformSpace.toTopologicalSpace := rfl


-- ## Exercise 2
open scoped NNReal
--Recall from last lecture the two classes below, and the test-variable `p`:
class NormedModuleBad (M : Type*) [AddCommGroup M] where
  norm_b : M → ℝ≥0
export NormedModuleBad (norm_b)

notation "‖" e "‖₀" => norm_b e

instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [NormedModuleBad M] [NormedModuleBad N] :
    NormedModuleBad (M × N) where
  norm_b := fun ⟨m, n⟩ ↦ max ‖m‖₀ ‖n‖₀

class ModuleWithRel (M : Type*) [AddCommGroup M] where
  rel : M → M → Prop

export ModuleWithRel (rel)

instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [ModuleWithRel M] [ModuleWithRel N] :
    ModuleWithRel (M × N) where
  rel := fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)

variable (p : ∀ {T : Type}, (T → Prop) → Prop)
/- When defining a `ModuleWithRel` instance on any `NormedModuleBad` we used the relation "being in the
same ball of radius `1`. Clearly the choice of `1` was arbitrary.

Define an infinite collection of instances of `ModuleWithRel` on any `NormedModuleBad` indexed by
`ρ : ℝ≥0`, and reproduce both the bad and the good example.

There are (at least) two ways:
* Enrich the `NormedModule`'s structure with a `ρ`: this is straightforward.
* Keep `ρ` as a variable: this is much harder, both because Lean won't be very happy with a
`class` depending on a variable and because there will *really* be different instances even with
good choices, so a kind of "internal rewriting" is needed.
-/

class NMB_r (M : Type) extends AddCommGroup M, NormedModuleBad M where
  ρ : ℝ≥0

instance (M : Type) [NMB_r M] : ModuleWithRel M where
  rel := fun x y ↦ ‖x - y‖₀ ≤ NMB_r.ρ M

instance (M N : Type) [NMB_r M] [NMB_r N] : NMB_r (M × N) where
  ρ := max (NMB_r.ρ M) (NMB_r.ρ N)

instance (M : Type) [NMB_r M] : ModuleWithRel M where
  rel := fun x y ↦ ‖ x - y ‖₀ ≤ NMB_r.ρ M

example (ρ : ℝ≥0) (hp : ∀ M : Type, [NMB_r M] → ∀ m : M, p (rel m))
    (M : Type) [NMB_r M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  -- exact hp
  sorry

class NMG_r (M : Type) extends AddCommGroup M, NormedModuleBad M where
  ρ : ℝ≥0
  rel_ρ := fun x y ↦ norm_b (x - y) ≤ ρ

instance (M : Type) [NMG_r M] : ModuleWithRel M where
  rel := NMG_r.rel_ρ--fun x y ↦ ‖x - y‖₁ ≤ NMG_r.ρ M

instance (M N : Type) [NMG_r M] [NMG_r N] : NMG_r (M × N) where
  ρ := max (NMG_r.ρ M) (NMG_r.ρ N)
  norm_b := fun ⟨m, n⟩ ↦ max ‖m‖₀ ‖n‖₀
  rel_ρ := rel

example /- (ρ : ℝ≥0) -/ (hp : ∀ M : Type, [NMG_r M] → ∀ m : M, p (rel m))
    (M : Type) [NMG_r M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  exact hp

-- ### The hard approach

@[nolint unusedArguments]
def aliasR (M : Type*) (ρ : ℝ≥0) [AddCommGroup M] := M

class AsAliasR (M : Type*) (ρ : ℝ≥0) [AddCommGroup M] :=
  norm_R : M → ℝ≥0
  rel_R : M → M → Prop := fun x y ↦ norm_R (x - y) ≤ ρ
  equiv : M ≃ aliasR M ρ := Equiv.refl _

instance (M M' : Type*) (ρ ρ' : ℝ≥0) [AddCommGroup M] [AddCommGroup M'] [AsAliasR M ρ]
  [AsAliasR M' ρ']: AsAliasR (M × M') (max ρ ρ') where
  norm_R := fun ⟨m₁, m₁'⟩ ↦ max (AsAliasR.norm_R ρ m₁) (AsAliasR.norm_R ρ' m₁')

instance (M : Type*) (ρ : ℝ≥0) [AddCommGroup M] : AddCommGroup (aliasR M ρ) :=
  inferInstanceAs (AddCommGroup M)

-- The `ModuleWithRel` instance on every `aliasR`.
@[nolint unusedArguments]
instance (M : Type*) (ρ : ℝ≥0) [AddCommGroup M] [AsAliasR M ρ] : ModuleWithRel (aliasR M ρ) where
  rel := @AsAliasR.rel_R M ρ _ _

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, ∀ ρ : ℝ≥0, [AddCommGroup M] → [AsAliasR M ρ] →
    ∀ m : aliasR M ρ, p (rel m))
    (M : Type) (ρ : ℝ≥0) [AddCommGroup M] [AsAliasR M ρ] (v : aliasR (M × M) ρ) :
      p (rel (max_self ρ ▸ v)) := by
  specialize hp (M × M) (max ρ ρ) v
  convert hp
  simp only [eq_rec_constant]

-- ## Exercise 3
attribute [- instance] PSM_Nat
/- Prove the following claims, stated in the section about the non-discrete metric on `ℕ`:
1. The uniformity is discrete if the metric is discrete.
2. As uniformities, `𝒫 (idRel) = ⊥`.
3. Is the equality `𝒫 (idRel) = ⊥` true as filters?
**ANSWER** NO
4. For any `α`, the discrete topology is the bottom element `⊥` of the type `TopologicalSpace α`.
**ANSWER** instance : CompleteLattice (TopologicalSpace α) := (gciGenerateFrom α).liftCompleteLattice
-/
open Metric Filter Classical

example (X : Type*) [MetricSpace X] (hdisc : ∀ x y : X, x ≠ y → dist x y = 1) :
    PseudoMetricSpace.toUniformSpace = (⊥ : UniformSpace X) := by
    -- (uniformity X) = Filter.principal (idRel : Set (X × X)) := by
  convert Metric.uniformSpace_eq_bot.mpr ?_
  -- · exact StrictMono.apply_eq_bot_iff fun _ _ a ↦ a
  use 1
  simp only [zero_lt_one, true_and]
  intro i j h
  exact ge_of_eq <| hdisc i j h

example (X : Type*) : (⊥ : UniformSpace X).uniformity = 𝓟 (idRel) := rfl


end Exercises
