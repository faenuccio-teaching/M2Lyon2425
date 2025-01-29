import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Topology.MetricSpace.Basic

-- import Mathlib.Data.NNReal.Basic


noncomputable section

open Classical

section LocalInstances

open scoped Filter Uniformity

#print UniformSpace
-- One constructor and five fields

#print instUniformSpaceNat

example : instUniformSpaceNat = ⊥ := rfl

example : (uniformity ℕ) = (𝓟 idRel) := rfl

#synth UniformSpace ℕ -- instUniformSpaceNat
attribute [- instance] instUniformSpaceNat --this is local, it only applies to the current section

--#synth UniformSpace ℕ -- failed to synthesize

def PSM_Nat : PseudoMetricSpace ℕ where
  dist := fun n m ↦ |2 ^ (-n : ℤ) - 2 ^ (-m : ℤ)|
  dist_self := by simp only [zpow_neg, zpow_natCast, sub_self, abs_zero, implies_true]
  dist_comm := fun _ _ ↦ abs_sub_comm ..
  dist_triangle := fun _ _ _ ↦ abs_sub_le ..

attribute [instance] PSM_Nat

-- local instance : PseudoMetricSpace ℕ where
--   dist := fun n m ↦ |2 ^ (-n : ℤ) - 2 ^ (-m : ℤ)|
--   dist_self := by simp only [zpow_neg, zpow_natCast, sub_self, abs_zero, implies_true]
--   dist_comm := fun _ _ ↦ abs_sub_comm ..
--   dist_triangle := fun _ _ _ ↦ abs_sub_le ..

#synth UniformSpace ℕ

/-! This is actually true! See `Counterexamples/DiscreteTopologyNonDiscreteUniformity.lean`-/
lemma idIsCauchy : CauchySeq (id : ℕ → ℕ) := by
  simp only [CauchySeq, Filter.map_id, Cauchy]

  sorry

example : CauchySeq (id : ℕ → ℕ) := idIsCauchy
example : CauchySeq (id : ℕ → ℕ) := idIsCauchy

end LocalInstances

-- This does not work, since we have quit the `LocalInstance` section
example : CauchySeq (id : ℕ → ℕ) := idIsCauchy


-- `⌘`


noncomputable section Synonyms
namespace bleah
scoped notation "𝔸" => ℕ

def NiceNumber : ℕ := 37

#check NiceNumber

#check (37 : 𝔸)
end bleah

-- open bleah
#print NiceNumber

#check (37 : 𝔸)

notation "𝒩" => ℕ
#check (37 : 𝒩)

abbrev AbbNat := ℕ
#check (37 : AbbNat)

def DefNat := ℕ
#check (Nat.zero : DefNat)
#check (Nat.succ : DefNat → ℕ)

def DefSucc (a : ℤ) := a + 1 --definition as in Mathlib
abbrev AbbSucc (a : ℤ) := a + 1 --

example (a : ℤ) : DefSucc (DefSucc a) = a + 2 := by
  unfold DefSucc
  simp only [add_assoc, Int.reduceAdd]

example (a : ℤ) : AbbSucc (AbbSucc a) = a + 2 := by simp only [add_assoc, Int.reduceAdd]


-- `⌘`


abbrev 𝓡 := ℝ --type 𝓡 with \MCR
#synth TopologicalSpace 𝓡

attribute [-instance] UniformSpace.toTopologicalSpace
--#synth TopologicalSpace ℝ

instance TopSpace𝓡 : TopologicalSpace 𝓡 := ⊥
#synth TopologicalSpace 𝓡
#synth TopologicalSpace ℝ

example : Continuous (fun x : ℝ ↦ if x < 0 then (0 : ℝ) else 1) := by
  apply continuous_bot
/-`continuous_bot` is the statement saying that every function leaving from a discrete space
is automatically continuous. -/


def ℛ := ℝ --type ℛ with \McR

--#synth TopologicalSpace ℛ --(fails)
--#synth Field ℛ --(fails)

instance : TopologicalSpace ℛ := ⊥

instance : Field ℛ := inferInstanceAs (Field ℝ)
instance : Field ℛ := inferInstanceAs (Field ℝ)

#synth CommRing ℛ
#synth CommRing 𝓡

instance : LT ℛ := inferInstanceAs <| LT ℝ

lemma ContJump : Continuous (fun x : ℛ ↦ if x < 0 then (0 : ℛ) else 1) := by
  apply continuous_bot

lemma ContJump' : Continuous (fun x : 𝓡 ↦ if x < 0 then (0 : 𝓡) else 1) := by
  apply continuous_bot

-- This might be a problem!
lemma ContJump'' : Continuous (fun x : ℝ ↦ if x < 0 then (0 : ℝ) else 1) := by
  apply continuous_bot

end Synonyms


-- This might be a problem!
lemma ContJump''' : Continuous (fun x : ℝ ↦ if x < 0 then (0 : ℝ) else 1) := by
  apply continuous_bot

-- Even leaving the `Synonyms` section, the following still works.
example : Continuous (fun x : ℛ × ℛ ↦ if x.1 < 0 then (0 : ℛ) else 1) := by
  apply ContJump.comp
  apply continuous_fst


-- `⌘`


section Structures


structure OneNat :=
  fst : ℕ

structure TwoNat where
  pair ::
  fst : ℕ
  snd : ℕ

#print TwoNat

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
--#check TwoNat.mk
#check TwoNat.pair
#check OrderedPairs.mk
--#check order
#check OrderedPairs.order


structure TwoTerms (α : Type) where
  fst : α
  snd : α

structure Mess (α β γ : Type) [Zero α] [TopologicalSpace β] [UniformSpace γ] where--:=--`where` or `:=`
  a : α := 0
  f : α → β → γ → γ
  cont : Continuous (f a)

#print Mess


-- `⌘`


attribute [-instance] TopSpace𝓡
-- ## Constructing terms

example : TwoNat where
  fst := 2
  snd := 76

open Real

-- What happens if we have a default value?
def x1 : Mess ℕ ℝ ℝ := ⟨37, fun _ _ _ ↦ 0, by continuity⟩

def x2 : Mess ℕ ℕ ℕ := ⟨37, fun _ _ _ ↦ 0, continuous_bot⟩

example (x : TwoNat) : Couple where
  left := x.fst
  right := x.snd

-- Same construction, different syntax
example (x : TwoNat) : Couple := {left := x.fst, right := x.snd}

example (x : TwoNat) : Couple := ⟨x.fst, x.snd⟩

example (x : OneNat) : Couple :=
  sorry


-- `⌘`


-- This forgets the label and takes it back.
example (x : OneNat) : TwoNat := sorry

-- another syntax
example (x : OneNat) : TwoNat := sorry

example (x : TwoNat) : OneNat := sorry

example (x : TwoNat) : OneNat := sorry


example (x : TwoNat) : Couple := sorry

example (x : OneNat) : Couple := sorry

example (x : OneNat) : ℕ := sorry

structure Mix where
  fst : ℕ
  right : ℕ

#check Mix.mk

def mix1 (x : TwoNat) (y : Couple) : Mix := sorry
/- remember that `x := {x.fst, x.snd}`, `y = {y.left, y.right}`
  and `Mix.mk` takes a `fst : ℕ` and `right : ℕ`: se we need to throw away `x.snd` and `y.left`-/

def mix1' (x : TwoNat) (y : Couple) : Mix := sorry

-- the order does not really matter, it "destructs and reconstructs".
def mix2 (x : TwoNat) (y : Couple) : Mix := sorry


example : mix1 = mix1' := sorry

example : mix1 = mix2 := sorry


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
example (x : Mix) (y : Mix') (z : ThreeNat) : Mix₃ := sorry

-- A final example with a `Prop`-valued field:

def f₁ : Mess ℕ ℕ ℕ := sorry

def f₂ : Mess ℕ ℕ ℕ := sorry

-- `Prop`-valued fields disappear by proof irrelevance
example : f₁ = f₂ := sorry


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

def TwoExtToCouple : TwoNatExt → Couple := by sorry

def TwoNatToCouple : TwoNat → Couple :=  sorry

/- And if there are duplicates? Remember that
  `structure Mix where`
      `fst : ℕ`
      `right : ℕ`     -/

structure ThreeNatExt extends TwoNat, Mix

#print ThreeNatExt

/- Overlapping fields are not duplicated; moreover, whenever possible, fields will coincide with
constructors of the parent structure; in case of overlapping fields, things are destructured. -/


def TwoNatToExt : TwoNat → TwoNatExt := sorry

/- `with` is able to
1. Destruct `x` into `x.fst` and get a `OneNat`
2. Out of the `OneNat` reuire another `ℕ` to define a `TwoNatExt`
3. Destruct `x` into `x.snd` and get the missing field. -/

example (x : TwoNat) : TwoNatToExt x = ⟨⟨x.fst⟩, x.snd⟩ := sorry


/- Remember
    `mix1 (x : TwoNat) (y : Couple) : Mix := {x, y with}` and
    `mix2 (x : TwoNat) (y : Couple) : Mix := {y, x with}` -/

def mix3 (x : TwoNatExt) (y : Couple) : Mix := sorry

example (x : TwoNat) (y : Couple) : mix1 x y = mix3 (TwoNatToExt x) y := sorry


/- Remember that `ThreeNatExt extends TwoNat, Mix` and
  `structure Mix where`
        `fst : ℕ`
        `right : ℕ`     -/

def M₁ : Mix := {fst := 17, right := 11}
def two : TwoNat := {fst := 1, snd := 2}

def three₁ : ThreeNatExt := {M₁, two with}
def three₁' : ThreeNatExt := {two, M₁ with}

example : three₁.fst = 17 := by sorry
example : three₁'.fst = 1 := by sorry

/- So in reality Lean is first using the first variable (`M` or `two`), possibly throwing away
useless stuff, and then using what follows to complete them -/

example : three₁ = three₁' := sorry


def M₂ : Mix := {fst := 13, right := 11}
def three₂' : ThreeNatExt := {two, M₂ with}

example : three₂'.fst = 1 := sorry
example : three₁' = three₂' := sorry

structure TwoNatExtLeft extends TwoNat where
  left : ℕ

example (x : ThreeNat) (y : Couple) : TwoNatExtLeft := sorry


-- `⌘`


/- ### In True Math
Remember the piece of code-/

-- We can now go back to what we saw last week: remember that we defined
class AddMonoidBad (M : Type) extends Add M, AddZeroClass M

instance : AddMonoidBad ℕ := sorry

instance : AddMonoidBad ℕ := ⟨Nat.zero_add, Nat.add_zero⟩
-- instance : AddMonoidBad ℕ := ⟨Nat.add_zero, Nat.zero_add⟩ -- order matters!

instance : AddMonoidBad ℕ := sorry

instance : AddMonoidBad ℕ := sorry

end Structures

section Exercises
attribute [-instance] TopSpace𝓡

/- ## Exercise 1
Define the class of metric spaces (but call them `SpaceWithMetric` to avoid conflict with the
existing library) as defined in https://en.wikipedia.org/wiki/Metric_space#Definition, and deduce
an instance of `TopologicalSpace` on every `SpaceWithMetric`.

Explain why this is the *wrong* choice, on an explicit example, and fix this.
-/


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

instance (M : Type) [AddCommGroup M] [NormedModuleBad M] (ρ : ℝ := 1) : ModuleWithRel M where
  rel a b := ‖ a - b ‖₀ ≤ ρ



/- ## Exercise 3
Prove the following claims, stated in the section about the non-discrete metric on `ℕ`:
1. `PseudoMetricSpace.uniformity_dist = 𝒫 (idRel)` if the metric is discrete.
2. As uniformities, `𝒫 (idRel) = ⊥`.
3. Is the equality `𝒫 (idRel) = ⊥` true as filters?
4. For any `α`, the discrete topology is the bottom element `⊥` of the type `TopologicalSpace α`.
-/



end Exercises
