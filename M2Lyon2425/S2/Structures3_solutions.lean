import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Data.Complex.Exponential

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

def PSM_Nat : PseudoMetricSpace ℕ where
  dist := fun n m ↦ |2 ^ (- n : ℤ) - 2 ^ (- m : ℤ)|
  dist_self := by simp only [zpow_neg, zpow_natCast, sub_self, abs_zero, implies_true]
  dist_comm := fun _ _ ↦ abs_sub_comm ..
  dist_triangle := fun _ _ _ ↦ abs_sub_le _ _ _

attribute [instance] PSM_Nat

-- local instance : PseudoMetricSpace ℕ where
--   dist := fun n m ↦ |2 ^ (- n : ℤ) - 2 ^ (- m : ℤ)|
--   dist_self := by simp only [zpow_neg, zpow_natCast, sub_self, abs_zero, implies_true]
--   dist_comm := fun _ _ ↦ abs_sub_comm ..
--   dist_triangle := fun _ _ _ ↦ abs_sub_le _ _ _

#synth UniformSpace ℕ -- PseudoMetricSpace.toUniformSpace

/- Now suppose that we prove a statement about `ℕ` endowed with this uniformity induced from
the metric. Can we access it at a later stage outside this section? -/

/-! This is actually true! See
-- `Counterexamples/DiscreteTopologyNonDiscreteUniformity.lean`-/
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

def DefSucc (a : ℤ) := a + 1 --as in mathlib
abbrev AbbSucc (a : ℤ) := a + 1 --

example (a : ℤ) : DefSucc (DefSucc a) = a + 2 := by simp only [add_assoc, Int.reduceAdd]

example (a : ℤ) : AbbSucc (AbbSucc a) = a + 2 := by simp only [add_assoc, Int.reduceAdd]

-- `⌘`
private
abbrev 𝓡 := ℝ --type 𝓡 with \MCR
#synth TopologicalSpace 𝓡

-- attribute [-instance] UniformSpace.toTopologicalSpace
-- #synth TopologicalSpace ℝ

instance TopSpace𝓡 : TopologicalSpace 𝓡 := ⊥
-- attribute [-instance] TopSpace𝓡
#synth TopologicalSpace 𝓡
#synth TopologicalSpace ℝ

example : Continuous (fun x : ℝ ↦ if x < 0 then (0 : ℝ) else 1) := by
  apply continuous_bot

def ℛ := ℝ --type ℛ with \McR

-- #synth TopologicalSpace ℛ
-- #synth Field ℝ

instance : TopologicalSpace ℛ := ⊥

-- instance : Field ℛ := inferInstance--inferInstanceAs (Field ℝ)
instance : Field ℛ := inferInstanceAs (Field ℝ)

#synth CommRing ℛ
#synth CommRing 𝓡

instance : LT ℛ := inferInstanceAs <| LT ℝ

lemma ContJump : Continuous (fun x : ℛ ↦ if x < 0 then (0 : ℛ) else 1) := by
  apply continuous_bot

-- lemma ContJump' : Continuous (fun x : 𝓡 ↦ if x < 0 then (0 : 𝓡) else 1) := by
--   apply continuous_bot

example : Continuous (fun x : ℛ × ℛ ↦ if x.1 < 0 then (0 : ℛ) else 1) := by
  exact ContJump.comp continuous_fst

end Synonyms


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

structure Mess (α β γ : Type) [Zero α] [TopologicalSpace β] [UniformSpace γ] :=--where or := are intercheangeable
  a : α := 0
  f : α → β → γ → γ
  cont : Continuous (f a)

#print Mess

-- `⌘`


-- ## Constructing terms
attribute [-instance] TopSpace𝓡

example : TwoNat := sorry --farlo con `:=`, poi aggiungere _, lampadina, etc...

open Real

-- What happens if we have a default value? **Comment
def x1 : Mess ℕ ℝ ℝ where
  f := fun n x y ↦ n + x + y
  cont := by
    simp only [CharP.cast_eq_zero, zero_add]
    apply continuous_pi
    exact fun i ↦ continuous_add_right i

def x2 : Mess ℕ ℝ ℝ where
  a := 37
  f := fun n x y ↦ n + x + y
  cont := by
    apply continuous_pi
    intro i
    apply Continuous.add
    · apply continuous_add_left
    · apply continuous_const


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
  /-try to remove `with` (remember that `x := {x.fst, x.snd}`, `y = {y.left, y.right}`
  and `Mix.mk` takes a `fst : ℕ` and `right : ℕ`: se we need to throw away `x.snd` and `y.left`-/

-- the order does not really matter, it "destructs and reconstructs".
def mix2 (x : TwoNat) (y : Couple) : Mix :=
  {y, x with}

def mix1' (x : TwoNat) (y : Couple) : Mix := {x, y with}
  -- __ := x
  -- __ := y

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

example : f₁ = f₂ := rfl

example : OneNat := {fst := f₁.a}

example : ℕ → ℕ → ℕ := f₁.f f₁.a


-- ## Extends

structure TwoNatExt extends OneNat where
  snd : ℕ

structure OneNatOneInt where
  fst : ℕ
  snd : ℕ

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



-- `⌘`

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
/- example : three₁ = three₁' := rfl -- (they're even different, not simply not `defeq`..._
 indeed, `three₁={fst = 17, snd = 2, right = 11}` while `three₁'={fst = 1, snd = 2, right = 11}`-/


def M₂ : Mix := {fst := 13, right := 11}
def three₂' : ThreeNatExt := {two, M₂ with}
example : three₂'.fst = 1 := rfl
example : three₁' = three₂' := rfl -- one uses `M₁`, and the other uses `M₂`.
/- both are `{fst = 1, snd = 2, right = 11}` (the field `left` has been discharged) . -/

structure TwoNatExtLeft extends TwoNat where
  left : ℕ

example (x : ThreeNat) (y : Couple) : TwoNatExtLeft := {x, y with}


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
