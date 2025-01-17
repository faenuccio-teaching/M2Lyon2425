import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Cauchy
-- import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Topology.UniformSpace.Basic

noncomputable section LocalInstances

#print UniformSpace
-- One constructor and four fields

#synth UniformSpace ℕ -- instUniformSpaceNat

example : instUniformSpaceNat = ⊥ := rfl

open scoped Filter Uniformity

example : (uniformity ℕ) = (𝓟 idRel) := rfl -- this is the "trivial" or "discrete" uniformity.

attribute [- instance] instUniformSpaceNat --this is local, it only applies to the current section

-- #synth UniformSpace ℕ -- failed to synthesize

local instance : PseudoMetricSpace ℕ where
  dist := fun n m ↦ |2 ^ (- n : ℤ) - 2 ^ (- m : ℤ)|
  dist_self := by simp only [zpow_neg, zpow_natCast, sub_self, abs_zero, implies_true]
  dist_comm := fun _ _ ↦ abs_sub_comm ..
  dist_triangle := fun _ _ _ ↦ abs_sub_le .. -- do you know these two dots?


#synth UniformSpace ℕ -- PseudoMetricSpace.toUniformSpace

/- Now suppose that we prove a statement about `ℕ`endowed with this uniformity induced from
the metric. Can we access it at a later stage outside this section? -/

/-! This is actually true! See
-- `Counterexamples/DiscreteTopologyNonDiscreteUniformity.lean`-/
lemma idIsCauchy : CauchySeq (id : ℕ → ℕ) := by sorry


example : CauchySeq (id : ℕ → ℕ) := idIsCauchy

end LocalInstances

section Structures


-- `⌘`


structure OneNat where
  fst : ℕ

structure TwoNat where
  pair ::
  fst : ℕ
  snd : ℕ

whatsnew in
@[ext]
structure Couple where
  left : Nat
  right : Nat

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
  f : α → β → γ
  cont : Continuous (f a)

-- `⌘`



-- ## Constructing terms

-- `⌘`

example : TwoNat := sorry --farlo con `:=`, poi aggiungere _, lampadina, etc...

-- What happens if we have a default value?
example : Mess ℕ ℝ ℝ := sorry


example (x : TwoNat) : Couple where
  left := x.fst
  right := x.snd

-- Same construction, different syntax
example (x : TwoNat) : Couple := {left := x.fst, right := x.snd}


/- The syntax `with` instructs Lean to take all possible labels from that term and to only ask
for the remaining-/

-- This forgets the label and takes it back.
example (x : OneNat) : TwoNat :=
  {x with snd := x.1}


example (x : OneNat) : Couple := sorry
  -- {x with left := x.1} fields missing: 'right'
--so, it does not "populate missing fields with the first available type-correct term: labels matter"

example (x : OneNat) : Couple :=
  {left := x.1, right := x.1}

example (x : TwoNat) : OneNat := {x with} --without the `with` the extra-field is not thrown away

structure Mix where
  fst : Nat
  right : Nat

#check Mix.mk
/- It is also able to throw away useless ones. -/
def mix1 (x : TwoNat) (y : Couple) : Mix :=
  {x, y with}
  /-try to remove `with` (remember that `x := {x.fst, x.snd}`, `y = {y.left, y.right}`
  and `Mix.mk` takes a `fst : ℕ` and `right : ℕ`: se we need to throw away `x.snd` and `y.left`-/

def mix2 (x : TwoNat) (y : Couple) : Mix :=
  {y, x with}

example (x : TwoNat) : Couple := x

-- ## Extends

structure TwoNatExt extends OneNat where
  snd : Nat


structure OneNatOneInt where
  fst : Nat
  snd : Int

structure Blob extends OneNatOneInt, OneNat
structure Blob' extends OneNatOneInt, TwoNat


def mix3 (x : TwoNatExt) (y : Couple) : Mix :=
  {x, y with}



def TwoToExt : TwoNat → TwoNatExt := fun x ↦ {x with}

example (x : TwoNat) (y : Couple) : mix1 x y = mix2 x y := rfl

example (x : TwoNat) (y : Couple) : mix1 x y = mix3 (TwoToExt x) y := rfl

/- Under the hood, Lean destructs all these terms and reconstructs them "in the right order" --- but
keeping labels. -/

def TwoExtToCouple : TwoNatExt → Couple := by --fun x ↦ {left := x.1, right := x.2} -- error! why?
  rintro ⟨x, y⟩ -- by def, `TwoNatExt` extends `OneNat`, so `x : OneNat`. So,
  exact {left := x.1, right := y}

def OtherToCouple : TwoNat → Couple := fun x ↦ {left := x.1, right := x.2}

/- Yet... **CHECK AGAIN! & DRAW A DIAGRAM**-/
example (x : TwoNat) : TwoExtToCouple (TwoToExt x) = OtherToCouple x := rfl

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

/- And if there are duplicates? -/
structure ThreeNatExt extends TwoNat, Mix

#print ThreeNatExt -- it seems that `fst` will come from the `toTwoNat` field, not from `Mix`: yet

def two : TwoNat := {fst := 1, snd := 2}
def mix₁ : Mix := {fst := 17, right := 11}
def mix₂ : Mix := {fst := 13, right := 11}

def three₁ : ThreeNatExt := {mix₁, two with}
def three₁' : ThreeNatExt := {two, mix₁ with}
def three₂ : ThreeNatExt := {mix₂, two with}
def three₂' : ThreeNatExt := {two, mix₂ with}

example : three₁.fst = 17 := by rfl
example : three₁'.fst = 1 := by rfl
/- So in reality Lean is first using the first variable (`mix` or `two`), possibly throwing away
useless stuff **ADD AN EXAMPLE OF A STRUCTURE WITH SPURIOUS CONSTRUCTORS, LIKE MIX**, and then using
what follows to complete them -/

-- example : three₁ = three₁' := rfl
/- indeed, `three₁={fst = 17, snd = 2, right = 11}` while `three₁'={fst = 1, snd = 2, right = 11}`-/
example : three₁' = three₂' := rfl
/- both are `{fst = 1, snd = 2, right = 11}` (the field `left` has been discharged) . -/

/- ## As classes
This `extends` has a special behaviour when we're upgrading `structures` to `classes`. Suppose
that we make `OneNat`, `TwoNat` and `OtherTwo` classes: how can we produce instances for them?
-/

attribute [class] OneNat
attribute [class] TwoNat
attribute [class] TwoNatExt

instance (n : ℕ) : OneNat := ⟨n⟩
-- instance (n m : ℕ) : TwoNat := ⟨n, m⟩--does not work, it extends!
instance (n m : ℕ) : TwoNatExt := ⟨⟨n⟩, m⟩--ok
instance (n m : ℕ) : TwoNat := ⟨n, m⟩ --yes

/- And `extends` interacts with instances even more if we have variables!-/

class GeTwo (X : Type*) where
  x : X
  y : X
  ne : x ≠ y

class GeThree (X : Type*) [GeTwo X] where
  z : X
  nex : z ≠ GeTwo.x
  ney : z ≠ GeTwo.y

class GeThree' (X : Type*) extends GeTwo X where
  z : X
  nex : z ≠ x
  ney : z ≠ y

instance : GeTwo ℕ := ⟨1, 2, by omega⟩
-- instance : GeTwo Bool := ⟨true, false, by simp⟩

-- instance : GeThree ℤ := ⟨3, by omega, by omega⟩--unhappy
-- instance : GeThree ℕ := ⟨3, by linarith [show GeTwo.x = 1 by rfl],
--   by linarith [show GeTwo.y = 2 by rfl]⟩

instance : GeThree' ℕ where
-- three more fields where proposed,but are useless
  z := 3
  nex := by linarith [show GeTwo.x = 1 by rfl]
  ney := by linarith [show GeTwo.y = 2 by rfl]

instance : GeThree' ℤ where
  x := 1
  y := 2
  ne := by simp
  z := 3
  nex := by
    -- have : GeTwo.x = 1 := by
       --still does not work, it uses the coercion from `ℕ` to `ℤ`: with `(1 : ℤ)` it fails.
    sorry
  ney := sorry


/- ### In True Math
Remember the piece of code-/

-- We can now go back to what we saw last week: remember that we defined
class AddMonoidBad (M : Type) extends Add M, AddZeroClass M

instance : AddMonoidBad ℕ where --{Nat.instAddMonoid with}
  __ := Nat.instAddMonoid -- the double line means "pick all fields that you can from this term: it is
  -- the where-version of the behaviour of `with`, "
  -- add := _
  -- zero := _
  -- zero_add := _
  -- add_zero := _
  -- __ := Nat.instAddMonoid-- {__ := @AddZeroClass }--{zero_add := Nat.zero_add, add_zero := by simp}
-- instance : AddMonoidBad ℕ := { __ := Nat.instAddMonoid}
/-Why do we need to add these fields? -/
#synth AddZeroClass ℕ
#check @zero_add ℕ


end Structures
