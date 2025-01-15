import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Basic


open Classical

noncomputable section

/- ## Sections:
1. FunnyBracket
2. Extends -- In Structures3
3. ForgetfulInheritance -- In Structures2
4. LocalInstances
5. Synonyms
6. OutParam
-/

section FunnyBracket

/- Some examples of the interest of ⦃

-/

end FunnyBracket
section Extends

/- The usual way to define a `structure` is to write its name, then `where` and then the list of
fields (remember, there is a unique constructor by definition of `structure`!). -/

/- `OneNat` is the structure with just one number. -/
structure OneNat where
  fst : Nat

/- `TwoNat` is the structure whose terms are pairs of naturals... -/
structure TwoNat extends OneNat where
  snd : Nat

structure OtherTwo where
  fst : Nat
  snd : Nat

structure Couple where
  left : Nat
  right : Nat

/- The big difference between `TwoNat`, `OtherTwo` and `Couple` are the names of the fields. These
name **are relevant**! You might think of a term of type `TwoNat` as a pair of *labelled* naturals,
and that a structure is a collection of labelled terms. So: -/

example (x : OneNat) : TwoNat :=
  {fst := x.1, snd := x.1}
-- This forgets the label and takes it back.

example (x : OneNat) : TwoNat :=
  {x with snd := x.1}

example (x : OneNat) : Couple := sorry
  -- {x with left := x.1} fields missing: 'right'

example (x : OneNat) : Couple :=
  {left := x.1, right := x.1}

/- So, the keyword `with` instructs Lean to take all possible labels from that term and to only ask
for the remaining, throwing away useless ones. -/

structure Mix where
  fst : Nat
  right : Nat

def mix1 (x : TwoNat) (y : Couple) : Mix :=
  {x, y with}

def mix2 (x : TwoNat) (y : Couple) : Mix :=
  {y, x with}

def mix3 (x : OtherTwo) (y : Couple) : Mix :=
  {x, y with}

def TwoToOther : TwoNat → OtherTwo := fun x ↦ {x with}

example (x : TwoNat) (y : Couple) : mix1 x y = mix2 x y := rfl

example (x : TwoNat) (y : Couple) : mix1 x y = mix3 (TwoToOther x) y := rfl

/- Under the hood, Lean destructs all these terms and reconstructs them "in the right order". But
keeping labels! -/

def TwoToCouple : TwoNat → Couple := by --fun x ↦ {left := x.1, right := x.2} -- error! why?
  rintro ⟨x, y⟩ -- by def, `TwoNat` extends `OneNat`, so `x : OneNat`. So,
  exact {left := x.1, right := y}

def OtherToCouple : OtherTwo → Couple := fun x ↦ {left := x.1, right := x.2}

/- Yet... -/
example (x : TwoNat) : TwoToCouple x = OtherToCouple (TwoToOther x) := rfl


/- And if there are duplicates? -/
structure ThreeNat extends TwoNat, Mix

#print ThreeNat -- it seems that `fst` will come from the `toTwoNat` field, not from `Mix`: yet

def two : TwoNat := {fst := 1, snd := 2}
def mix₁ : Mix := {fst := 17, right := 11}
def mix₂ : Mix := {fst := 13, right := 11}

def three₁ : ThreeNat := {mix₁, two with}
def three₁' : ThreeNat := {two, mix₁ with}
def three₂ : ThreeNat := {mix₂, two with}
def three₂' : ThreeNat := {two, mix₂ with}

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
attribute [class] OtherTwo

instance (n : ℕ) : OneNat := ⟨n⟩
-- instance (n m : ℕ) : TwoNat := ⟨n, m⟩--does not work, it extends!
instance (n m : ℕ) : TwoNat := ⟨⟨n⟩, m⟩--ok
instance (n m : ℕ) : OtherTwo := ⟨n, m⟩ --yes

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
class AddMonoid_bad (M : Type) extends AddSemigroup M, AddZeroClass M

@[simp]
instance : AddMonoid_bad ℕ := {zero_add := Nat.zero_add, add_zero := by simp}

/-Why do we need to add these fields? Let's see...-/


end Extends

--added to Structures2
section ForgetfulInheritance

class NormedModule_long (M : Type*) [AddCommGroup M] where
  norm : M → ℝ

class NormedModule₁ (M : Type*) extends AddCommGroup M where
  norm₁ : M → ℝ

#print NormedModule_long
#print NormedModule₁

export NormedModule₁ (norm₁)

notation "‖" e "‖₁" => norm₁ e

class ModuleWithRel (M : Type*) extends AddCommGroup M where
  rel : M → M → Prop

export ModuleWithRel (rel)

instance (M N : Type*) [NormedModule₁ M] [NormedModule₁ N] : NormedModule₁ (M × N) where
      norm₁ := fun ⟨m, n⟩ ↦ max ‖m‖₁ ‖n‖₁

instance (M N : Type*) [ModuleWithRel M] [ModuleWithRel N] : ModuleWithRel (M × N) where
      rel := fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)

instance (M : Type*) [NormedModule₁ M] : ModuleWithRel M where
      rel := fun m n ↦ ‖m - n‖₁ ≤ 1

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, [NormedModule₁ M] → ∀ m : M, p (rel m))
    (M : Type) [NormedModule₁ M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  -- exact hp
  sorry

/- Let's try again! The problem is that passing from `NormedModule₁` to `ModuleWithRel`
is not a pure "erasure", because we are not simply throwing away a field, but using some
field in the first to construct the term of the second: this yields to the problem we have
just witnessed, and the slogan is that only "forgetful inheritance" is allowed (an idea initially
proposed by Affeldt, Cohen, Kerjean, Mahboubi, Rouhling and Sakaguchi in
https://inria.hal.science/hal-02463336v2 , from which this example is extracted.) -/

-- whatsnew in (see the last one)
class NormedModule (M : Type*) extends ModuleWithRel M where
  norm : M → ℝ


variable (X : Type*) [NormedModule X]
#synth ModuleWithRel X

instance (M : Type*) [NormedModule M] : ModuleWithRel M := inferInstance

#print NormedModule
#print NormedModule₁

export NormedModule (norm)

notation "‖" e "‖" => norm e

instance (M N : Type*) [NormedModule M] [NormedModule N] : NormedModule (M × N) where
  rel := fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)
  norm := fun ⟨m, n⟩ ↦ max ‖m‖ ‖n‖

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, [NormedModule M] → ∀ m : M, p (rel m))
    (M : Type) [NormedModule M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  exact hp

end ForgetfulInheritance

section LocalInstances

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

-- example : CauchySeq (id : ℕ → ℕ) := idIsCauchy

section Synonyms


/-Another strategy that works more globally: use type synonyms. The idea is to create a copy of a
type, that comes with no instance at all. -/

def ℛ := ℝ --type ℛ with \McR
abbrev 𝓡 := ℝ --type 𝓡 with \MCR
def 𝒩 := ℕ --type 𝓡 with 𝒩 \McR


#synth TopologicalSpace ℝ
#synth TopologicalSpace 𝓡
-- #synth TopologicalSpace 𝒩
-- #synth TopologicalSpace ℛ
#synth Field ℝ

instance : TopologicalSpace ℛ := ⊥

instance : Field ℛ := inferInstanceAs (Field ℝ)
-- instance : Field 𝒩 := inferInstanceAs (Field ℝ)

#synth CommRing ℛ

instance : LT ℛ := inferInstanceAs <| LT ℝ

lemma ContJump : Continuous (fun x : ℛ ↦ if x < 0 then 0 else 1) := by
  apply continuous_bot

end Synonyms

lemma ContJump' : Continuous (fun x : ℛ ↦ if x < 0 then 0 else 1) := by
  apply continuous_bot

lemma NotContJump : Continuous (fun x : ℝ ↦ if x < 0 then 0 else 1) := by
  sorry


section OutParam

class ExtMul₁ (γ δ W : Type*) where
  xmul₁ : γ → δ → W

export ExtMul₁ (xmul₁)

infixr:70 "⋄" => xmul₁

variable {α β X Y Z: Type*} [ExtMul₁ β X Y] [ExtMul₁ α Y Z]

-- example (a : α) (b : β) (x : X) (z : Z) : a ⋄ (b ⋄ x) = z := sorry

-- Let's try to do better
class ExtMul (γ : Type*) (δ : semiOutParam (Type*)) (W  : outParam (Type*)) where
  xmul : γ → δ → W

export ExtMul (xmul)

infixr:70 "⬝" => xmul

variable [ExtMul β X Y] [ExtMul α Y Z]

example (a : α) (b : β) (x : X) (z : Z) : a ⬝ (b ⬝ x) = z := by
  sorry
/-What is going on is that for `ExtMul₁` Lean needs to know the landing type when trying class
inference, whereas for `ExtMul` it can replace it with a metavariable and hope that later on
thigs get ok.

Concerning `ExtMul₁`, it first evaluates `a ⋄ b` and needs a `ExtMul₁` instance so it creates
a metavariable `?v1` and hopes to find a `ExtMul₁ β ?v1 Z` instance (this is exactly the error
message). On the other hand, `ExtMul` arrives at `ExtMul β ?v1 Z` and then it evaluates
`(b ⬝ x)` (supposed of type `?v1`): since it finds a `ExtMul β X Y` instance, it tries replacing
`?v1` with `Y` and backtracks to see if it finds a `ExtMul α Y X` instance, which it does, so
everybody is happy. -/

/- This can still occasionally create problems: indeed, by design, when an `outParam` is around it
can only take one value (via `instances`), so the following does create problems: -/


instance : ExtMul ℝ ℝ ℕ := ⟨fun _ _ ↦ 0⟩
instance : ExtMul ℝ ℝ Prop := ⟨fun _ _ ↦ False⟩

example (x y : ℝ) : x ⬝ y = 0 := rfl
-- example (x y : ℝ) : x ⬝ y = False := rfl-- but removing the first instance makes this type-check


end OutParam
