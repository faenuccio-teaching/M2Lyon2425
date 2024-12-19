import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Data.Real.Basic
-- import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Basic

open Classical

noncomputable section

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

/- Let's try again! The problem is that passing from `NormedModule₁` to `ModuleWithRel₁`
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

variable (α β X Y Z: Type*) [ExtMul₁ β X Y] [ExtMul₁ α Y Z]

example (a : α) (b : β) (x : X) (z : Z) : a ⋄ (b ⋄ x) = z := sorry

class ExtMul (γ δ: Type*) (W : outParam (Type*)) where
  xmul : γ → δ → W

export ExtMul (xmul)

infixr:70 "⬝" => xmul

variable {α β X Y Z: Type*} [ExtMul β X Y] [ExtMul α Y Z]

example (a : α) (b : β) (x : X) (z : Z) : a ⬝ (b ⬝ x) = z := by
  sorry
/-What is going on is that for `ExtMul₁` Lean needs to know the landing type when trying class
inference, whereas for `ExtMul` it can replace it with a metavariable and hope that later on
thigs get ok.

Concerning `ExtMul₁`, it first evaluates `b ⋄ x` and needs a `ExtMul₁` instance so it creates
a metavariable `?v1` and hopes to find a `ExtMul₁ β X ?v1` instance. Then it evaluates `a ⋄ (b ⋄ x)`
and for this it needs an instance `ExtMul₁ α ?v1 Z` which it cannot find (this is exactly the error
message). On the other hand, `ExtMul` arrives at `ExtMul β X ?v1` and when it evaluates
`a ⬝ (b ⬝ x)` it knows that the type of `?v1` needs to be unified with the context: since it finds
a `ExtMul α Y Z` instance, it tries replacing `?v1` with `Y` and backtracks to see if it finds a
`ExtMul β X Y` instance, which it does, so everybody is happy.
-/

/- This can still occasionally create problems.-/
variable (Y' : Type*) [ExtMul α Y' Z] [ha : ExtMul β X Y']
variable [Zero Z]

lemma bar (a : α) (y : Y) : a ⬝ y = 0 := by
  sorry

example (a : α) (b : β) (x : X) : a ⬝ (b ⬝ x) = 0 := by
-- Lean prefers `ExtMul β X Y'` rather than `ExtMul X Y`, so the above lemma does not apply
  have := bar a (b ⬝ x)

end OutParam
