import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Data.Real.Basic
-- import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Basic

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


variable (X : Type) [NormedModule X]
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

example : (uniformity ℕ) = (𝓟 idRel) := rfl
example : (uniformity ℕ) = ⊥ := by sorry

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

example : CauchySeq (id : ℕ → ℕ) := idIsCauchy

section Aliases

end Aliases
-- example (α : Type*) [UniformSpace α] (h : 𝓤 α = ⊥) : uniformity α = 𝓟 idRel := by
--   rw [h]
--   sorry



-- example : (uniformity ℕ) = ⊥ := by
-- example : (uniformity ℕ) = ⊥ := by
--   convert_to (uniformity ℕ) = (𝓟 idRel)
--   · have := bot_uniformity (α := ℕ)
--     infer_instance


--   · rfl
--   let U : UniformSpace ℕ := by exact instUniformSpaceNat
--   have : U = ⊥ := rfl
--   -- rcases U with ⟨h1, h2, h3, h4⟩
--   -- rcases h1 with ⟨f1, f2, f3, f4⟩
--   let B : Bot (UniformSpace ℕ) := by exact instBotUniformSpace
--   have also : U = B.1 := rfl
--   simp_all
