import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

namespace ForgetfulInheritance

-- ## An Example


-- `⌘`

section AnExample

open scoped NNReal

class NormedModuleBad (M : Type*) [AddCommGroup M] where
  norm_b : M → ℝ≥0

class NormedModule_ext (M : Type*) extends AddCommGroup M where
  norm_ext : M → ℝ≥0
/- Of course, this `NomedModule_ext` is preferable, but for inspecting the details of this section,
it is better to keep all fields as explicit as possible. -/

#print NormedModule_ext
#print NormedModuleBad

export NormedModuleBad (norm_b)

notation "‖" e "‖₀" => norm_b e

class ModuleWithRel (M : Type*) [AddCommGroup M] where
  rel : M → M → Prop

export ModuleWithRel (rel)

-- The `ModuleWithRel` instance on every `NormedModuleBad`.
instance (M : Type*) [AddCommGroup M] [NormedModuleBad M] : ModuleWithRel M where
  rel := sorry


-- `⌘`


-- The `NormedModuleBad` instance on a product
instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [NormedModuleBad M] [NormedModuleBad N] :
    NormedModuleBad (M × N) where
  norm_b := fun ⟨m, n⟩ ↦ max ‖m‖₀ ‖n‖₀

-- The `ModuleWithRel` instance on a product
instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [ModuleWithRel M] [ModuleWithRel N] :
    ModuleWithRel (M × N) where
  rel := sorry

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModuleBad M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModuleBad M] (v : M × M) : p (rel v) := by
  sorry


-- `⌘`


class NormedModuleGood (M : Type*) [AddCommGroup M] where
  norm_g : M → ℝ≥0
  rel : M → M → Prop

export NormedModuleGood (norm_g)

notation "‖" e "‖₁" => norm_g e

instance (M : Type*) [AddCommGroup M] [NormedModuleGood M] : ModuleWithRel M :=
  ⟨NormedModuleGood.rel⟩

instance (M N : Type*) [AddCommGroup M] [NormedModuleGood M] [AddCommGroup N] [NormedModuleGood N] :
  NormedModuleGood (M × N) where
  rel := sorry
  norm_g := sorry

-- This would have worked before as well.
example (M : Type) [AddCommGroup M] [NormedModuleGood M] : ModuleWithRel (M × M) := inferInstance

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModuleGood M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModuleGood M] (v : M × M) : p (rel v) := by
  sorry

/- The **same example** can be constructed using the `extend` construction:-/
-- whatsnew in --(see the last non-proteced `def`, whose name ends with `...toModuleWithRel`)
class NormedModuleGood₂ (M : Type*) extends AddCommGroup M, ModuleWithRel M where
  norm₂ : M → ℝ≥0


/- The `ModuleWithRel` instance on a `NormedModule₂` now comes for free, because
`NormedModule` extends `ModuleWithRel`.-/
instance (M : Type) [NormedModuleGood₂ M] : ModuleWithRel M := inferInstance

instance (M N : Type) [NormedModuleGood₂ M] [NormedModuleGood₂ N] : NormedModuleGood₂ (M × N) :=
  sorry

example (hp : ∀ M : Type, [NormedModuleGood₂ M] → ∀ m : M, p (rel m))
    (M : Type) [NormedModuleGood₂ M] (v : M × M) : p (rel v) := by
  sorry

--  We'll see more details about this `extend` construction and its syntax later on.


-- `⌘`

end AnExample

/- ## In Mathlib-/
section InMathlib


-- `⌘`


class AddMonoidBad (M : Type) extends Add M, AddZeroClass M

class HasNatSmul (M : Type) [Zero M] [Add M] where
  smul : ℕ → M → M

-- A recursive definition of `n • x = x + x + ... + x` (`n` times).
@[simp]
def nsmul_rec {M : Type} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul_rec n a


@[simp] -- We can give explicit names to instances if we want to call them later: it's optional.
instance AddMndB_to_NatSmul (M : Type) [AddMonoidBad M] : HasNatSmul M := ⟨nsmul_rec⟩

@[simp]
instance SmulEqMul_on_Nat : HasNatSmul ℕ := ⟨fun n m ↦ n * m⟩

@[simp] -- We'll come back later on and discuss why these two fields are needed.
instance : AddMonoidBad ℕ := {zero_add := Nat.zero_add, add_zero := by simp}

-- We ended up with two multiplication by `ℕ` on `ℕ`
example : HasNatSmul ℕ := AddMndB_to_NatSmul ℕ
example : HasNatSmul ℕ := SmulEqMul_on_Nat

example : AddMndB_to_NatSmul ℕ = SmulEqMul_on_Nat := sorry

-- This induction proof owes a lot to the `@[simp]` in the previous definitions: remove and see...
example {n m : ℕ} : HasNatSmul.smul n m = nsmul_rec n m := by
  sorry


-- `⌘`


class AddMonoidGood (M : Type) extends AddSemigroup M, AddZeroClass M where
  smul : ℕ → M → M := nsmul_rec

@[simp] -- A simple erasure
instance AddMndG_to_NatSmul (M : Type) [AddMonoidGood M] : HasNatSmul M := ⟨AddMonoidGood.smul⟩

@[simp]
instance : AddMonoidGood ℕ where
 zero_add := Nat.zero_add
 add_zero := by simp
 smul := Nat.mul -- this is the same as `fun m n ↦ m * n`.
-- One more field `smul` is needed, of course.

example : HasNatSmul ℕ := AddMndG_to_NatSmul ℕ
example : HasNatSmul ℕ := SmulEqMul_on_Nat
example : AddMndG_to_NatSmul ℕ = SmulEqMul_on_Nat := rfl
-- does not work if we comment `smul` in `AddMonoidGood ℕ`: why?

example {n m : ℕ} : HasNatSmul.smul n m = n * m := by sorry

-- `⌘`

end InMathlib

namespace Exercises

/- ## Exercise 1
Produce instances of `ModuleWithRel, NormedModuleBad, NormedModuleGood` on the type `M → M` and
show, using the same "universal term" `p` used above, that this yields to conflicting instances
for `NormedModuleBad` but not for `NormedModuleGood`. -/



/- ## Exercice 2
Define the class of metric spaces (but call them `SpaceWithMetric` to avoid conflict with the
existing library) as defined in https://en.wikipedia.org/wiki/Metric_space#Definition, and deduce
an instance of `TopologicalSpace` on every `SpaceWithMetric`.

Explain why this is the *wrong* choice, on an explicit example, and fix this.
-/


/- ## Exercise 3
When defining a `ModuleWithRel` instance on any `NormedModuleBad` we used the relation "being in the
same ball of radius `1`. Clearly the choice of `1` was arbitrary.

Define an infinite collection of instances of `ModuleWithRel` on any `NormedModuleBad` indexed by
`ρ : ℝ≥0`, and reproduce both the bad and the good example.

There are (at least) two ways:
* Enrich the `NormedModule`'s structure with a `ρ`: this is straightforward.
* Keep `ρ` as a variable: this is much harder, both because Lean won't be very happy with a
`class` depending on a variable and because there will *really* be different instances even with
good choices, so a kind of "internal rewriting" is needed.
-/


end Exercises

end ForgetfulInheritance
