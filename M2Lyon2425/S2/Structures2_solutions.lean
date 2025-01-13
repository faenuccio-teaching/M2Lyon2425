import Mathlib.Data.Real.Basic
import Mathlib.Topology.UniformSpace.Basic

noncomputable section

--  # Forgetful Innheritance
namespace ForgetfulInheritance

-- ## An Example
section AnExample

class NormedModule_bad (M : Type*) [AddCommGroup M] where
  norm_b : M → ℝ

class NormedModule_ext (M : Type*) extends AddCommGroup M where
  norm_ext : M → ℝ
/- Of course, it `NomedModule_ext` is preferable, but for inspecting the details of this section, it
is better to keep all fields as explicit as possible. -/

#print NormedModule_ext
#print NormedModule_bad

export NormedModule_bad (norm_b)

notation "‖" e "‖₀" => norm_b e

class ModuleWithRel (M : Type*) [AddCommGroup M] where
  rel : M → M → Prop

export ModuleWithRel (rel)

-- The `ModuleWithRel` instance on every `NormedModule_bad`.
instance (M : Type*) [AddCommGroup M] [NormedModule_bad M] : ModuleWithRel M where
  rel := fun m n ↦ ‖m - n‖₀ ≤ 1


-- `⌘`


-- The `NormedModule_bad` instance on a product
instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [NormedModule_bad M] [NormedModule_bad N] :
    NormedModule_bad (M × N) where
  norm_b := fun ⟨m, n⟩ ↦ max ‖m‖₀ ‖n‖₀

-- The `ModuleWithRel` instance on a product
instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [ModuleWithRel M] [ModuleWithRel N] :
    ModuleWithRel (M × N) where
  rel := fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)


-- `⌘`


variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModule_bad M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModule_bad M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  -- exact hp
  sorry


-- `⌘`


class NormedModule (M : Type*) [AddCommGroup M] where
  norm : M → ℝ
  rel : M → M → Prop := fun m n ↦ norm (m - n) ≤ 1

export NormedModule (norm)

notation "‖" e "‖" => norm e

instance (M : Type*) [AddCommGroup M] [NormedModule M] : ModuleWithRel M := ⟨NormedModule.rel⟩


-- Let's inspect the difference: in one case we need a `rel`, in the other we need an `AddCommGroup`
#print NormedModule_bad
#print NormedModule

instance (M N : Type*) [AddCommGroup M] [NormedModule M] [AddCommGroup N] [NormedModule N] :
  NormedModule (M × N) where
  -- rel := --fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)
  rel := rel--since we already have a `ModuleWithRel` instance on `M × N`, we can use it.
  norm := fun ⟨m, n⟩ ↦ max ‖m‖ ‖n‖

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (M : Type) [AddCommGroup M] [NormedModule M] : ModuleWithRel (M × M) := inferInstance

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModule M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModule M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  exact hp

/- The **same example** can be constructed using the `extend` construction:-/
-- whatsnew in --(see the last one)
class NormedModule₂ (M : Type*) extends AddCommGroup M, ModuleWithRel M where
  norm₂ : M → ℝ


/- The `ModuleWithRel` instance on a `NormedModule₂` now comes for free, because
`NormedModule` extends `ModuleWithRel`.-/
instance (M : Type) [NormedModule₂ M] : ModuleWithRel M := inferInstance

instance (M N : Type) [NormedModule₂ M] [NormedModule₂ N] : NormedModule₂ (M × N) where
  -- add := _
  -- add_assoc := _
  -- zero := _
  -- zero_add := _
  -- add_zero := _
  -- nsmul := _
  -- neg := _
  -- zsmul := _
  -- neg_add_cancel := _
  -- add_comm := _
  rel := rel
  norm₂ := fun ⟨m, n⟩ ↦ max (NormedModule₂.norm₂ m) (NormedModule₂.norm₂ n)

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, [NormedModule₂ M] → ∀ m : M, p (rel m))
    (M : Type) [NormedModule₂ M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  exact hp

-- We'll see more details about this `extend` construction and its syntax later on.


-- `⌘`
end AnExample

/- ## In Mathlib-/
section InMathlib

class AddMonoidBad (M : Type) extends AddSemigroup M, AddZeroClass M

class HasNatSmul (M : Type) [Zero M] [Add M] where
  smul : ℕ → M → M

-- A recursive definition of `n • x = x + x + ... + x` (`n` times).
@[simp]
-- These `@[simp]` help the inductive proof below: remove and see...
def nsmul_rec {M : Type} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul_rec n a


@[simp]
instance AddMndB_to_NatSmul (M : Type) [AddMonoidBad M] : HasNatSmul M := ⟨nsmul_rec⟩

@[simp]
instance /- (priority := low) -/ SmulEqMul_on_Nat : HasNatSmul ℕ := ⟨fun n m ↦ n * m⟩

@[simp]
instance : AddMonoidBad ℕ := {zero_add := Nat.zero_add, add_zero := by simp}
-- We'll come back later on and discuss why these two fields are needed.


example : HasNatSmul ℕ := AddMndB_to_NatSmul ℕ
example : HasNatSmul ℕ := SmulEqMul_on_Nat
example : AddMndB_to_NatSmul ℕ = SmulEqMul_on_Nat := sorry--rfl does not work

example {n m : ℕ} : HasNatSmul.smul n m = nsmul_rec n m := by
  -- rfl -- does not work, look at the infoview!
  induction' n with k hk
  · simp
  · simp_all
    rw [← hk, add_one_mul, add_comm]
  -- rfl


-- `⌘`


class AddMonoidGood (M : Type) extends AddSemigroup M, AddZeroClass M where
  smul : ℕ → M → M := nsmul_rec

@[simp]
instance AddMndG_to_NatSmul (M : Type) [AddMonoidGood M] : HasNatSmul M := ⟨AddMonoidGood.smul⟩

@[simp]
instance : AddMonoidGood ℕ where
 zero_add := Nat.zero_add
 add_zero := by simp
 smul := fun n m ↦ n * m -- this is the same as `fun m n ↦ m * n`.
-- One more field is needed, of course.

example : HasNatSmul ℕ := AddMndG_to_NatSmul ℕ
example : HasNatSmul ℕ := SmulEqMul_on_Nat
example : AddMndG_to_NatSmul ℕ = SmulEqMul_on_Nat := rfl
-- does not work if we comment `smul` in `AddMonoidGood ℕ`.

example {n m : ℕ} : HasNatSmul.smul n m = n * m := by rfl
-- this is not affected by priorities.

end InMathlib

end ForgetfulInheritance

namespace Extends


end Extends
