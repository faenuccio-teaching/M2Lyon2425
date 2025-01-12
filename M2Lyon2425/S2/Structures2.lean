import Mathlib.Data.Real.Basic
import Mathlib.Topology.UniformSpace.Basic

noncomputable section

section ForgetfulInheritance

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


-- `⌘ `


-- We can now go back to what we saw last week: remember that we defined
class AddMonoid_bad (M : Type) extends AddSemigroup M, AddZeroClass M

@[simp]
instance : AddMonoid_bad ℕ := {zero_add := Nat.zero_add, add_zero := by simp}

@[simp]
def Nat_smul {M : Type} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + Nat_smul n a

class HasNat_smul (M : Type) [Zero M] [Add M] where
  smul : ℕ → M → M

@[simp]
instance (priority := 10000) (M : Type) [AddMonoid_bad M] : HasNat_smul M := ⟨Nat_smul⟩

@[simp] -- make some comments here and above on why these `@[simp]` help the proof below?
instance (priority := 10001) : HasNat_smul ℕ := ⟨fun n m ↦ n * m⟩

-- devo capire meglio

example {n m : ℕ} : Nat_smul n m = HasNat_smul.smul n m := by
  by_cases hn : n = 0
  · rw [hn]
    simp
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hk]
    simp
    -- rw [add_one_mul, add_comm]--funzionava prima di commentare la `instance HasNat_smul ℕ`
    -- simp
    -- sorry

-- Say a word about priorities, and the fact that they're in general the wrong way to solve these issues

-- In our case, we can modify the definition of `AddMonoid₃` to include a `nsmul` data field and
-- some Prop-valued fields ensuring this operation is provably the one we constructed above.

class AddMonoid_good (M : Type) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  smul : ℕ → M → M := Nat_smul
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  smul_zero : ∀ x, smul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  smul_succ : ∀ (n : ℕ) (x), smul (n + 1) x = x + smul n x := by intros; rfl

instance (M : Type) [AddMonoid_good M] : HasNat_smul M := ⟨Nat_smul⟩

-- instance mySMul {M : Type*} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

-- **ADD** the `TopologicalSpace` in `UniformSpace`).

end ForgetfulInheritance
