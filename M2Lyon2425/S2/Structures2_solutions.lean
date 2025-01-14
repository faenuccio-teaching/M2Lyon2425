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
  rel := fun m n ↦ ‖m - n‖₀ ≤ 1


-- `⌘`


-- The `NormedModuleBad` instance on a product
instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [NormedModuleBad M] [NormedModuleBad N] :
    NormedModuleBad (M × N) where
  norm_b := fun ⟨m, n⟩ ↦ max ‖m‖₀ ‖n‖₀

-- The `ModuleWithRel` instance on a product
instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [ModuleWithRel M] [ModuleWithRel N] :
    ModuleWithRel (M × N) where
  rel := fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModuleBad M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModuleBad M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  -- exact hp
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
  -- rel := --fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)
  rel := rel--since we already have a `ModuleWithRel` instance on `M × N`, we can use it.
  norm_g := fun ⟨m, n⟩ ↦ max ‖m‖₁ ‖n‖₁

-- This would have worked before as well.
example (M : Type) [AddCommGroup M] [NormedModuleGood M] : ModuleWithRel (M × M) := inferInstance

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModuleGood M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModuleGood M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  exact hp

/- The **same example** can be constructed using the `extend` construction:-/
-- whatsnew in --(see the last non-proteced `def`, whose name ends with `...toModuleWithRel`)
class NormedModuleGood₂ (M : Type*) extends AddCommGroup M, ModuleWithRel M where
  norm₂ : M → ℝ≥0


/- The `ModuleWithRel` instance on a `NormedModule₂` now comes for free, because
`NormedModule` extends `ModuleWithRel`.-/
instance (M : Type) [NormedModuleGood₂ M] : ModuleWithRel M := inferInstance

instance (M N : Type) [NormedModuleGood₂ M] [NormedModuleGood₂ N] : NormedModuleGood₂ (M × N) where
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
  norm₂ := fun ⟨m, n⟩ ↦ max (NormedModuleGood₂.norm₂ m) (NormedModuleGood₂.norm₂ n)

example (hp : ∀ M : Type, [NormedModuleGood₂ M] → ∀ m : M, p (rel m))
    (M : Type) [NormedModuleGood₂ M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  exact hp

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
instance /- (priority := low)  -/ SmulEqMul_on_Nat : HasNatSmul ℕ := ⟨fun n m ↦ n * m⟩

@[simp] -- We'll come back later on and discuss why these two fields are needed.
instance : AddMonoidBad ℕ := {zero_add := Nat.zero_add, add_zero := by simp}

-- We ended up with two multiplication by `ℕ` on `ℕ`
example : HasNatSmul ℕ := AddMndB_to_NatSmul ℕ
example : HasNatSmul ℕ := SmulEqMul_on_Nat

example : AddMndB_to_NatSmul ℕ = SmulEqMul_on_Nat := sorry--rfl does not work: yet they *are* equal

-- This induction proof owes a lot to the `@[simp]` in the previous definitions: remove and see...
example {n m : ℕ} : HasNatSmul.smul n m = nsmul_rec n m := by
  -- rfl -- does not work, look at the infoview!
  induction' n with k hk
  · simp
  · simp_all
    rw [← hk, add_one_mul, add_comm]


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

example {n m : ℕ} : HasNatSmul.smul n m = n * m := by rfl
-- this is not affected by priorities.

-- `⌘`

end InMathlib

namespace Exercises

/- ## Exercise 1
Produce instances of `ModuleWithRel, NormedModuleBad, NormedModuleGood` on the type `M → M` and
show, using the same "universal term" `p` used above, that this yields to conflicting instances
for `NormedModuleBad` but not for `NormedModuleGood`. -/

instance (M : Type) [AddCommGroup M] [NormedModuleBad M] : NormedModuleBad (M → M) where
  norm_b := fun f ↦ ‖ f 0 ‖₀

instance (M : Type) [AddCommGroup M] [ModuleWithRel M] : ModuleWithRel (M → M) where
  rel := fun f g ↦ ∀ x, rel (f x) (g x)

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModuleBad M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModuleBad M] (v : M → M) : p (rel v) := by
  specialize hp (M → M) v
  -- exact hp
  sorry

instance (M : Type) [AddCommGroup M] [NormedModuleGood M] : NormedModuleGood (M → M) where
  norm_g := fun f ↦ ‖ f 0 ‖₁
  rel := fun f g ↦ ∀ x, rel (f x) (g x)

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModuleGood M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModuleGood M] (v : M → M) : p (rel v) := by
  specialize hp (M → M) v
  exact hp

/- ## Exercice 2
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


/- ## Exercise 3
When defining a `ModuleWithRel` instance on any `NormedModuleBad` we used the relation "being in the
same ball of radius `1`. Clearly the choice of `1` was arbitrary.

Define an infinite collection of instances of `ModuleWithRel` on any `NormedModuleBad` indexed by
`ρ : ℝ≥0`, and reproduce both the bad and the good example.

There are (at least) two ways:
* Enrich the `NormedModule`'s structure with a `ρ`: this is straightforward.
* Keep `ρ` as a variable: this is much harder, both because Lean won't be very happy with a
`class` depending on a variable and because there will *really* be different instances even with
good choices. Try it nonetheless!
-/

open scoped NNReal

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

#help tactic omega

class NMG_r (M : Type) extends AddCommGroup M, NormedModuleGood M where
  ρ : ℝ≥0
  rrel := fun x y ↦ norm_g (x - y) ≤ ρ

instance (M : Type) [NMG_r M] : ModuleWithRel M where
  rel := NMG_r.rrel--fun x y ↦ ‖x - y‖₁ ≤ NMG_r.ρ M

instance (M N : Type) [NMG_r M] [NMG_r N] : NMG_r (M × N) where
  ρ := max (NMG_r.ρ M) (NMG_r.ρ N)
  norm_g := fun ⟨m, n⟩ ↦ max ‖m‖₁ ‖n‖₁
  rel := rel

example (ρ : ℝ≥0) (hp : ∀ M : Type, [NMG_r M] → ∀ m : M, p (rel m))
    (M : Type) [NMG_r M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  have prodRel : @rel (M × M) Prod.instAddCommGroup (instModuleWithRelProd M M) v 0 =
    (rel v.1 0 ∧ rel v.2 0) := rfl
  have prodNMG : @rel (M × M) NMG_r.toAddCommGroup (instModuleWithRel_2 (M × M)) v 0 =
    (norm_g (v - 0) ≤ NMG_r.ρ (M × M)) := rfl
  sorry


abbrev BadR (M : Type) (ρ : ℝ≥0) [AddCommGroup M] [NormedModuleBad M] : Type := M


instance (ρ : ℝ≥0) (M : Type) [AddCommGroup M] [NormedModuleBad M] : ModuleWithRel (BadR M ρ) where
  rel := fun x y ↦ ‖x - y ‖₀ ≤ ρ


end Exercises

end ForgetfulInheritance
