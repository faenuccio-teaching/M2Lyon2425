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

notation "‖" e "‖₁" => norm_b e

class ModuleWithRel (M : Type*) extends AddCommGroup M where
  rel : M → M → Prop

export ModuleWithRel (rel)


instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [NormedModule_bad M] [NormedModule_bad N] :
    NormedModule_bad (M × N) where
  norm_b := fun ⟨m, n⟩ ↦ max ‖m‖₁ ‖n‖₁

instance (M N : Type*) [ModuleWithRel M] [ModuleWithRel N] : ModuleWithRel (M × N) where
  rel := fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)

instance (M : Type*) [AddCommGroup M] [NormedModule_bad M] : ModuleWithRel M where
  rel := fun m n ↦ ‖m - n‖₁ ≤ 1

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModule_bad M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModule_bad M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  -- exact hp
/-This is not working because the `rel` in the goal comes from the `ModuleWithRel` instance on a
product, whereas the `rel` in `hp` comes from the `Rel` instance *deduced* from the
`NormedModule_bad` instance on the product (it suffices to hover on the terms to see this).
-/
  sorry

/- Hot to solve this? The problem is that passing from `NormedModule₁` to `ModuleWithRel`
(i.e. declaring a `ModuleWithRel` instance on every `NormedModule₁`)
is not a pure "erasure", because we are not simply throwing away a field, but using some
field in the first (namely `‖ ⬝ ‖₁`) to construct the term `rel` of the second: this yields to the
problem we have just witnessed, and the slogan is that only "forgetful inheritance" is allowed: this
is an idea initially proposed by Affeldt, Cohen, Kerjean, Mahboubi, Rouhling and Sakaguchi in
https://inria.hal.science/hal-02463336v2, from which this example is extracted. In their words, one

" needs to ensure definitional equality by including poorer structures into richer ones; this way,
deducing one structure from the other always amounts to erasure of data, and this guarantees
there is a unique and canonical way of getting it. We call this technique *forgetful inheritance*,
as it is reminiscent of forgetful functors in category theory."
-/

class NormedModule₁ (M : Type*) [AddCommGroup M] where
  rel : M → M → Prop
  norm₁ : M → ℝ

instance (M : Type*) [AddCommGroup M] [NormedModule₁ M] : ModuleWithRel M := ⟨NormedModule₁.rel⟩
/- The huge difference with what happened for `NormedModule_bad` is that there the instance
contained some **new** data (the definition of `rel`), whereas here it is simply a projection, or the
forgetfullness of `norm₁`. No *creation*!
-/

-- Let's inspect the difference: in one case we need a `Rel`, in the other we need an `AddCommGroup`
#print NormedModule_bad
#print NormedModule₁

export NormedModule₁ (norm₁)

notation "‖" e "‖" => norm₁ e

instance (M N : Type*) [AddCommGroup M] [NormedModule₁ M] [AddCommGroup N] [NormedModule₁ N] :
  NormedModule₁ (M × N) where
  rel := fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)
  norm₁ := fun ⟨m, n⟩ ↦ max ‖m‖ ‖n‖

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, [AddCommGroup M] → [NormedModule₁ M] → ∀ m : M, p (rel m))
    (M : Type) [AddCommGroup M] [NormedModule₁ M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  /-the `rel v` in the goal is still the `rel` coming from the `ModuleWithRel` instance on a
product, and the `rel` in `hp` still comes from the `ModuleWithRel` instance deduced from the
`NormedModule₁ structure on `M × M`; but now this second instance is simply obtained from the first
by forgetting a field, so in particular it *coincides definitionally* with the previous one.

Indeed, observe that in the first case we were forced to manually define a `ModuleWithRel` instance
on the product, whereas now the path has been
`?m : ModuleWithRel (M × M)` ← `?m : NormedModule₁ (M × M)` ← *the instance above*
-->**NO questo è falso, ma probabilmente non troppo: il modo in cui si crea la instance di `ModuleWithRel` cambia nei due casi**
  -/
  exact hp

/- The **same example** can be constructed using the `extend` construction:-/
-- whatsnew in --(see the last one)
class NormedModule₂ (M : Type*) extends ModuleWithRel M where
  norm₂ : M → ℝ

/- As seen above, the `ModuleWithRel` instance on a `NormedModule₂` now comes for free, because
`NormedModule` **extends** `ModuleWithRel`.-/
instance (M : Type*) [ModuleWithRel M] [NormedModule₂ M] : ModuleWithRel M := inferInstance

-- variable (X : Type*) [ModuleWithRel X] [NormedModule₁ X]
-- #synth ModuleWithRel X

/- From the point of view of constructing a library, the above solution looks problematic. What can
we do if we already have a class and we want to later insert something "below" it (i. e. to create
a class that is more general than the one we had, so that every element of the first will have an
instance of the second?).
**ANSWER?**
Add here the `nsmul` and `zsmul` examples (and the `TopologicalSpace` in `UniformSpace`).

-/

end ForgetfulInheritance
