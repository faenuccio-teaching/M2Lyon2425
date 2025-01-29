import Init.Data.List.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.Interval


section Structures

structure OneNat where
  fst : ℕ

structure TwoNat where
  pair ::
  fst : ℕ
  snd : ℕ

structure Couple where
  left : ℕ
  right : ℕ

structure OneNatOneInt where
  fst : ℕ
  snd : ℤ

structure Mess (α β γ : Type) [Zero α] [TopologicalSpace β] [UniformSpace γ] :=--`where` or `:=`
  a : α := 0
  f : α → β → γ → γ
  cont : Continuous (f a)

-- `⌘`


-- This forgets the label and takes it back.
example (x : OneNat) : TwoNat := sorry

-- another syntax
example (x : OneNat) : TwoNat := sorry

example (x : TwoNat) : OneNat := sorry

example (x : TwoNat) : OneNat := sorry

example (x : TwoNat) : Couple := sorry

example (x : OneNat) : Couple := sorry

example (x : OneNat) : ℕ := sorry


-- This forgets the label and takes it back.
example (x : OneNat) : TwoNat := sorry

-- another syntax
example (x : OneNat) : TwoNat := sorry

example (x : TwoNat) : OneNat := sorry

example (x : TwoNat) : OneNat := sorry


example (x : TwoNat) : Couple := sorry

example (x : OneNat) : Couple := sorry

example (x : OneNat) : ℕ := sorry


structure Mix where
  fst : ℕ
  right : ℕ

#check Mix.mk

def mix1 (x : TwoNat) (y : Couple) : Mix := sorry
/- remember that `x := {x.fst, x.snd}`, `y = {y.left, y.right}`
  and `Mix.mk` takes a `fst : ℕ` and `right : ℕ`: s we need to throw away `x.snd` and `y.left`-/

def mix1' (x : TwoNat) (y : Couple) : Mix := sorry

-- the order does not really matter, it "destructs and reconstructs".
def mix2 (x : TwoNat) (y : Couple) : Mix := sorry


example : mix1 = mix1' := sorry

example : mix1 = mix2 := sorry

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
example (x : Mix) (y : Mix') (z : ThreeNat) : Mix₃ := sorry

-- A final example with a `Prop`-valued field:

#check Mess.mk

def f₁ : Mess ℕ ℕ ℕ := sorry

def f₂ : Mess ℕ ℕ ℕ := sorry

-- `Prop`-valued fields disappear by proof irrelevance
example : f₁ = f₂ := sorry


-- `⌘`


-- ## Extends


structure Blob extends OneNatOneInt, OneNat
structure Blob' extends OneNatOneInt, TwoNat

structure TwoNatExt extends OneNat where
  snd : ℕ

/- Under the hood, Lean destructs all these terms and reconstructs them "in the right order" ---
 but keeping labels. -/

def TwoExtToCouple : TwoNatExt → Couple := by sorry

def TwoNatToCouple : TwoNat → Couple :=  sorry

/- And if there are duplicates? Remember that
  `structure Mix where`
      `fst : ℕ`
      `right : ℕ`     -/

structure ThreeNatExt extends TwoNat, Mix

#print ThreeNatExt

/- Overlapping fields are not duplicated; moreover, whenever possible, fields will coincide with
constructors of the parent structure; in case of overlapping fields, things are destructured. -/
def TwoNatToExt : TwoNat → TwoNatExt := sorry

/- In the above definition, `with` is able to
1. Destruct `x` into `x.fst` and get a `OneNat`, that populates the first field of a `TwoNatExt`
2. Observe that the other field `x.snd` has the right type and label of what is missing. -/

example (x : TwoNat) : TwoNatToExt x = ⟨⟨x.fst⟩, x.snd⟩ := sorry

/- Remember that `ThreeNatExt extends TwoNat, Mix` and
  `structure Mix where`
        `fst : ℕ`
        `right : ℕ`     -/

#check ThreeNatExt.mk

def M₁ : Mix := {fst := 17, right := 11}
def two : TwoNat := {fst := 1, snd := 2}

def three : ThreeNatExt := {M₁, two with}
def three' : ThreeNatExt := {two, M₁ with}

example : three.fst = 17 := by sorry
example : three'.fst = 1 := by sorry

/- So in reality Lean is first using the first variable (`M₁` or `two`), possibly throwing away
useless stuff, and then using what follows to complete them. -/

example : three = three' := sorry


def M₂ : Mix := {fst := 13, right := 11}
def trois : ThreeNatExt := {two, M₂ with}

example : trois.fst = 1 := sorry

example : three' = trois := sorry


-- `⌘`


/- ### In True Math
We can now go back to what we saw the last weeks: remember that we defined -/

class AddMonoidBad (M : Type) extends Add M, AddZeroClass M

instance : AddMonoidBad ℕ := sorry

instance : AddMonoidBad ℕ := sorry

instance : AddMonoidBad ℕ := sorry

instance : AddMonoidBad ℕ := sorry

end Structures

section AncillarySyntax

open scoped NNReal


-- `⌘`


def F₁ : ℝ → ℝ≥0 := fun a ↦ ‖ a ‖₊
def F₂ : ℝ → ℝ≥0 := (‖ · ‖₊)

def G₁ : ℕ → ℕ := (· + 1)
def G₂ : ℕ → ℕ := fun x ↦ x + 1
def G₃ : ℕ → ℕ := fun x ↦ Nat.succ x

example : F₁ = F₂ := sorry
example : G₁ = G₂ := sorry
example : G₂ = G₃ := sorry

def L₁ : Type _ → Type _ := (List ·) --
def L₂ : Type* → Type _ := (List ·)
def L₃ : Type* → Type* := (List ·)
/-The difference between `Type*` and `Type _` is that the first declares a term in every universe
level, the second requires Lean to infer it automatically. -/


-- `⌘`


open Real Function

def myInjective (f : ℕ → ℕ) : Prop :=
  ∀ {a b : ℕ}, f a = f b → a = b

-- def Injective (f : α → β) : Prop :=
--   ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂


lemma myInjective.comp {f g : ℕ → ℕ} (hf : myInjective f) (hg : myInjective g) :
    myInjective (f ∘ g) := by sorry

example (f g : ℕ → ℕ) (hf : myInjective f) (hg : ∀ (a b), g a = g b → a = b) :
  myInjective (f ∘ g) := by sorry

/- As "explained" in the error message, `myInjective g` creates two variables `a† : ℕ` and
`b† : ℕ` so that `myInjective g` *is* `g a† = g b† → a† = b†`and the `∀` has vanished. -/

example (f g : ℕ → ℕ) (hf : Injective f) (hg : ∀ (a b), g a = g b → a = b) :
  Injective (f ∘ g) := by sorry

example (a b : ℕ) (f : ℕ → ℕ) (h_myInj : myInjective f) (h_Inj : Injective f) (hab : f a = f b) :
  True := sorry


-- `⌘`


end AncillarySyntax


noncomputable section Exercises

-- ## Exercise 1
open scoped NNReal
--Recall from last lecture the two classes below, and the test-variable `p`:
class NormedModuleBad (M : Type*) [AddCommGroup M] where
  norm_b : M → ℝ≥0
export NormedModuleBad (norm_b)

notation "‖" e "‖₀" => norm_b e

instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [NormedModuleBad M] [NormedModuleBad N] :
    NormedModuleBad (M × N) where
  norm_b := fun ⟨m, n⟩ ↦ max ‖m‖₀ ‖n‖₀

class ModuleWithRel (M : Type*) [AddCommGroup M] where
  rel : M → M → Prop

export ModuleWithRel (rel)

instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [ModuleWithRel M] [ModuleWithRel N] :
    ModuleWithRel (M × N) where
  rel := fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)

variable (p : ∀ {T : Type}, (T → Prop) → Prop)
/- When defining a `ModuleWithRel` instance on any `NormedModuleBad` we used the relation "being in the
same ball of radius `1`. Clearly the choice of `1` was arbitrary.

Define an infinite collection of instances of `ModuleWithRel` on any `NormedModuleBad` indexed by
`ρ : ℝ≥0`, and reproduce both the bad and the good example.

There are (at least) two ways:
* Enrich the `NormedModule`'s structure with a `ρ`: this is straightforward.
* Keep `ρ` as a variable: this is much harder, both because Lean won't be very happy with a
`class` depending on a variable and because there will *really* be different instances even with
good choices, so a kind of "internal rewriting" is needed.
-/


-- ## Exercise 2
/- Prove the following claims, stated in the section about the non-discrete metric on `ℕ`:
1. The uniformity is discrete if the metric is discrete.
2. As uniformities, `𝒫 (idRel) = ⊥`.
3. Is the equality `𝒫 (idRel) = ⊥` true as filters?
4. For any `α`, the discrete topology is the bottom element `⊥` of the type `TopologicalSpace α`.
-/


/- ## Exercise 3
In the attached file `PlanMetro.pdf` you find a reduced version of Lyon's subway network. I have
already defined the type of `Stations`.

1. Find a way to formalize lines (both ordered and non-ordered), and the notion for two stations of
being connected by a path.

2. Prove that being connected is an equivalence relation.

3. Prove that if we add a "circle line" connecting all terminus', then every two stations become
connected.

4. Prove that in the above configuration with a "circle line" every trip requires of at most two
changes.
-/

inductive Stations : Type
  | JeanMace : Stations
  | SaxeGambetta : Stations
  | PlaceGuichard : Stations
  | PartDieu : Stations
  | HotelDeVille : Stations
  | CroixPacquet : Stations
  | Perrache : Stations
  | Ampere : Stations
  | Bellecour : Stations
  | Cordeliers : Stations
  | Guillotiere : Stations
  | VieuxLyon : Stations

open Stations List Classical


end Exercises
