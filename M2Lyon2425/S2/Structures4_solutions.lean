import Init.Data.List.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.Interval

section AncillarySyntax

open scoped NNReal

/- ## The anonymous variable
(typed `\. = ·` and not `\cdot = ⬝`). -/

def f₁ : ℝ → ℝ≥0 := fun a ↦ ‖ a ‖₊
def f₂ : ℝ → ℝ≥0 := (‖ · ‖₊)

def g₁ : ℕ → ℕ := (· + 1)
def g₂ : ℕ → ℕ := fun x ↦ x + 1
def g₃ : ℕ → ℕ := fun x ↦ Nat.succ x

example : f₁ = f₂ := rfl
example : g₁ = g₂ := rfl
example : g₂ = g₃ := rfl

def L₁ : Type _ → Type _ := (List ·) --
def L₂ : Type* → Type _ := (List ·)
def L₃ : Type* → Type* := (List ·)
/-The difference between `Type*` and `Type _` is that the first declares a term in every universe
level, the second requires Lean to infer it automatically. -/


end AncillarySyntax
section FunnyBracket

open Real

-- Some examples of the interest of ⦃
open Function

def myInjective (f : ℕ → ℕ) : Prop :=
  ∀ {a b : ℕ}, f a = f b → a = b

-- def Injective (f : α → β) : Prop :=
--   ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂


lemma myInjective.comp {f g : ℕ → ℕ} (hf : myInjective f) (hg : myInjective g) :
    myInjective (f ∘ g) := by
  intro a b H
  apply hg
  apply hf
  exact H

example (f g : ℕ → ℕ) (hf : myInjective f) (hg : ∀ (a b), g a = g b → a = b) :
  myInjective (f ∘ g) := by
  apply myInjective.comp
  exact hf
  exact hg
  exact @hg

/- As "explained" in the error message, Lean has a mechanism for automatically insterting
implicit λ-variables when needed; so, as soon as it encounters `myInjective g` it creates two
metavariables `a† : ℕ` and `b† : ℕ` so that `myInjective g` *is*
`g a† = g b† → a† = b†`
and the `∀` has vanished.

The role of the `@` is to *disable* this mechanism, which is indeed what allows to explicitely
populate the fields when needed.

The syntax `⦃` introduces so-called *minimally/weakly inserted implicit arguments*, that only
becomes populated when something explicit *following them* is provided (lest the whole term would
not type-check): if nothing is inserted *after*, they stay implicit and the `λ`-term is treated as
a honest term in the `∀`-Type.

For more on this, see for example
https://proofassistants.stackexchange.com/questions/66/in-lean-what-do-double-curly-brackets-mean
or
https://lean-lang.org/doc/reference/latest/Terms/Functions/#implicit-functions (section §5.3.1).
-/

example (f g : ℕ → ℕ) (hf : Injective f) (hg : ∀ (a b), g a = g b → a = b) :
  Injective (f ∘ g) := by
  apply Injective.comp
  exact hf
  exact hg

example (a b : ℕ) (f : ℕ → ℕ) (h_myInj : myInjective f) (h_Inj : Injective f) (hab : f a = f b) :
  True := by sorry
  -- have : h_myInj = h_Inj := rfl
  -- have : h_myInj = h_myInj := rfl
  -- have : h_Inj = h_Inj := rfl
  -- have : h_myInj hab = h_myInj hab := rfl
  -- have : h_myInj hab = h_Inj hab := rfl





end FunnyBracket

/- ## Exercice
* Define structures for stations, lines, trips (insisting on connections being reasonable, i.e.
if one changes line there must be a *connection* (a type on its own?)
* Prove the following theorems:
0. Perhaps, do not assume that the graph is path-connected and add the def of a "good trip".
1. If there is a trip from `a` to `b` with `n` changes, there is also a trip from `b` to `a` with
`n` changes
2. If there is a trip from `a` to `b` with `n` changes and one from `b` to `c` with `m` changes, there
is a trip from `a` to `c` with at `n+m` changes.
3. Define the type of trips with at most `n` changes and state the above results here?
4. Define a "circle line" that touches all terminus and prove that, assuming this exists, there is
a trip from `a` to `b` with at most two changes for every `a` and `b` (go to the terminus of a line
through `a`, pick the circle line to a terminus of a line through `b`, use this last line till `b`).


-/

inductive Stations : Type*
  | PartDieu : Stations
  | Perrache : Stations

structure Line where
  stops : List Stations
  not_empty : stops ≠ []
  nodup : stops.Nodup

structure Trip where
  n : ℕ+ -- the number of stops
  select : Fin n → Stations
  inj : select.Injective


-- -- #check Line.notempty
-- def Start (L : Line) : Stations := by
--   exact (L.stops).head (L.not_empty)

-- def End (L : Line) : Stations := by
--   exact (L.stops).length-- (L.not_empty)

-- inductive Terminus (L : Line) : Type*
--   | Start M : Terminus L
--   -- | (stops L).head (not_empty L) : Terminus
