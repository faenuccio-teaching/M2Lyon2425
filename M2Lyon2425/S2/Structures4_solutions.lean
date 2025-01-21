import Init.Data.List.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic

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

example (X : Type) (v : L₁ X) : X := by
  let L : L₁ (Type → Type) := sorry


end AncillarySyntax
section FunnyBracket

open Real

-- Some examples of the interest of ⦃
open Function

def f : ℕ → ℕ := (· + 5) -- say something about `⬝`

def myInjective (f : ℕ → ℕ) : Prop :=
  ∀ {a b : ℕ}, f a = f b → a = b

lemma myInjective.comp {f g : ℕ → ℕ} (hf : myInjective f) (hg : myInjective g) :
    myInjective (f ∘ g) := by
  intro a b H
  apply hg
  apply hf
  exact H

lemma Inj_f : f.Injective := by
  intro _ _ h
  rwa [f, f, add_left_inj] at h

lemma myInj_f : myInjective f := by
  intro _ _ h
  rwa [f, f, add_left_inj] at h

lemma Inj_f_comp : Function.Injective (fun n ↦ f (f n)) := by
  -- show Injective (fun n ↦ (f ∘ f) n)
  apply Inj_f.comp
  exact Inj_f

lemma myInj_f_comp : myInjective (fun n ↦ f (f n)) := by
  apply myInj_f.comp
  -- sorry
  -- have := Inj_f
  have := Inj_f
  rw [Injective] at this
  -- exact @Inj_f
  -- apply Inj_f


/- The `..` syntax for exact and its interaction with `⦃` (if they're not used there might be
several remaining variables to discharge, albeit perhaps automatically). -/

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
