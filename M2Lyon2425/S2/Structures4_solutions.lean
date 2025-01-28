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
  True := sorryAx
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

inductive IsDirection : List Stations → Prop
  | c_SN : IsDirection [HotelDeVille, CroixPacquet]
  | b_SN : IsDirection [JeanMace, SaxeGambetta, PlaceGuichard, PartDieu]
  | a_SN : IsDirection [Perrache, Ampere, Bellecour, Cordeliers, HotelDeVille]
  | d_EW : IsDirection [Guillotiere, Bellecour, VieuxLyon]
  | back {L : List Stations} : IsDirection L → IsDirection L.reverse

structure Directions where
  stops : List Stations
  isDir : IsDirection stops

-- def reverse : Directions → Directions := fun ⟨D, hD⟩ ↦
--   ⟨D.stops.reverse, IsDirection.back D.isDir⟩

def A_SN : Directions where
  stops := [Perrache, Ampere, Bellecour, Cordeliers, HotelDeVille]
  isDir := IsDirection.a_SN

def A_NS : Directions where
  stops := [Perrache, Ampere, Bellecour, Cordeliers, HotelDeVille].reverse
  isDir := IsDirection.back IsDirection.a_SN

instance Directions.Setoid : Setoid Directions where
  r := fun L M ↦ L.stops = M.stops.reverse ∨ L.stops = M.stops
  iseqv := by
    constructor
    · tauto
    · intros
      rw [← reverse_eq_iff]
      tauto
    · intro _ _ _
      rintro (h1 | h1) (_ | _) <;> simp_all

def Lines := Quotient Directions.Setoid

abbrev A : Lines := Quotient.mk'' A_NS
abbrev A'' : Lines := ⟦A_NS⟧
abbrev A' : Lines := Quotient.mk'' A_SN
abbrev A''' : Lines := Quotient.mk'' A_NS

example : A = A' := by
  rw [Quotient.eq'']
  constructor
  rfl

#check List.get

structure Trip (start arrival : Stations) where
  stops : List Stations
  not_empty : stops ≠ []
  start : stops.head not_empty = start
  arrival : stops.getLast not_empty = arrival
  nodup : stops.Nodup
  connection (l : List Stations) : IsInfix l stops → l.length == 2 →
    ∃ D : Directions, IsInfix l D.stops

def Connected (S A : Stations) : Prop := Nonempty (Trip S A)

lemma Connected_symm (stat : Stations) : Connected stat stat := by
  use [stat] <;> simp
  intro l hl _
  have := hl.length_le
  simp_all

lemma Connected_rfl {pt₁ pt₂} (h : Connected pt₁ pt₂) : Connected pt₂ pt₁ := by
  let t := choice h
  use t.stops.reverse
  · simp [t.not_empty]
  · simp [t.arrival]
  · simp [t.start]
  · simp [t.nodup]
  · intro l hl htwo
    obtain ⟨D, hD⟩ := t.connection l.reverse ?_ ?_
    fconstructor
    · fconstructor
      · use D.stops.reverse
      · apply IsDirection.back
        exact D.isDir






-- -- #check Line.notempty
-- def Start (L : Line) : Stations := by
--   exact (L.stops).head (L.not_empty)

-- def End (L : Line) : Stations := by
--   exact (L.stops).length-- (L.not_empty)

-- inductive Terminus (L : Line) : Type*
--   | Start M : Terminus L
--   -- | (stops L).head (not_empty L) : Terminus
