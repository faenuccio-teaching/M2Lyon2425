import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.FinCases

section Metro

/- ## Exercise
"In the attached file `PlanMetro.pdf` you find a reduced version of Lyon's subway network. I have
already defined the type of `Stations`.

1. Find a way to formalize lines (both ordered and non-ordered), and the notion for two stations of
being connected by a path.

2. Prove that being connected is an equivalence relation.

3. Prove that if we add a "circle line" connecting all Terminus', then every two stations become
connected.

-/


namespace Metro -- just to avoid overwriting the root definition.
inductive List (α : Type*) where
  /-- `[]` is the empty list. -/
  | nil : List α
  /-- If `a : α` and `l : List α`, then `cons a l`, or `a :: l`, is the
  list whose first element is `a` and with `l` as the rest of the list. -/
  | cons (head : α) (tail : List α) : List α
end Metro

#check ([2, 3] : List ℕ)
#check (Prop :: [ℤ, Bool] : List Type)
#check ([Prop, Nat] ++ [ℤ, Bool] : List Type)

example : [2, 37, 101] = 2 :: 37 :: [101] := rfl
example : [true, false] = true :: [false] := rfl
example : [false, true] = (true :: [false]).reverse := rfl
example : ([2 < 3, 1 = 1] ++ [0 = 0, True] : List Prop )= [2 < 3, 1 = 1, 0 = 0, True] := rfl

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


open Stations List

#print Finset.card

structure LigneOrdonnee where
  data : Finset (List Stations)
  deuxSens : Finset.card data = 2
  bienInverse : ∀ s ∈ data, ∃ t ∈ data, s = t.reverse

structure LigneDesordonnee where
  lesStations : Finset Stations

end Metro
