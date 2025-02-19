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

inductive IsDirection : List Stations → Prop
  | a_SN : IsDirection [Perrache, Ampere, Bellecour, Cordeliers, HotelDeVille]
  | b_SN : IsDirection [JeanMace, SaxeGambetta, PlaceGuichard, PartDieu]
  | c_SN : IsDirection [HotelDeVille, CroixPacquet]
  | d_EW : IsDirection [Guillotiere, Bellecour, VieuxLyon]
  | back {L : List Stations} : IsDirection L → IsDirection L.reverse

abbrev Directions := {D : List Stations // IsDirection D}


def Directions.reverse : Directions → Directions :=
  fun ⟨a, ha⟩ ↦ ⟨a.reverse, IsDirection.back ha⟩

@[simp]
lemma Directions.reverse_eq (D : Directions) : D.reverse.1 = D.1.reverse := by rfl

lemma two_le_length_ofDirection (D : Directions) : 2 ≤ D.1.length := by
  rcases D with ⟨_, hl⟩
  induction hl
  simp
  simp
  simp
  simp
  simp_all

lemma ne_nil_Direction (D : Directions) : D.1 ≠ [] := by
  apply ne_nil_of_length_pos
  linarith [two_le_length_ofDirection D]

-- The directions
abbrev A_SN : Directions := ⟨_, IsDirection.a_SN⟩

abbrev A_NS : Directions := ⟨_, IsDirection.back IsDirection.a_SN⟩

abbrev B_SN : Directions := ⟨_, IsDirection.b_SN⟩

abbrev B_NS : Directions := ⟨_, IsDirection.back IsDirection.b_SN⟩

abbrev C_SN : Directions := ⟨_, IsDirection.c_SN⟩

abbrev C_NS : Directions := ⟨_, IsDirection.back IsDirection.c_SN⟩

abbrev D_EW : Directions := ⟨_, IsDirection.d_EW⟩

abbrev D_WE : Directions := ⟨_, IsDirection.back IsDirection.d_EW⟩


instance Directions.Setoid : Setoid Directions where
  r := fun d₁ d₂ ↦ d₁.1 = d₂.1 ∨ d₁.1 = d₂.1.reverse
  iseqv := by
    constructor
    · intro d; left; rfl
    · intro d e h
      cases h with
      | inl h' => left; rw [h']
      | inr h' => right; rw [h']; simp
    · intro _ _ _
      rintro (h1 | h2) (_ | _) <;> simp_all


abbrev Lines := Quotient Directions.Setoid

-- Several ways to write a line
abbrev A : Lines := Quotient.mk'' A_NS
abbrev A' : Lines := ⟦A_NS⟧

example : A = A' := by rfl



end Metro
