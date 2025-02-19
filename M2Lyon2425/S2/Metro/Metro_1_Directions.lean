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

def Directions.reverse : Directions → Directions := by
  intro l
  obtain ⟨l, hl⟩ := l
  exact ⟨l.reverse, IsDirection.back hl⟩

@[simp]
lemma Directions.reverse_eq (D : Directions) : D.reverse.1 = D.1.reverse := by
  rfl

lemma two_le_length_ofDirection (D : Directions) : 2 ≤ D.1.length := by
  cases' D with D hD
  induction' hD with s hs hs₂
  · simp only [length_cons, length_singleton, Nat.reduceAdd, Nat.reduceLeDiff]
  · simp only [length_cons, length_singleton, Nat.reduceAdd, Nat.reduceLeDiff]
  · simp only [length_cons, length_singleton, Nat.reduceAdd, le_refl, length_nil]
  · simp only [length_cons, length_singleton, Nat.reduceAdd, Nat.reduceLeDiff]
  · simp only [length_reverse] at hs₂ ⊢
    exact hs₂

lemma ne_nil_Direction (D : Directions) : D.1 ≠ [] := by
  cases' D with D hD
  induction' hD with s hs hs₂
  · simp only [ne_eq, not_false_eq_true]
  · simp only [ne_eq, not_false_eq_true]
  · simp only [ne_eq, not_false_eq_true]
  · simp only [ne_eq, not_false_eq_true]
  · simp only [ne_eq, reverse_eq_nil_iff] at hs₂ ⊢
    exact hs₂

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
  r := fun D D' ↦ D.1 = D'.1.reverse ∨ D.1 = D'.1
  iseqv := by
    constructor
    · simp only [or_true, implies_true]
    · intros
      rw [← reverse_eq_iff]
      tauto
    · intro _ _ _
      rintro (h1 | h2) (_ | _) <;> simp_all

def Lines := Quotient Directions.Setoid

-- Several ways to write a line
abbrev A : Lines := Quotient.mk'' A_NS
abbrev A' : Lines := sorry
abbrev A'' : Lines := Quotient.mk'' A_SN

example : A = A' := sorry
example : A = A'' := by
  rw [Quotient.eq'']
  constructor
  rfl

-- Being connected

-- In mathlib
variable {α : Type*}
def nthLe (l : List α) (n : ℕ) (h : n < l.length) : α := get l ⟨n, h⟩

def connected (s₁ s₂ : Stations) :=
    ∃ (D D' : Directions), (s₁ ∈ D.1 ∧ s₂ ∈ D'.1 ∧ ∃ (s : Stations), s ∈ D.1 ∧ s ∈ D'.1)

instance : Equivalence (fun s₁ s₂ ↦ connected s₁ s₂) where
  refl := sorry
  symm := sorry
  trans := sorry

end Metro
