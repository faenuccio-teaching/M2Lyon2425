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
fun D ↦ ⟨D.1.reverse, IsDirection.back D.2⟩

@[simp]
lemma Directions.reverse_eq (D : Directions) : D.reverse.1 = D.1.reverse := rfl

lemma two_le_length_ofDirection (D : Directions) : 2 ≤ D.1.length := by
  rcases D with ⟨L, hL⟩
  induction' hL with _ _ h_ind
  all_goals simp
  apply h_ind

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
  r := fun L M ↦ L.1 = M.1.reverse ∨ L.1 = M.1
  iseqv := by
    constructor
    · tauto
    · intros
      rw [← reverse_eq_iff]
      tauto
    · intro _ _ _
      rintro (h1 | h1) (_ | _) <;> simp_all

def Lines := Quotient Directions.Setoid

-- Several ways to write a line
abbrev A : Lines := Quotient.mk'' A_NS
abbrev A'' : Lines := ⟦A_NS⟧
abbrev A' : Lines := Quotient.mk'' A_SN
abbrev A''' : Lines := Quotient.mk'' A_NS

example : A = A' := by
  rw [Quotient.eq'']
  constructor
  rfl

inductive IsTrip (L : List Stations) : Prop
  | no_move (s : Stations) (_ : L = [s]) : IsTrip L
  | change : 2 ≤ L.length → (∀ {s t : Stations} (_ : s ≠ t), [s, t] <:+: L → ∃ D : Directions,
    [s,t] <:+: D.1) → IsTrip L


lemma isTrip_ofDirection (D : Directions) : IsTrip D.1 := by

  sorry

lemma isTrip_ofDirection' (D : Directions) : IsTrip D.1 := by
  rcases D with ⟨l, hl⟩
  cases l with
  | nil =>
    exfalso
    apply ne_nil_Direction ⟨_, hl⟩
    rfl
  | cons h t =>
    cases t with
    | nil =>
      exact IsTrip.no_move h (by rfl)
    | cons th tt =>
      refine IsTrip.change ?_ ?_
      · simp
      · intro s t hdiff hstsuite

        sorry


lemma isTrip_infix_pair {L : List Stations} {s t : Stations} (H  : [s, t] <:+: L) (hL : IsTrip L) :
    IsTrip [s, t] := by sorry

lemma ne_nil_Trip {L : List Stations} (hL : IsTrip L) : L ≠ [] := by sorry


lemma cons_isTrip {s : Stations} {L : List Stations} (hL : IsTrip L)
  (hs : IsTrip [s, L.head (ne_nil_Trip hL)]) : IsTrip (s :: L) := by
    rcases hs with _ | ⟨_, H⟩
    · simp_all
    · apply IsTrip.change (by sorry)
      sorry

lemma isTrip_infix {L : List Stations} {l : List Stations} (hl : l ≠ []) (hL : IsTrip L)
    (H : l <:+: L) : IsTrip l := by
  sorry

lemma isTrip_tail {L : List Stations} (hL : IsTrip L) (h_len : 1 < L.length) : IsTrip (L.tail) := by
  apply isTrip_infix _ hL <| IsSuffix.isInfix <| tail_suffix L
  rw [← length_pos, length_tail]
  omega

lemma isTrip_trans {L M : List Stations} (hL : IsTrip L)  (hM : IsTrip M)
    (H : L.getLast (ne_nil_Trip hL) = M.head (ne_nil_Trip hM)) : IsTrip (L ++ M.tail) := by
  sorry

lemma isTrip_symm {L : List Stations} (hL : IsTrip L) : IsTrip L.reverse := by
  sorry


structure Trip (start arrival : Stations) where
  stops : List Stations
  permitted : IsTrip stops
  start : stops.head (ne_nil_Trip permitted) = start
  arrival : stops.getLast (ne_nil_Trip permitted) = arrival

def IsConnected : Stations → Stations → Prop := sorry

example : IsConnected JeanMace SaxeGambetta := by
  sorry

example : IsConnected Ampere Guillotiere  := by
  sorry

def Connected : Equivalence IsConnected := sorry

end Metro
