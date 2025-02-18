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
deriving DecidableEq --try to comment out

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
  apply IsTrip.change
  · exact two_le_length_ofDirection _
  · refine fun _ H ↦ ⟨D, H⟩


lemma isTrip_infix_pair {L : List Stations} {s t : Stations} (H  : [s, t] <:+: L) (hL : IsTrip L) :
    IsTrip [s, t] := by
  apply IsTrip.change (by simp)
  intro x y h_ne hxy
  replace hxy : [x, y] = [s, t] := IsInfix.eq_of_length hxy (by simp)
  replace hxy : x = s ∧ y = t := by simp_all
  by_cases hst : s = t
  · rw [hxy.1, hxy.2] at h_ne
    tauto
  · rw [← ne_eq] at hst
    rcases hL with ⟨_, h_abs⟩ | ⟨-, h⟩
    · obtain ⟨l₁, l₂, hl⟩ := H
      apply_fun List.length at hl
      simp [h_abs] at hl
      linarith
    · obtain ⟨D, hD⟩ := h hst H
      rw [← hxy.1, ← hxy.2] at hD
      exact ⟨D, hD⟩

lemma ne_nil_Trip {L : List Stations} (hL : IsTrip L) : L ≠ [] := by
  rcases hL with _ | H
  · simp_all
  · rw [← length_pos_iff_ne_nil]
    exact lt_of_lt_of_le two_pos H


lemma cons_isTrip {s : Stations} {L : List Stations} (hL : IsTrip L)
    (hs : IsTrip [s, L.head (ne_nil_Trip hL)]) : IsTrip (s :: L) := by
  rcases hs with _ | ⟨_, H⟩
  · simp_all
  have h_len : 1 ≤ L.length := by simp [Nat.one_le_iff_ne_zero, ne_nil_Trip hL]
  apply IsTrip.change (by simp [h_len])
  intro x y h_ne ⟨l₁, l₂, hl⟩
  by_cases h_nil : l₁ = []
  · rw [h_nil] at hl
    simp only [nil_append, cons_append, singleton_append, cons.injEq] at hl
    have hl' : L.head (ne_nil_Trip hL) = y := by
      simp_rw [← hl.2, head_cons]
    rw [hl.1, ← hl'] at h_ne ⊢
    exact H h_ne (infix_rfl)
  · have hl' : [x, y] ++ l₂ <:+: L := by
      rw [← head_cons_tail l₁ h_nil, cons_append, cons_append, cons_eq_cons] at hl
      refine ⟨l₁.tail, [], ?_⟩
      simp only [← hl.2, cons_append, singleton_append, append_nil, append_assoc]
    rcases hL with ⟨z, rfl⟩ | ⟨_, H'⟩
    · rw [← ne_eq, ← length_pos] at h_nil
      apply_fun List.length at hl
      simp_all only [ne_eq, length_singleton, le_refl, cons_append, singleton_append, head_cons,
        length_cons, append_assoc, length_append, not_false_eq_true]-- at hl
      linarith
    · apply H' h_ne
      apply IsInfix.trans _ hl'
      exact ⟨[], l₂, by simp⟩

lemma isTrip_infix {L : List Stations} {l : List Stations} (hl : l ≠ []) (hL : IsTrip L)
    (H : l <:+: L) : IsTrip l := by
  match l with
  | [s] => apply IsTrip.no_move s rfl
  | x :: xs =>
    by_cases h_ne : xs = []
    · rw [h_ne]
      apply IsTrip.no_move x rfl
    · have uno : xs <:+: L := by
        apply IsInfix.trans _ H
        refine ⟨[x], [], by simp⟩
      apply cons_isTrip
      · have tre : [x, xs.head h_ne] <:+: L := by
          apply IsInfix.trans _ H
          refine ⟨[], xs.tail, by simp⟩
        apply isTrip_infix_pair tre hL
      · apply isTrip_infix h_ne hL uno

lemma isTrip_tail {L : List Stations} (hL : IsTrip L) (h_len : 1 < L.length) : IsTrip (L.tail) := by
  apply isTrip_infix _ hL <| IsSuffix.isInfix <| tail_suffix L
  rw [← length_pos, length_tail]
  omega

lemma isTrip_trans {L M : List Stations} (hL : IsTrip L)  (hM : IsTrip M)
    (H : L.getLast (ne_nil_Trip hL) = M.head (ne_nil_Trip hM)) : IsTrip (L ++ M.tail) := by
  induction' L with s L h_ind
  · have := ne_nil_Trip hL
    tauto
  · by_cases L_ne : L = []
    · by_cases M_ne : 1 < M.length
      · rw [L_ne]
        simp
        apply cons_isTrip
        · simp_rw [L_ne] at H
          simp at H
          rw [H]
          apply isTrip_infix_pair _ hM
          · apply isTrip_infix _ hM
            · refine ⟨[M.head (ne_nil_Trip hM)], [], ?_⟩
              simp
            · apply ne_nil_of_length_pos
              simpa [length_tail, tsub_pos_iff_lt]
          · refine ⟨[], M.tail.tail, ?_⟩
            simp only [nil_append, cons_append, singleton_append, head_cons_tail]
      · simp at M_ne
        replace M_ne : M.length = 1 := by
          apply eq_of_le_of_not_lt M_ne
          simpa [Nat.lt_one_iff] using ne_nil_Trip hM
        rw [length_eq_one] at M_ne
        obtain ⟨_, rfl⟩ := M_ne
        simpa
    · show IsTrip ([s] ++ L ++ M.tail)
      have : 1 < (s :: L).length := by
        rw [length_cons]
        rw [← ne_eq, ← length_pos] at L_ne
        omega
      apply cons_isTrip _
      · apply isTrip_infix (by simp) hL
        refine ⟨[], L.tail, ?_⟩
        simp
        rw [head_append_of_ne_nil L_ne]
        exact head_cons_tail L L_ne
        · apply h_ind
          rw [← H]
          refine (getLast_cons L_ne).symm
          have := isTrip_tail hL this
          simpa

lemma isTrip_symm {L : List Stations} (hL : IsTrip L) : IsTrip L.reverse := by
  rcases hL with ⟨s, hs⟩ | ⟨_, H⟩
  · apply IsTrip.no_move s
    simp [hs]
  · apply IsTrip.change
    · simp_all
    intro s t h_ne hst
    specialize H h_ne.symm
    have := IsInfix.reverse hst
    simp at this
    obtain ⟨D, hD⟩ := H this
    use D.reverse
    rwa [Directions.reverse_eq, ← reverse_reverse [s, _], reverse_infix]


structure Trip (start arrival : Stations) where
  stops : List Stations
  permitted : IsTrip stops
  start : stops.head (ne_nil_Trip permitted) = start
  arrival : stops.getLast (ne_nil_Trip permitted) = arrival

def IsConnected : Stations → Stations → Prop := fun S A ↦ Nonempty (Trip S A)

example : IsConnected JeanMace SaxeGambetta := by
  use [JeanMace, SaxeGambetta]
  · refine IsTrip.change (by rfl) (fun _ hl ↦ ?_)
    refine ⟨B_SN, ⟨[], [PlaceGuichard, PartDieu], ?_⟩⟩
    simp only [nil_append, cons_append, singleton_append, cons.injEq, and_true,
      hl.eq_of_length (by simp)]
  all_goals rfl

example : IsConnected Ampere Guillotiere  := by
  use [Ampere, Bellecour, Guillotiere]
  apply isTrip_trans (L := [Ampere, Bellecour]) (M := [Bellecour, Guillotiere])
  · simp
  · apply isTrip_infix_pair (L := A_SN.1)
    · use [Perrache]
      simp
    · apply isTrip_ofDirection
  · apply isTrip_infix_pair (L := D_WE.1)
    apply IsSuffix.isInfix
    simp
    · apply isTrip_ofDirection
  · simp
  · simp


def Connected : Equivalence IsConnected where
  refl := by
    intro
    exact ⟨[_], IsTrip.no_move _ (rfl), head_cons, getLast_singleton _ (by simp)⟩
  symm := by
    intro s t ⟨trip, permitted, start, arrival⟩
    use trip.reverse
    · apply isTrip_symm permitted
    · rwa [head_reverse]
    · rwa [getLast_reverse]
  trans := by
    intro s t u ⟨trip_st, perm_st, start_st, arrival_st⟩ ⟨trip_tu, perm_tu, start_tu, arrival_tu⟩
    by_cases u_ne : trip_tu.length = 1
    · use trip_st
      obtain ⟨_, rfl⟩ := length_eq_one.mp u_ne
      simp at arrival_tu start_tu
      rw [arrival_st, ← arrival_tu, ← start_tu]
    use trip_st ++ (trip_tu.tail)
    · apply isTrip_trans (perm_st) (perm_tu)
      rw [arrival_st, start_tu]
    · rwa [head_append_of_ne_nil (ne_nil_Trip perm_st)]
    · rw [getLast_append_of_ne_nil]
      · simp_rw [drop_zero _ ▸ (tail_drop trip_tu 0), zero_add, getLast_drop, arrival_tu]
      · apply ne_nil_of_length_pos
        simp only [drop_one, length_tail, tsub_pos_iff_lt]
        have : 0 < trip_tu.length := by
          rw [length_pos]
          exact ne_nil_Trip perm_tu
        omega


def Terminus (D : Directions) : Stations := D.1.getLast (ne_nil_Direction _)

lemma Terminus_mem_line (D : Directions) : Terminus D ∈ D.1 := getLast_mem _

axiom IsTrip_circleLine : IsDirection
  [CroixPacquet, HotelDeVille, VieuxLyon, Perrache, Guillotiere, JeanMace, PartDieu]

abbrev CircleDirection : Directions := by
  use [CroixPacquet, HotelDeVille, VieuxLyon, Perrache, Guillotiere, JeanMace, PartDieu]
  exact IsTrip_circleLine

abbrev CircleLine : Lines := ⟦CircleDirection⟧

lemma IsConnected_within_Direction {s t : Stations} {D : Directions} (hst : s ∈ D.1 ∧ t ∈ D.1) :
    IsConnected s t := by
  obtain ⟨ns, ns_le, hns⟩ := List.getElem_of_mem hst.1
  obtain ⟨nt, nt_le, hnt⟩ := List.getElem_of_mem hst.2
  wlog h_wlog : ns ≤ nt
  · apply Connected.symm
    exact this hst.symm nt nt_le hnt ns ns_le hns (le_of_lt (lt_of_not_le h_wlog))
  by_cases h_eq : ns = nt
  · simp_all only [le_refl, and_self]
    apply Connected.refl
  set L := (D.1.drop ns).take (nt - ns + 1) with hL
  use L
  apply isTrip_infix _ (isTrip_ofDirection D)
  · apply IsInfix.trans (l₂ := drop ns D.1) (IsPrefix.isInfix ?_) (IsSuffix.isInfix ?_)
    apply take_prefix
    apply drop_suffix
  · apply ne_nil_of_length_pos
    rw [hL, length_take, length_drop]
    omega
  · simp_rw [hL]
    rwa [head_take, head_drop]
  · simp_rw [hL, take_drop, getLast_drop, getLast_eq_getElem, length_take]
    have : min (ns + (nt - ns + 1)) D.1.length - 1 = nt := by
      omega
    simp_rw [this]
    rwa [← getElem_take]
    omega

-- See at the end for a better solution once `Directions` is a `Fintype`
lemma exists_mem_Direction (s : Stations) : ∃ D : Directions, s ∈  D.1 := by
  induction s
  all_goals try {use B_SN ; simp_all}
  all_goals try {use A_NS ; simp_all}
  all_goals try {use C_SN ; simp_all}
  all_goals try {use D_EW; simp_all}

lemma IsConnected_to_Terminus (s : Stations) : ∃ D, IsConnected s (Terminus D) := by
  obtain ⟨D, hD⟩ := exists_mem_Direction s
  exact ⟨D, IsConnected_within_Direction ⟨hD, Terminus_mem_line _⟩⟩


-- See at the end for a better solution once `Directions` is a `Fintype`
lemma Directions.alternative (D : Directions) : D = A_SN ∨ D = B_SN ∨ D = C_SN ∨ D = D_EW ∨
    D.1.reverse = A_SN ∨ D.1.reverse = B_SN ∨ D.1.reverse = C_SN ∨ D.1.reverse = D_EW := by
  rcases D with ⟨D, hD⟩
  induction' hD with M hM H
  · simp
  · simp
  · simp
  · simp
  · simp at H ⊢
    tauto

  lemma Terminus_mem_CircleDirection (D : Directions) : Terminus D ∈ CircleDirection.1 := by
  have := Directions.alternative D
  rcases this with H | H | H | H | H | H | H | H
  · rw [H, Terminus]
    simp
  · rw [H, Terminus]
    simp
  · rw [H, Terminus]
    simp
  · rw [H, Terminus]
    simp
  · rw [← reverse_involutive A_SN.1, reverse_inj] at H
    simp [Terminus, H]
  · rw [← reverse_involutive B_SN.1, reverse_inj] at H
    simp [Terminus, H]
  · rw [← reverse_involutive C_SN.1, reverse_inj] at H
    simp [Terminus, H]
  · rw [← reverse_involutive D_EW.1, reverse_inj] at H
    simp [Terminus, H]


lemma IsConnected_Terminus {D₁ D₂ : Directions} : IsConnected (Terminus D₁) (Terminus D₂) := by
  apply IsConnected_within_Direction (D := CircleDirection)
  constructor <;>
  apply Terminus_mem_CircleDirection


lemma Everything_IsConnected (s t : Stations) : IsConnected s t := by
  obtain ⟨D1, h1⟩ := IsConnected_to_Terminus s
  obtain ⟨D2, h2⟩ := IsConnected_to_Terminus t
  apply Connected.trans h1
  exact Connected.trans IsConnected_Terminus (Connected.symm h2)

/- Let's provide a `Fintype` instance on `Distances` to make things computable-/

def Directions.listAll : List Directions := [A_SN, B_SN, C_SN, D_EW, A_SN.reverse, B_SN.reverse,
    C_SN.reverse, D_EW.reverse]

lemma mem_Directions_ListAll (D : Directions) : D ∈ Directions.listAll := by
  rcases D with ⟨D, hD⟩
  induction' hD with M hM H
  all_goals try decide
  fin_cases H <;> exact mem_of_elem_eq_true (by rfl)

instance : Fintype (Directions) := Fintype.ofList Directions.listAll mem_Directions_ListAll

lemma Terminus_mem_CircleDirection' (D : Directions) : Terminus D ∈ CircleDirection.1 := by
  have := mem_Directions_ListAll D
  fin_cases this <;> decide

lemma exists_mem_Direction' (s : Stations) : ∃ D : Directions, s ∈  D.1 := by
  induction s <;> decide

end Metro
