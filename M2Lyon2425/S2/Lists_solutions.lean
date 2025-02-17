import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Lemmas
import Mathlib.Data.NNReal.Basic

section Metro

/- ## Exercise
"In the attached file `PlanMetro.pdf` you find a reduced version of Lyon's subway network. I have
already defined the type of `Stations`.

1. Find a way to formalize lines (both ordered and non-ordered), and the notion for two stations of
being connected by a path.

2. Prove that being connected is an equivalence relation.

3. Prove that if we add a "circle line" connecting all terminus', then every two stations become
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
deriving DecidableEq

open Stations List

inductive IsDirection : List Stations → Prop
  | a_SN : IsDirection [Perrache, Ampere, Bellecour, Cordeliers, HotelDeVille]
  | b_SN : IsDirection [JeanMace, SaxeGambetta, PlaceGuichard, PartDieu]
  | c_SN : IsDirection [HotelDeVille, CroixPacquet]
  | d_EW : IsDirection [Guillotiere, Bellecour, VieuxLyon]
  | back {L : List Stations} : IsDirection L → IsDirection L.reverse


abbrev Directions := {D : List Stations // IsDirection D}

lemma Direction_two_le_length (D : Directions) : 2 ≤ D.1.length := by
  rcases D with ⟨L, hL⟩
  induction' hL with _ _ h_ind
  all_goals simp
  apply h_ind

lemma ne_nil_D (D : Directions) : D.1 ≠ [] := by
  apply ne_nil_of_length_pos
  linarith [Direction_two_le_length D]


def Directions.reverse : Directions → Directions :=
  fun D ↦ ⟨D.1.reverse, IsDirection.back D.2⟩

@[simp]
lemma Directions.reverse_eq (D : Directions) : D.reverse.1 = D.1.reverse := rfl

abbrev A_SN : Directions := ⟨_, IsDirection.a_SN⟩

abbrev A_NS : Directions := ⟨_, IsDirection.back IsDirection.a_SN⟩

abbrev B_SN : Directions := ⟨_, IsDirection.b_SN⟩

abbrev B_NS : Directions := ⟨_, IsDirection.back IsDirection.b_SN⟩

abbrev C_SN : Directions := ⟨_, IsDirection.c_SN⟩

abbrev C_NS : Directions := ⟨_, IsDirection.back IsDirection.c_SN⟩

abbrev D_EW : Directions := ⟨_, IsDirection.d_EW⟩

abbrev D_WE : Directions := ⟨_, IsDirection.back IsDirection.d_EW⟩


instance : Fintype (Stations) := by
  apply Fintype.ofList
      [JeanMace, SaxeGambetta, PlaceGuichard, PartDieu, HotelDeVille, CroixPacquet, Perrache,
  Ampere, Bellecour, Cordeliers, Guillotiere, VieuxLyon]
  intro s
  cases s
  all_goals {simp}

instance : DecidableEq Directions := Subtype.instDecidableEq

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

abbrev A : Lines := Quotient.mk'' A_NS
abbrev A'' : Lines := ⟦A_NS⟧
abbrev A' : Lines := Quotient.mk'' A_SN
abbrev A''' : Lines := Quotient.mk'' A_NS

example : A = A' := by
  rw [Quotient.eq'']
  constructor
  rfl


inductive IsQ (L : List Stations) : Prop
  | nom (s : Stations) (_ : L = [s]) : IsQ L
  | two : 2 ≤ L.length → (∀ {s t : Stations} (_ : s ≠ t), [s, t] <:+: L → ∃ D : Directions,
    [s,t] <:+: D.1) → IsQ L


lemma isQ_D (D : Directions) : IsQ D.1 := by
  apply IsQ.two
  · exact Direction_two_le_length _
  · refine fun _ H ↦ ⟨D, H⟩


lemma isQ_infix_pair {L : List Stations} {s t : Stations} (H  : [s, t] <:+: L) (hL : IsQ L) :
    IsQ [s, t] := by
  apply IsQ.two (by simp)
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

lemma not_nil_Q {L : List Stations} (hL : IsQ L) : L ≠ [] := by
  rcases hL with _ | H
  · simp_all
  · rw [← length_pos_iff_ne_nil]
    exact lt_of_lt_of_le two_pos H

lemma length_pos_Q {L : List Stations} (hL : IsQ L) : 0 < L.length := by
  rw [length_pos]
  exact not_nil_Q hL


lemma isQ_left {s : Stations} {L : List Stations} (hL : IsQ L)
    (hs : IsQ [s, L.head (not_nil_Q hL)]) : IsQ (s :: L) := by
  rcases hs with _ | ⟨_, H⟩
  · simp_all
  have h_len : 1 ≤ L.length := by simp [Nat.one_le_iff_ne_zero, not_nil_Q hL]
  apply IsQ.two (by simp [h_len])
  intro x y h_ne ⟨l₁, l₂, hl⟩
  by_cases h_nil : l₁ = []
  · rw [h_nil] at hl
    simp only [nil_append, cons_append, singleton_append, cons.injEq] at hl
    have hl' : L.head (not_nil_Q hL) = y := by
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

lemma isQ_infix {L : List Stations} {l : List Stations} (hl : l ≠ []) (hL : IsQ L) (H : l <:+: L) :
    IsQ l := by
  match l with
  | [s] => apply IsQ.nom s rfl
  | x :: xs =>
    by_cases h_ne : xs = []
    · rw [h_ne]
      apply IsQ.nom x rfl
    · have uno : xs <:+: L := by
        apply IsInfix.trans _ H
        refine ⟨[x], [], by simp⟩
      apply isQ_left
      · have tre : [x, xs.head h_ne] <:+: L := by
          apply IsInfix.trans _ H
          refine ⟨[], xs.tail, by simp⟩
        apply isQ_infix_pair tre hL
      · apply isQ_infix h_ne hL uno

lemma isQ_tail {L : List Stations} (hL : IsQ L) (h_len : 1 < L.length) : IsQ (L.tail) := by
  apply isQ_infix _ hL <| IsSuffix.isInfix <| tail_suffix L
  rw [← length_pos, length_tail]
  omega

lemma isQ_trans {L M : List Stations} (hL : IsQ L)  (hM : IsQ M)
    (H : L.getLast (not_nil_Q hL) = M.head (not_nil_Q hM)) : IsQ (L ++ M.tail) := by
  induction' L with s L h_ind
  · have := not_nil_Q hL
    tauto
  · by_cases L_ne : L = []
    · by_cases M_ne : 1 < M.length
      · rw [L_ne]
        simp
        apply isQ_left
        · simp_rw [L_ne] at H
          simp at H
          rw [H]
          apply isQ_infix_pair _ hM
          · apply isQ_infix _ hM
            · refine ⟨[M.head (not_nil_Q hM)], [], ?_⟩
              simp
            · apply ne_nil_of_length_pos
              simpa [length_tail, tsub_pos_iff_lt]
          · refine ⟨[], M.tail.tail, ?_⟩
            simp only [nil_append, cons_append, singleton_append, head_cons_tail]
      · simp at M_ne
        replace M_ne : M.length = 1 := by
          apply eq_of_le_of_not_lt M_ne
          simpa [Nat.lt_one_iff] using not_nil_Q hM
        rw [length_eq_one] at M_ne
        obtain ⟨_, rfl⟩ := M_ne
        simpa
    · show IsQ ([s] ++ L ++ M.tail)
      have : 1 < (s :: L).length := by
        rw [length_cons]
        rw [← ne_eq, ← length_pos] at L_ne
        omega
      apply isQ_left _
      · apply isQ_infix (by simp) hL
        refine ⟨[], L.tail, ?_⟩
        simp
        rw [head_append_of_ne_nil L_ne]
        exact head_cons_tail L L_ne
        · apply h_ind
          rw [← H]
          refine (getLast_cons L_ne).symm
          have := isQ_tail hL this
          simpa

lemma isQ_symm {L : List Stations} (hL : IsQ L) : IsQ L.reverse := by
  rcases hL with ⟨s, hs⟩ | ⟨_, H⟩
  · apply IsQ.nom s
    simp [hs]
  · apply IsQ.two
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
  permitted : IsQ stops
  start : stops.head (not_nil_Q permitted) = start
  arrival : stops.getLast (not_nil_Q permitted) = arrival

def Connected : Stations → Stations → Prop := fun S A ↦ Nonempty (Trip S A)

example : Connected JeanMace SaxeGambetta := by
  use [JeanMace, SaxeGambetta]
  · refine IsQ.two (by rfl) (fun _ hl ↦ ?_)
    refine ⟨B_SN, ⟨[], [PlaceGuichard, PartDieu], ?_⟩⟩
    simp only [nil_append, cons_append, singleton_append, cons.injEq, and_true,
      hl.eq_of_length (by simp)]
  all_goals rfl

example : Connected Ampere Guillotiere  := by
  use [Ampere, Bellecour, Guillotiere]
  apply isQ_trans (L := [Ampere, Bellecour]) (M := [Bellecour, Guillotiere])
  · simp
  · apply isQ_infix_pair (L := A_SN.1)
    · use [Perrache]
      simp
    · apply isQ_D
  · apply isQ_infix_pair (L := D_WE.1)
    apply IsSuffix.isInfix
    simp
    · apply isQ_D
  · simp
  · simp


lemma exists_Direction (s : Stations) : ∃ D : Directions, s ∈  D.1 := by
  induction s
  all_goals try {use B_SN ; simp_all}
  all_goals try {use A_NS ; simp_all}
  all_goals try {use C_SN ; simp_all}
  all_goals try {use D_EW; simp_all}


def ConnectedEquiv : Equivalence Connected where
  refl := by
    intro
    exact ⟨[_], IsQ.nom _ (rfl), head_cons, getLast_singleton _ (by simp)⟩
  symm := by
    intro s t ⟨trip, permitted, start, arrival⟩
    use trip.reverse
    · apply isQ_symm permitted
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
    · apply isQ_trans (perm_st) (perm_tu)
      rw [arrival_st, start_tu]
    · rwa [head_append_of_ne_nil (not_nil_Q perm_st)]
    · rw [getLast_append_of_ne_nil]
      · simp_rw [drop_zero _ ▸ (tail_drop trip_tu 0), zero_add, getLast_drop, arrival_tu]
      · apply ne_nil_of_length_pos
        simp only [drop_one, length_tail, tsub_pos_iff_lt]
        have : 0 < trip_tu.length := by
          rw [length_pos]
          exact not_nil_Q perm_tu
        omega


def terminus (D : Directions) : Stations := D.1.getLast (ne_nil_D _)

lemma mem_line_terminus (D : Directions) : terminus D ∈ D.1 := getLast_mem _

axiom Q_circleLine : IsDirection
  [CroixPacquet, HotelDeVille, VieuxLyon, Perrache, Guillotiere, JeanMace, PartDieu]

abbrev CircleLine : Directions := by
  use [CroixPacquet, HotelDeVille, VieuxLyon, Perrache, Guillotiere, JeanMace, PartDieu]
  exact Q_circleLine


lemma connected_with_D {s t : Stations} {D : Directions} (hst : s ∈ D.1 ∧ t ∈ D.1) :
    Connected s t := by
  obtain ⟨ns, ns_le, hns⟩ := List.getElem_of_mem hst.1
  obtain ⟨nt, nt_le, hnt⟩ := List.getElem_of_mem hst.2
  wlog h_wlog : ns ≤ nt
  · apply ConnectedEquiv.symm
    exact this hst.symm nt nt_le hnt ns ns_le hns (le_of_lt (lt_of_not_le h_wlog))
  by_cases h_eq : ns = nt
  · simp_all only [le_refl, and_self]
    apply ConnectedEquiv.refl
  set L := (D.1.drop ns).take (nt - ns + 1) with hL
  use L
  apply isQ_infix _ (isQ_D D)
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


lemma connected_to_terminus (s : Stations) : ∃ D, Connected s (terminus D) := by
  obtain ⟨D, hD⟩ := exists_Direction s
  exact ⟨D, connected_with_D ⟨hD, mem_line_terminus _⟩⟩

lemma alternative (D : Directions) : D = A_SN ∨ D = B_SN ∨ D = C_SN ∨ D = D_EW ∨
    D.1.reverse = A_SN ∨ D.1.reverse = B_SN ∨ D.1.reverse = C_SN ∨ D.1.reverse = D_EW := by
  rcases D with ⟨D, hD⟩
  induction' hD with M hM H
  · simp
  · simp
  · simp
  · simp
  · simp at H ⊢
    tauto

#help tactic nth

lemma mem_terminus_CircleLine (D : Directions) : terminus D ∈ CircleLine.1 := by
  have := alternative D
  rcases this with H | H | H | H | H | H | H | H
  · rw [H, terminus]
    simp
  · rw [H, terminus]
    simp
  · rw [H, terminus]
    simp
  · rw [H, terminus]
    simp
  · rw [← reverse_involutive A_SN.1, reverse_inj] at H
    simp [terminus, H]
  · rw [← reverse_involutive B_SN.1, reverse_inj] at H
    simp [terminus, H]
  · rw [← reverse_involutive C_SN.1, reverse_inj] at H
    simp [terminus, H]
  · rw [← reverse_involutive D_EW.1, reverse_inj] at H
    simp [terminus, H]


lemma Terminus_Connected {D₁ D₂ : Directions} : Connected (terminus D₁) (terminus D₂) := by
  apply connected_with_D (D := CircleLine)
  constructor <;>
  apply mem_terminus_CircleLine


lemma Everything_Connected (s t : Stations) : Connected s t := by
  obtain ⟨D1, h1⟩ := connected_to_terminus s
  obtain ⟨D2, h2⟩ := connected_to_terminus t
  apply ConnectedEquiv.trans h1
  exact ConnectedEquiv.trans Terminus_Connected (ConnectedEquiv.symm h2)


end Metro
