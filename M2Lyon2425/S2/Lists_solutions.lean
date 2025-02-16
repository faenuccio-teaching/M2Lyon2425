import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Lemmas
import Mathlib.Data.NNReal.Basic

section Metro

/- ## Exercise 1
"In the attached file `PlanMetro.pdf` you find a reduced version of Lyon's subway network. I have
already defined the type of `Stations`.

1. Find a way to formalize lines (both ordered and non-ordered), and the notion for two stations of
being connected by a path.

2. Prove that being connected is an equivalence relation.

3. Prove that if we add a "circle line" connecting all terminus', then every two stations become
connected.

4. Prove that in the above configuration with a "circle line" every trip requires of at most two
changes."
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

instance : Inhabited Stations := ⟨Stations.PartDieu⟩

open Stations List /- Classical -/

inductive IsDirection : List Stations → Prop
  | c_SN : IsDirection [HotelDeVille, CroixPacquet]
  | b_SN : IsDirection [JeanMace, SaxeGambetta, PlaceGuichard, PartDieu]
  | a_SN : IsDirection [Perrache, Ampere, Bellecour, Cordeliers, HotelDeVille]
  | d_EW : IsDirection [Guillotiere, Bellecour, VieuxLyon]
  | back {L : List Stations} : IsDirection L → IsDirection L.reverse

structure Directions where
  stops : List Stations
  isDir : IsDirection stops

lemma Direction_two_le_length (D : Directions) : 2 ≤ D.1.length := by
  rcases D with ⟨L, hL⟩
  induction' hL with _ _ h_ind
  all_goals simp
  apply h_ind

lemma ne_nil_D (D : Directions) : D.1 ≠ [] := by
  apply ne_nil_of_length_pos
  linarith [Direction_two_le_length D]


def Directions.reverse : Directions → Directions :=
  fun D ↦ ⟨D.stops.reverse, IsDirection.back D.isDir⟩

@[simp]
lemma Directions.reverse_eq (D : Directions) : D.reverse.1 = D.1.reverse := rfl

abbrev A_SN : Directions where
  stops := _
  isDir := IsDirection.a_SN

abbrev A_NS : Directions where
  stops := _
  isDir := IsDirection.back IsDirection.a_SN

abbrev B_SN : Directions where
  stops := _
  isDir := IsDirection.b_SN

abbrev B_NS : Directions where
  stops := _
  isDir := IsDirection.back IsDirection.b_SN

abbrev C_SN : Directions where
  stops := _
  isDir := IsDirection.c_SN

abbrev C_NS : Directions where
  stops := _
  isDir := IsDirection.back IsDirection.c_SN

abbrev D_EW : Directions where
  stops := _
  isDir := IsDirection.d_EW

abbrev D_WE : Directions where
  stops := _
  isDir := IsDirection.back IsDirection.d_EW

-- instance DecidableEq Stations :=
--   fun s t =>
--   match decEq with
--   |


instance : Fintype (Stations) := by
  · apply Fintype.ofList
      [JeanMace, SaxeGambetta, PlaceGuichard, PartDieu, HotelDeVille, CroixPacquet, Perrache,
    Ampere, Bellecour, Cordeliers, Guillotiere, VieuxLyon]
    intro s
    cases s
    all_goals {simp}


-- instance : Fintype (Directions) := by
--   fconstructor
--   · apply Finset


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

/-
inductive IsPermitted : Prop
| (S : Stat) => IsPerm [S]
| S , M => IsPerm M=> exist D, [M.last, S] ≤ D=> IsPerm M ++ S
| the same with M.head

structure Trip where
L : List Stat
perm : IsPermittes L

-/


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
  permitted : IsQ stops-- not_empty : stops ≠ []
  start : stops.head (not_nil_Q permitted) = start
  arrival : stops.getLast (not_nil_Q permitted) = arrival

def Connected : Stations → Stations → Prop := fun S A ↦ Nonempty (Trip S A)

example : Connected JeanMace SaxeGambetta := by-- sorry
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


example : ¬ Connected VieuxLyon PartDieu := by sorry --use `injection` tactic?

lemma exists_Direction (s : Stations) : ∃ D : Directions, s ∈  D.1 := by
  induction s
  all_goals try {use B_SN ; simp_all}
  all_goals try {use A_NS ; simp_all}
  all_goals try {use C_SN ; simp_all}
  all_goals try {use D_EW; simp_all}

-- lemma exists_goodDirection (s : Stations) : ∃ D : GoodDirections, s ∈  D.1 := by
--   induction s
--   -- decide
--   -- -- induction s
--   all_goals try {use ⟨_, b_SN⟩ ; simp_all}
--   all_goals try {use A_NS ; simp_all}
--   all_goals try {use C_SN ; simp_all}
--   all_goals try {use D_EW; simp_all}

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

lemma mem_terminus (D : Directions) : terminus D ∈ D.1 := getLast_mem _

axiom Q_circleLine : IsDirection
  [CroixPacquet, HotelDeVille, VieuxLyon, Perrache, Guillotiere, JeanMace, PartDieu]

abbrev CircleLine : Directions where
  stops := [CroixPacquet, HotelDeVille, VieuxLyon, Perrache, Guillotiere, JeanMace, PartDieu]
  isDir := Q_circleLine


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
    have : min (ns + (nt - ns + 1)) D.stops.length - 1 = nt := by
      omega
    simp_rw [this]
    rwa [← getElem_take]
    omega


lemma connected_to_terminus (s : Stations) : ∃ D, Connected s (terminus D) := by
  obtain ⟨D, hD⟩ := exists_Direction s
  exact ⟨D, connected_with_D ⟨hD, mem_terminus _⟩⟩

-- #exit

--   obtain ⟨n, hn⟩ := List.get_of_mem hD
--   use D
--   set L := D.1.drop n with hL
--   use L
--   · by_cases hn₀ : n < D.1.length - 1
--     · apply IsQ.two
--       · rw [hL, length_drop]
--         omega
--       · rintro s t - ⟨l₁, l₂, hlD⟩
--         use D
--         let M := D.1.take n
--         have : M ++ L = D.1 := by apply take_append_drop
--         use M ++ l₁
--         use l₂
--         rwa [append_assoc, append_assoc, ← append_assoc l₁ _ _, hlD]
--     · replace hn₀ : n = D.1.length - 1 := by
--         apply eq_of_le_of_le
--         · have := n.2
--           rw [Nat.le_sub_one_iff_lt]
--           exact this
--           omega
--         · rw [not_lt] at hn₀
--           exact hn₀
--       apply isQ_infix _ (isQ_D D)
--       · apply IsSuffix.isInfix
--         rw [hL]
--         apply drop_suffix
--       · apply ne_nil_of_length_pos
--         rw [hL]
--         rw [length_drop]
--         omega
--   · simp_rw [hL]
--     rw [List.head_drop]
--     exact hn
--   · rw [List.getLast_drop]
--     rfl


lemma Terminus_Connected {D₁ D₂ : Directions} {s t : Stations} (hs : s = terminus D₁)
    (ht : t = terminus D₂) : Connected s t := by
  apply connected_with_D (D := CircleLine)
  constructor
  · rw [terminus] at ht hs
    cases hs
    rw [CircleLine]
    simp
    use C_SN
    -- all_goals try {use A_NS ; simp_all}
    -- all_goals try {use B_NS ; simp_all}
    -- all_goals try {use C_NS ; simp_all}
    -- all_goals try {use D_NS ; simp_all}

  -- · simp
  -- · simp_all
  --   rcases D₁ with ⟨D, hD⟩

    -- decide
  -- · rcases ht with ⟨D, hD⟩
  --   cases CircleLine

    -- cases hs
  -- · cases hs



lemma Everything_Connected (s t : Stations) : Connected s t := by sorry
  -- obtain ⟨D1, h1⟩ := connected_to_terminus s
  -- obtain ⟨D2, h2⟩ := connected_to_terminus t
  -- use D1.1 ++ D2.1
  -- apply IsQ_trans
  -- · sorry
  -- · sorry





#synth DecidableRel (LT.lt : ℤ → ℤ → Prop)

instance : DecidableRel Connected := sorry

def GoodDirections := {D : List Stations // IsDirection D}



#exit




inductive IsPermitted : List Stations → Prop
  | no_move (S : Stations) : IsPermitted [S]
  -- | after_last (S : Stations) (M : List Stations) (hM : M ≠ []) (D : Directions) :
  --     IsPermitted M → (M.getLast hM /- hM -/) :: [S] <:+: D.1 → IsPermitted (M ++ [S]) -- M ++ [S] is `simp` normal form for `M.concat S`
  | before_head (S : Stations) (M : List Stations) (hM : M ≠ []) (D : Directions) :
      IsPermitted M → S :: [M.head hM] <:+: D.1 → IsPermitted (S :: M)


lemma isPermitted.ne_nil {L : List Stations} (hL : IsPermitted L) : L ≠ [] := by
  cases hL <;> simp



inductive IsP : List Stations → Prop
  | no_move (S : Stations) : IsP [S]
  | after_last (M N : List Stations) (D : Directions)  (M_ne : M ≠ []) (N_ne : N ≠ []) :
      IsP M → IsP N → (M.getLast M_ne) :: [N.head N_ne] <:+: D.1 → IsP (M ++ N) -- M ++ [S] is `simp` normal form for `M.concat S`

lemma foo {L : List Stations} (hL : IsPermitted L) : IsP L := by
  rcases hL with _ | ⟨s, M, hM, D, H⟩
  · exact IsP.no_move _
  · apply IsP.after_last _ _ D (isPermitted.ne_nil H)
    · apply foo H
    · exact IsP.no_move _
    · simpa
    · simp
  termination_by L.length
    -- · sorry

lemma bar {L : List Stations} (hL : IsP L) : IsPermitted L := by
  rcases hL with _ | ⟨M, N, D, M_ne, N_ne, hM⟩
  · exact IsPermitted.no_move _
  · match N with
    | [s] =>
      apply IsPermitted.after_last
      apply bar hM
      assumption
    | s :: xs =>
      by_cases hxs : xs = []
      · rw [hxs]
        apply IsPermitted.after_last s M M_ne D (bar hM)
        assumption
      · have h_ex : M ++ s :: xs = M ++ ([s]) ++ [(xs.getLast hxs)] := sorry
        rw [h_ex]
        apply IsPermitted.after_last (xs.getLast hxs) (M ++ [s]) (by simp) D
        · apply IsPermitted.after_last s M M_ne D (bar hM)
          sorry
        · sorry
      termination_by L.length
      -- termination_by M.length
      -- rw [append_cons
      -- rw [append_cons]
      -- rw [← concat_append]
      -- apply IsPermitted.before_head
  -- termination_by L.length



-- inductive IsP : List Stations → Prop
--   | no_move (S : Stations) : IsP [S]
--   | findD (L : List Stations) (D : Directions) (s t : Stations) :
--     [s, t] <:+: L → [s, t] <:+: D.1 → IsP L

-- lemma empty_not_isP : ¬ IsP [] := by
--   intro habs
  -- cases habs
  -- cases habs
  -- aesop

open IsP

lemma isP_ne_nil {L : List Stations} (hL : IsP L) : L ≠ [] := by
  cases hL <;> simp_all

lemma isP_trans {M N : List Stations} (hM : IsP M) (hN : IsP N) (D : Directions) :
    (M.getLast (isP_ne_nil hM)) :: [N.head (isP_ne_nil hN)] <:+: D.1 → IsP (M ++ N) := by
  intro H
  apply after_last _ _ D (isP_ne_nil hM) (isP_ne_nil hN) hM hN
  exact H

lemma iP_refl (s : Stations) : IsP [s] := no_move _

-- lemma isP_symm {L : List Stations} (hL : IsP L) : IsP L.reverse := by
--   rcases hL with s | ⟨M, N, D, M_me, N_ne, hM, hN, H⟩
--   · simp
--     exact no_move _
--   · simp
--     induction' M with x xs h_ind_M
--     · simp
--       induction' N with y yx h_ind_N
--       · simpa
--       · simp
--         exfalso
--         apply M_me
--         rfl
--     · have N_e : N.reverse ≠ [] := sorry
--       have xx_e : (x :: xs).reverse ≠ [] := sorry
--       apply after_last _ _ D.reverse N_e xx_e
--       · apply isP_symm hN
--       · apply isP_symm hM
--       · simp
--         sorry








    -- have h1 : M.length < (N.reverse ++ M.reverse).length := sorry
    -- have h2 : N.length < (N.reverse ++ M.reverse).length := sorry
    -- apply after_last N.reverse M.reverse D.reverse ?_ ?_
    -- apply isP_symm hN
    -- apply isP_symm hM
    -- sorry
    -- simpa [reverse_eq_nil_iff] using isP_ne_nil hN
    -- simpa [reverse_eq_nil_iff] using isP_ne_nil hM
  -- termination_by (N.reverse ++ M.reverse).length



-- lemma refl_isP (s : Stations) : IsP [s] := no_move s

-- lemma refl_isP' (s : Stations) : IsP [s, s] := by
--   cases s
--   · apply findD _ _ JeanMace JeanMace
--     · simp
--     ·

-- lemma trans_isP {L M : List Stations} (hL : IsP L) (hM : IsP M)
--     (H : L.head (isP_not_empty hL) = M.getLast (isP_not_empty hM)) : IsP (L ++ M) := by
--   rcases hM with s | as
--   · rcases hL with x | ax
--     simp at H
--     rw [H]
--     simp




open IsPermitted

lemma IsPermitted_rfl (S : Stations) : IsPermitted [S] := no_move S

-- lemma IsPermitted_symm {L : List Stations} (hL : IsPermitted L) : IsPermitted L.reverse := by
--   rcases hL with _ | ⟨S, M, D, hM, hDM⟩ | ⟨S, M, D, hM, hDM⟩
--   · simpa using IsPermitted.no_move _
--   · simp only [reverse_append, reverse_cons, reverse_nil, nil_append, singleton_append]
--     apply before_head _ _ D.reverse
--     · apply IsPermitted_symm hM
--     · simp
--       rwa [← List.reverse_infix, reverse_reverse, ← getLastD_eq_getLast?]
--   · rw [reverse_cons/- , ← concat_eq_append -/]
--     apply IsPermitted.after_last _ _ D.reverse
--     · apply IsPermitted_symm hM
--     · rw [← List.reverse_infix, /- reverse_reverse, -/ getLastD_eq_getLast?]
--       simp
--       convert hDM

--   termination_by L.length
open isPermitted

lemma two_append {α : Type} (x y : α) (L M : List α) (hL : L ≠ []) (hM : M ≠ []) (H : [x, y] <:+: L ++ M) :
    [x, y] <:+: M ∨ [x, y] <:+: L ∨ [x] <:+ L ∧ [y] <+: M := by sorry
  -- obtain ⟨l₁, l₂, H⟩ := H
  -- rw [append_eq_append_iff] at H
  -- rcases H with ⟨l₃, H1, H2⟩ | ⟨l₃, H1, H2⟩
  -- · right
  --   left
  --   use l₁
  --   use l₃
  --   exact H1.symm
  -- · rw [append_eq_append_iff] at H1
  --   rcases H1 with ⟨l₄, h1, h2⟩ | ⟨l₄, _, H⟩
  --   · right
  --     right
  --     sorry


    -- by_cases h_emp : l₄ = []
    -- · sorry
    -- · right
    --   right
    --   constructor
    --   · replace h2 : [x] <+: l₄ := by --[x, y] = l₄ ++ l₃
    --       rw [cons_eq_append] at h2
    --       simp only [h_emp, false_and, false_or] at h2
    --       obtain ⟨l₇, h7, h8⟩ := h2
    --       by_cases H8 : l₇ = []
    --       · use l₇
    --         rw [H8, append_nil]
    --         rw [H8] at h7
    --         exact h7.symm
    --       · use l₇
    --         sorry
    --     obtain ⟨l₅, h⟩ := h2
    --     rw [← h] at h1
    --     rw [← append_assoc] at h1
    --     use l₁ ++ l₅
    --     exact h1.symm
    --   · sorry

    -- · rw [H] at H2
    --   left
    --   use l₄
    --   use l₂
    --   exact H2.symm


lemma isPermitted_of_subDir (D : Directions) (L : List Stations) (L_ne : L ≠ []) (h : L <:+: D.1) :
    IsPermitted L := by
  match L with
  | [s] => exact IsPermitted.no_move _
  | s :: xs =>
    by_cases hxs : xs = []
    · rw [hxs]
      exact IsPermitted.no_move _
    · apply IsPermitted.before_head s xs hxs D _
      rw [infix_iff_prefix_suffix] at h ⊢
      obtain ⟨t, ht1, ht2⟩ := h
      refine ⟨t, ?_, ht2⟩
      apply IsPrefix.trans _ ht1
      · simp
        convert List.take_prefix 1 xs using 1
        cases xs
        · simp
          tauto
        · simp only [head_cons, take_succ_cons, take_zero]
      · have : xs <:+: D.1 := by
          obtain ⟨l₁, l₂, H⟩ := h
          use l₁ ++ [s]
          use l₂
          rw [← H, append_assoc, append_assoc, append_assoc, append_right_inj, ← append_assoc,
            append_left_inj]
          rfl
        exact isPermitted_of_subDir D xs hxs this


          -- use xs ++ l₂

      -- · simp only [cons_prefix_cons, true_and]
      --   apply prefix_me

      -- have : [s, xs.head hxs] = s :: [xs.head hxs] := rfl
      -- rw [this]

lemma IsPermitted_trans (M N : List Stations) (hM : IsPermitted M) (hN : IsPermitted N)
    (D : Directions) (h : M.getLast (ne_nil hM) :: [N.head (ne_nil hN)] <:+: D.1) :
    IsPermitted (M ++ N) := by
  match M with
  | [s] =>
    apply IsPermitted.before_head _ _ (isPermitted.ne_nil hN) D hN
    exact h
  | s :: xs =>
    rcases hM with _ | ⟨_, _, xs_ne, D₀, h_xs, h₀⟩
    · apply IsPermitted.before_head
      simp
      exact hN
      simp
      simp at h
      exact h
      simp
      exact isPermitted.ne_nil hN
    match N with
    | [t] =>
        apply IsPermitted.before_head
        swap
        · convert h₀ using 1
          simp
          exact head_append_of_ne_nil xs_ne
        · sorry
    | t :: xt => sorry


    -- · apply IsPermitted_trans
    --   · exact h
    --   · apply IsPermitted.before_head _ _ _ _ h_xs h₀
    --   · exact hN











#exit
structure Trip (start arrival : Stations) where
  stops : List Stations
  not_empty : stops ≠ []
  start : stops.head not_empty = start
  arrival : stops.getLast not_empty = arrival
  -- nodup : stops.Nodup
  connection (l : List Stations) : IsInfix l stops → l.length = 2 →
    ∃ D : Directions, IsInfix l D.stops

def Connected (S A : Stations) : Prop := Nonempty (Trip S A)

lemma Connected_symm (stat : Stations) : Connected stat stat := by
  use [stat] <;> try simp
  intro l hl _
  have := hl.length_le
  simp_all

lemma Connected_rfl {pt₁ pt₂} (h : Connected pt₁ pt₂) : Connected pt₂ pt₁ := by
  let t := choice h
  use t.stops.reverse
  · simp [t.not_empty]
  · simp [t.arrival]
  · simp [t.start]
  -- · simp [t.nodup]
  · intro l hl htwo
    replace hl := reverse_reverse _ ▸ hl.reverse
    obtain ⟨D, hD⟩ := t.connection l.reverse hl (htwo ▸ length_reverse _)
    exact ⟨D.reverse, l.reverse_reverse.symm ▸ hD.reverse⟩


lemma Connected_trans {pt₁ pt₂ pt₃} (h12 : Connected pt₁ pt₂) (h23 : Connected pt₂ pt₃) :
  Connected pt₁ pt₃ := by
  constructor
  let t12 := choice h12
  let t23 := choice h23
  use t12.stops ++ t23.stops
  · simp [t12.not_empty]
  · rw [head_append_of_ne_nil]
    exact t12.start
  · rw [getLast_append_of_ne_nil t23.not_empty]
    exact t23.arrival
  · intro l hl hltwo
    by_cases in_12 : IsInfix l t12.stops
    · sorry
    · by_cases in_23 : IsInfix l t23.stops
      · sorry
      · sorry

end Metro
