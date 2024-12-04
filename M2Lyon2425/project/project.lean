import Mathlib.Data.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.EReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Real.Cardinality
import Mathlib.Data.Set.Card

/-- Goal of the project: formalize the counterexamples of the chapter 10
of the book "Counterexamples in Analysis" by Bernard R. Gelbaum and
John M. H. Olmsted -/

-- Counterexample 1: Two disjoint closed sets that are at
-- a zero distance

def F1 : Set (ℝ × ℝ) := setOf fun (x,y) ↦ x*y = 1

def F2 : Set (ℝ × ℝ) := setOf fun (_,y) ↦ y=0

lemma F1_disjoint_F2 : F1 ∩ F2 = ∅ := by
  by_contra H
  rw [Set.ext_iff] at H
  push_neg at H
  cases' H with w H
  cases H with
  | inl h =>
      obtain ⟨⟨h, h'⟩, _⟩ := h
      change w.1 * w.2 = 1 at h
      rw [h', mul_zero] at h
      exact zero_ne_one h
  | inr h => exact h.2

lemma F1_closed : IsClosed F1 :=
  isClosed_eq (by continuity) continuous_one

lemma F2_closed : IsClosed F2 :=
  isClosed_eq continuous_snd continuous_zero

noncomputable instance : Dist (ℝ × ℝ) where
  dist := fun p q ↦ ((q.1 - p.1)^(2 : ℝ) + (q.2 - p.2)^(2 : ℝ))^(1/(2 : ℝ))

def set_dist (A B : Set (ℝ × ℝ)) : Set ℝ := setOf (∃ p ∈ A, ∃ q ∈ B, dist p q = ·)

noncomputable def distance (A B : Set (ℝ × ℝ)) := sInf (set_dist A B)

lemma set_dist_nonempty : (set_dist F1 F2).Nonempty := by
  refine ⟨dist (2, 1/2) ((2 : ℝ), (0 : ℝ)), ⟨(2, 1/2), ⟨?_, ⟨(2,0),
    ⟨(by rw [Set.mem_def]; rfl), rfl⟩⟩⟩⟩⟩
  change 2 * (1/2) = 1
  norm_num

lemma dist_on_prod_pos : ∀ d ∈ set_dist F1 F2, 0 ≤ d := by
  rintro a ⟨p, ⟨_, ⟨q, ⟨_, hdist⟩⟩⟩⟩
  rw [← hdist]
  change 0 ≤ ((q.1 - p.1)^2 + (q.2 - p.2)^2)^(1/2)
  rw [← Real.sqrt_eq_rpow]
  exact Real.sqrt_nonneg _

lemma distance_F1_F2_neg : distance F1 F2 ≤ 0 := by
  rw [distance, Real.sInf_le_iff ⟨0, dist_on_prod_pos⟩ set_dist_nonempty]
  refine fun ε hε ↦ ⟨dist (2 / ε, ε / 2) (2 / ε, 0), ⟨?_, ?_⟩⟩
  · refine ⟨(2 / ε, ε / 2), ⟨?_, ⟨(2 / ε, 0), ⟨(by rw [Set.mem_def]; rfl), rfl⟩⟩⟩⟩
    change (2/ε) * (ε/2) = 1
    norm_num
    exact div_self (ne_of_gt hε)
  · change ((2/ε - 2/ε)^2 + (0 - ε/2)^2)^(1/2) < 0 + ε
    rw [zero_add, sub_self, zero_sub, Real.zero_rpow two_ne_zero, zero_add, Real.rpow_two,
    Even.neg_pow even_two, ← Real.sqrt_eq_rpow, Real.sqrt_sq, half_lt_self_iff]
    exact hε
    linarith

lemma distance_F1_F2_pos : 0 ≤ distance F1 F2 :=
  le_csInf set_dist_nonempty dist_on_prod_pos

lemma distance_F1_F2_eq_zero : distance F1 F2 = 0 :=
  (LE.le.ge_iff_eq distance_F1_F2_neg).1 distance_F1_F2_pos

-- Counterexample 2: A bounded plane set contained in no minimum closed disk

def IsClosedDisk (D : Set (ℝ × ℝ)) (h k r : ℝ) (_ : 0 < r) : Prop :=
    ∀ x ∈ D, (x.1 - h)^2 + (x.2 - k)^2 ≤ r^2

def MinimumClosedDisk (A D : Set (ℝ × ℝ)) {h k r : ℝ} {hr : 0 < r} (_ : IsClosedDisk D h k r hr ∧ A ⊆ D)  : Prop :=
    ∀ (D' : Set (ℝ × ℝ)) (_ : (∃ (h' k' r' : ℝ) (hr' : 0 < r'), IsClosedDisk D' h' k' r' hr') ∧ A ⊆ D'), D ⊆ D'

def Line (a b c : ℝ) : Set (ℝ × ℝ) := setOf (fun x ↦ a*x.1 + b*x.2 = c)

def IsTwoPointSet (S : Set (ℝ × ℝ)) : Prop :=
  ∀ (a b c : ℝ), Cardinal.mk (Subtype (· ∈ Line a b c ∩ S)) = 2

example (S : Set (ℝ × ℝ)) (hS : IsTwoPointSet S) :
    ¬(∃ (D : Set (ℝ × ℝ)) (h k r : ℝ) (hr : 0 < r) (hD : IsClosedDisk D h k r hr ∧ S ⊆ D),
    MinimumClosedDisk S D hD) := by
  intro h
  obtain ⟨D, h, k, r, hr, ⟨hD, hD₂⟩, hD₃⟩ := h
  let L := Line 1 0 (h + r + 1)
  have : L ∩ D = ∅ := by
    by_contra h₂
    rw [Set.ext_iff] at h₂
    push_neg at h₂
    obtain ⟨w, hw⟩ := h₂
    cases hw with
    | inl h₃ =>
        obtain ⟨⟨hw, hw₂⟩, hw₃⟩ := h₃
        rw [IsClosedDisk] at hD
        specialize hD w hw₂
        change 1*w.1 + 0*w.2 = (h + r + 1) at hw
        rw [one_mul, zero_mul, add_zero] at hw
        rw [hw, add_sub_right_comm, add_sub_right_comm, sub_self, zero_add] at hD
        have : r ^ 2 < (r + 1) ^ 2 := by
          linarith
        have : r ^ 2 < (r + 1) ^ 2 + (w.2 - k) ^ 2 := by
          rw [add_comm]
          exact lt_add_of_nonneg_of_lt (even_two.pow_nonneg (w.2 - k)) this
        exact not_lt.2 hD this
    | inr h₃ => exact h₃.2
  have : L ∩ S = ∅ := by
    ext x
    refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
    · rw [Set.ext_iff] at this
      exact (this x).1 ⟨h'.1, hD₂ h'.2⟩
    · exfalso
      exact h'
  unfold IsTwoPointSet at hS
  specialize hS 1 0 (h + r + 1)
  apply_fun Cardinal.mk at this
  simp only [Cardinal.mk_eq_zero] at this
  rw [this] at hS
  exact two_ne_zero hS.symm

-- Construction of the two-point set

def IsColinear (a b : ℝ × ℝ) : Prop :=
  ∃ (a' b' c' : ℝ), a ∈ Line a' b' c' ∧ b ∈ Line a' b' c'

def NoThreeColinearPoints {α : Type*} (s : α → Set (ℝ × ℝ)) : Prop :=
  ¬(∃ a b c, a ∈ Set.iUnion s ∧ b ∈ Set.iUnion s ∧ c ∈ Set.iUnion s
  ∧ IsColinear a b ∧ IsColinear b c)

def ordinals_lt (o : Ordinal) : Set Ordinal := setOf (· < o)

def ordinals_le_lt (o₁ o₂ : Ordinal) : Set (ordinals_lt o₁) := setOf (· ≤ o₂)

-- Should I prove this?
def Lines : ordinals_lt Cardinal.continuum.ord → setOf (∃ a b c, · = Line a b c) := sorry

lemma Lines_bijective : Lines.Bijective := sorry
--

def Lines₂ (o : Ordinal) (ho : o ≤ Cardinal.continuum.ord) :
    ordinals_lt o → setOf (∃ a b c, · = Line a b c) :=
  fun ⟨o₂, ho₂⟩ ↦ Lines ⟨o₂, lt_of_lt_of_le ho₂ ho⟩

-- We want to build a sequence with the properties prop₁, prop₂, prop₃ below.
def seq_A_prop₁ (o : Ordinal) (f : ordinals_lt o → Set (ℝ × ℝ)) : Prop :=
  ∀ ε : ordinals_lt o, Cardinal.mk (f ε) ≤ 2

def seq_A_prop₂ (o : Ordinal) (f : ordinals_lt o → Set (ℝ × ℝ)) : Prop :=
  ∀ ε : ordinals_lt o, NoThreeColinearPoints (fun (i : ordinals_le_lt o ε) ↦ f i)

def seq_A_prop₃ (o : Ordinal) (f : ordinals_lt o → Set (ℝ × ℝ)) : Prop :=
  ∀ ε : ordinals_lt o, (ho : o ≤ Cardinal.continuum.ord) →
  Cardinal.mk (Subtype (· ∈ Set.iUnion (fun (i : ordinals_le_lt o ε) ↦ f i)
  ∩ Lines₂ o ho ε)) = 2
--

def exists_seq_A : ∃ (f : ordinals_lt Cardinal.continuum.ord → Set (ℝ × ℝ)),
    seq_A_prop₁ Cardinal.continuum.ord f
    ∧ seq_A_prop₂ Cardinal.continuum.ord f
    ∧ seq_A_prop₃ Cardinal.continuum.ord f := by
  apply Ordinal.induction
    (p := fun (o : Ordinal) ↦ ∃ (f : ordinals_lt o → Set (ℝ × ℝ)),
    seq_A_prop₁ o f ∧ seq_A_prop₂ o f ∧ seq_A_prop₃ o f) Cardinal.continuum.ord
  intros ε hε
  have := ε.zero_or_succ_or_limit
  cases' this with h₁ h₂
  · rw [h₁]
    use (fun _ ↦ ∅)
    refine ⟨fun ε ↦ ?_, fun ε ↦ ?_, fun ε ↦ ?_⟩
    exfalso
    exact ε.1.not_lt_zero ε.2
    exfalso
    exact ε.1.not_lt_zero ε.2
    exfalso
    exact ε.1.not_lt_zero ε.2
  · cases' h₂ with h₂ h₃
    · obtain ⟨a, ha⟩ := h₂
      rw [ha] at hε
      specialize hε a (Order.lt_succ a)
      obtain ⟨f, hf⟩ := hε
      sorry
    . sorry

-- Filippo: some trials

def ordinals_le (o : Ordinal) : Set Ordinal := setOf (· ≤ o)

def fae_NoThreeColinearPoints (s : Set (ℝ × ℝ)) : Prop :=
  ¬ (∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ IsColinear a b ∧ IsColinear b c)

noncomputable
abbrev c := Cardinal.continuum.ord

def union_le_fae (A : ordinals_lt c → Set (ℝ × ℝ)) (o : ordinals_lt c) : Set (ℝ × ℝ) :=
  (⋃ (b : ordinals_le o), A ⟨b, (lt_of_le_of_lt b.2 o.2.out)⟩)


/- This is the condition that `(I)`, `(P)` and `(D)` on page 81 are satisfied up to a certain `ξ`.
The function `A` is total, but the property only holds up to `ξ`-/
def prop_fae (A : ordinals_lt c → Set (ℝ × ℝ)) (ξ : ordinals_lt c) : Prop :=
  Cardinal.mk (A ξ) ≤ 2 ∧
  fae_NoThreeColinearPoints (union_le_fae A ξ) ∧
  Nat.card ((union_le_fae A ξ) ∩ (Lines ξ) : Set (ℝ × ℝ)) = 2
-- To think about: Nat.card or Cardinal.mk?

-- This is proved in mathlib4.
universe v u

theorem Cardinal.mk_iUnion_Ordinal_lift_le_of_le {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
    (ho : Cardinal.lift.{v, u} o.card ≤ Cardinal.lift.{u, v} c) (hc : Cardinal.aleph0 ≤ c)
    (A : Ordinal.{u} → Set β) (hA : ∀ j < o, Cardinal.mk ↑(A j) ≤ c) :
    Cardinal.mk ↑(⋃ (j : Ordinal.{u}), ⋃ (_ : j < o), A j) ≤ c := sorry
--

def Equiv.iUnion_ordinals_lt (o : Ordinal) :
    ⋃ j, ⋃ (_ : j < o), (fun α ↦ setOf (· = α)) j ≃ ordinals_lt o := by
  refine ⟨fun a ↦ ⟨a.1, ?_⟩, fun a ↦ ⟨a.1,
    Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨a.2, rfl⟩⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  obtain ⟨a, ha⟩ := a
  simp only [Set.mem_iUnion, exists_prop] at ha
  obtain ⟨i, ⟨hi, hi₂⟩⟩ := ha
  rwa [← hi₂] at hi

theorem Cardinal.mk_ordinals_lt_lt_continuum (ξ : ordinals_lt c) :
    Cardinal.mk (ordinals_lt ξ) < Cardinal.continuum := by
  set A := fun (α : Ordinal) ↦ setOf (· = α) with hA
  have heq : Cardinal.mk (⋃ j, ⋃ (_ : j < ξ.1), A j) = Cardinal.mk (ordinals_lt ξ) :=
    Cardinal.mk_congr (Equiv.iUnion_ordinals_lt ξ)
  rw [← heq]
  have this₃ : Cardinal.aleph0 + Cardinal.lift.{u_1 + 1, u_1} ξ.1.card < Cardinal.continuum :=
    Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum Cardinal.aleph0_lt_continuum
    (Cardinal.lift_lt_continuum.mpr (Cardinal.lt_ord.1 ξ.2))
  refine lt_of_le_of_lt (Cardinal.mk_iUnion_Ordinal_lift_le_of_le ?_ ?_ A (fun j _ ↦ ?_)) this₃
  · simp only [Ordinal.lift_card, Cardinal.lift_add, Cardinal.lift_aleph0, Ordinal.lift_lift,
    self_le_add_left]
  · simp only [Ordinal.lift_card, self_le_add_right]
  · simp only [hA, Set.setOf_eq_eq_singleton, Cardinal.mk_fintype, Fintype.card_ofSubsingleton,
    Nat.cast_one, Ordinal.lift_card]
    exact le_trans Cardinal.one_le_aleph0 (self_le_add_right _ _)

theorem Cardinal.mk_sUnion_lt_continuum (ξ : ordinals_lt c)
    (A₀ : ordinals_lt c → Set (ℝ × ℝ)) (H : ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    Cardinal.mk (⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩)) < Cardinal.continuum := by
  set fB := fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩
  let pre_B := Set.range fB
  let card_pre_B := (fun (i : pre_B) ↦ Cardinal.mk i)
  have this₁ : Cardinal.mk pre_B < Cardinal.continuum := by
    have := Cardinal.mk_subset_ge_of_subset_image_lift fB (subset_of_eq Set.image_univ.symm)
    simp only [Set.mem_univ, Set.mem_range, exists_apply_eq_apply, and_self, Set.setOf_true,
      Cardinal.mk_univ, Cardinal.lift_id'] at this
    exact Cardinal.lift_lt_continuum.mp (lt_of_le_of_lt this (Cardinal.mk_ordinals_lt_lt_continuum ξ))
  refine lt_of_le_of_lt (Cardinal.mk_sUnion_le pre_B)
    (Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum this₁ (lt_of_le_of_lt (le_trans
    (Cardinal.iSup_le_sum card_pre_B) ?_) (Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum this₁
    (Cardinal.nat_lt_continuum 2))))
  rw [← Cardinal.sum_const']
  refine Cardinal.sum_le_sum _ _ (fun i ↦ ?_)
  obtain ⟨y, hy⟩ := i.2
  have := (H y).1
  apply_fun Cardinal.mk at hy
  rwa [hy] at this

theorem exists_of_two_le_card {α : Type*} {S : Set α} (h : 2 < Nat.card S) : ∃ a b c, a ≠ b ∧
    b ≠ c ∧ a ≠ c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S := by
  have hn : Nat.card S ≠ 0 := by
    intro hn
    rw [hn] at h
    contradiction
  have e := Nat.equivFinOfCardPos hn
  have e_inj : Function.Injective e.2 := e.symm.injective
  exact ⟨e.2 ⟨0, lt_trans two_pos h⟩, e.2 ⟨1, lt_trans Nat.one_lt_two h⟩, e.2 ⟨2, h⟩,
    fun he ↦ zero_ne_one (Fin.mk.inj_iff.1 (e_inj (Subtype.eq he))),
    fun he ↦ OfNat.one_ne_ofNat 2 (Fin.mk.inj_iff.1 (e_inj (Subtype.eq he))),
    fun he ↦ two_ne_zero (Fin.mk.inj_iff.1 (e_inj (Subtype.eq he))).symm,
    (e.2 ⟨0, _⟩).2, (e.2 ⟨1, _⟩).2, (e.2 ⟨2, h⟩).2⟩

theorem contradiction_of_exists (ξ : ordinals_lt c) (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (H : ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    ¬(∃ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c
    ∧ a ∈ (⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩) ∩ Lines ξ)
    ∧ b ∈ (⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩) ∩ Lines ξ)
    ∧ c ∈ (⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩) ∩ Lines ξ)) := by
  intro H
  obtain ⟨a, b, c, _, _, _, ⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩, ⟨hc₁, hc₂⟩⟩ := H
  have h₃ : ∃ (ζ : Ordinal) (hζ : ζ < ξ), a ∈ union_le_fae A₀ ⟨ζ, lt_trans hζ ξ.2⟩
    ∧ b ∈ union_le_fae A₀ ⟨ζ, lt_trans hζ ξ.2⟩
    ∧ c ∈ union_le_fae A₀ ⟨ζ, lt_trans hζ ξ.2⟩ := by
    rw [Set.mem_sUnion] at ha₁ hb₁ hc₁
    obtain ⟨t₁, ht₁, ht₁'⟩ := ha₁
    obtain ⟨t₂, ht₂, ht₂'⟩ := hb₁
    obtain ⟨t₃, ht₃, ht₃'⟩ := hc₁
    rw [Set.mem_range] at ht₁ ht₂ ht₃
    obtain ⟨x₁, hx₁⟩ := ht₁
    obtain ⟨x₂, hx₂⟩ := ht₂
    obtain ⟨x₃, hx₃⟩ := ht₃
    refine ⟨(x₁ ⊔ x₂) ⊔ x₃, ?_, ?_⟩
    · simp only [sup_lt_iff]
      exact ⟨⟨x₁.2, x₂.2⟩, x₃.2⟩
    · refine ⟨Set.mem_iUnion.2 ⟨⟨x₁, ?_⟩, by rwa [← hx₁] at ht₁'⟩, Set.mem_iUnion.2 ⟨⟨x₂, ?_⟩,
        by rwa [← hx₂] at ht₂'⟩, Set.mem_iUnion.2 ⟨⟨x₃, ?_⟩, by rwa [← hx₃] at ht₃'⟩⟩
      · change x₁ ≤ x₁ ⊔ x₂ ⊔ x₃
        rw [le_sup_iff]
        left
        rw [le_sup_iff]
        left
        exact le_refl x₁
      · change x₂ ≤ x₁ ⊔ x₂ ⊔ x₃
        rw [le_sup_iff]
        left
        rw [le_sup_iff]
        right
        exact le_refl x₂
      · change x₃ ≤ x₁ ⊔ x₂ ⊔ x₃
        rw [le_sup_iff]
        right
        exact le_refl x₃
  obtain ⟨ζ, hζ, h₃⟩ := h₃
  apply (H ⟨ζ, hζ⟩).2.1
  refine ⟨a, b, c, h₃.1, h₃.2.1, h₃.2.2, ?_⟩
  obtain ⟨a', b', c', h'⟩ := (Lines ξ).2
  exact ⟨⟨a', b', c', by rwa [h'] at ha₂, by rwa [h'] at hb₂⟩, ⟨a', b', c',
    by rwa [h'] at hb₂, by rwa [h'] at hc₂⟩⟩

theorem inter_line_card_le_two (ξ : ordinals_lt c) (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (H : ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    Nat.card (⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩)
    ∩ (Lines ξ) : Set (ℝ × ℝ)) ≤ 2 := by
  set B := ⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩)
  set n := Nat.card (B ∩ (Lines ξ) : Set (ℝ × ℝ))
  by_contra h
  push_neg at h
  exact contradiction_of_exists ξ A₀ H (exists_of_two_le_card h)

theorem exists_of_infinite {α : Type*} {S : Set α} (hS : S.Infinite) :
    ∃ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S := by
    obtain ⟨t, hsub, hcard⟩ := Set.Infinite.exists_subset_card_eq hS 3
    rw [← Set.ncard_coe_Finset, Set.ncard_eq_three] at hcard
    obtain ⟨x, y, z, hxy, hxz, hyz, ht⟩ := hcard
    exact ⟨x, y, z, hxy, hyz, hxz, hsub (by simp only [ht, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or]), hsub (by simp only [ht, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or, or_true]), hsub (by simp only [ht, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true])⟩

theorem inter_finite (ξ : ordinals_lt c) (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (H : ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    Set.Finite (⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩) ∩ Lines ξ) := by
  set B := ⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩)
  by_contra h
  rw [← Set.Infinite] at h
  exact contradiction_of_exists ξ A₀ H (exists_of_infinite h)

theorem fae (ξ : ordinals_lt c)
  (H : ∃ A₀ : ordinals_lt c → Set (ℝ × ℝ), ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    ∃ A : ordinals_lt c → Set (ℝ × ℝ),
    ∀ ζ : ordinals_le ξ, prop_fae A ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ := by
  obtain ⟨A₀, hA₀⟩ := H
  set B := ⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩) with hB
  have hB_le : Cardinal.mk B < Cardinal.continuum := Cardinal.mk_sUnion_lt_continuum ξ A₀ hA₀
  let 𝒢 := {S | 2 ≤ Cardinal.mk ↑(S ∩ B) ∧ ∃ a b c, S = Line a b c}
  have h𝒢_le : Cardinal.mk 𝒢 ≤ (Cardinal.mk B)^2 := sorry-- or directly `< Cardinal.continuum`
  let n := Nat.card (B ∩ (Lines ξ) : Set (ℝ × ℝ))-- Nat.card or Cardinal.mk?
  have byP : n ≤ 2 ∧ Set.Finite (B ∩ (Lines ξ)) := ⟨inter_line_card_le_two ξ A₀ hA₀,
    inter_finite ξ A₀ hA₀⟩
  let Aξ : Set (ℝ × ℝ) :=
    if n = 2 then ∅
    else
      if n = 1 then sorry
      else sorry
  apply Exists.intro
  swap
  intro ζ
  by_cases hζ : ζ < ξ
  · use A₀ ζ
  · by_cases hζ' : ζ = ξ
    · use Aξ
    · use Set.univ
  rintro ⟨η, hη⟩
  simp only [ordinals_le, Set.mem_setOf_eq] at hη
  rw [le_iff_eq_or_lt] at hη
  rcases hη with hη | hη
  · simp only [dite_eq_ite, hη, Subtype.coe_eta, prop_fae, lt_self_iff_false, reduceIte,
      Set.mem_setOf_eq]
    sorry
  · convert hA₀ ⟨η, hη⟩
    simp only [dite_eq_ite, ite_eq_left_iff, not_lt]
    intro h
    sorry