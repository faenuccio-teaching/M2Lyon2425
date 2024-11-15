import Mathlib.Data.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.EReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.SetTheory.Cardinal.Continuum

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
  isClosed_eq (Continuous.mul continuous_fst continuous_snd) continuous_one

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

-- To prove
universe u v

theorem Cardinal.mk_iUnion_Ordinal_lift_lt_of_lt {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
    (ho : Cardinal.lift.{v, u} o.card ≤ Cardinal.lift.{u, v} c) (hc : Cardinal.aleph0 ≤ c)
    (A : Ordinal.{u} → Set β) (hA : ∀ j < o, Cardinal.mk ↑(A j) < Cardinal.aleph0) :
Cardinal.mk ↑(⋃ (j : Ordinal.{u}), ⋃ (_ : j < o), A j) < c := sorry

theorem fae (ξ : Ordinal) (hξ : ξ < c)
  (H : ∃ A₀ : ordinals_lt c → Set (ℝ × ℝ), ∀ ζ, (hζ : ζ < ξ) → prop_fae A₀ ⟨ζ, hζ.trans hξ⟩) :
  ∃ A : ordinals_lt c → Set (ℝ × ℝ),
    ∀ ζ : ordinals_le ξ, prop_fae A ⟨ζ, lt_of_le_of_lt ζ.2.out hξ⟩ := by
  obtain ⟨A₀, hA₀⟩ := H
  set B := ⋃ (ζ : Ordinal) (hζ : ζ < ξ), A₀ ⟨ζ, lt_trans hζ hξ⟩ with hB
  have hB_le : Cardinal.mk B < Cardinal.continuum := by
    have ho : Cardinal.lift.{0, u_1} ξ.card ≤ Cardinal.lift.{u_1, 0} Cardinal.continuum := by
      simp only [Cardinal.lift_id', Cardinal.lift_continuum]
      exact Cardinal.card_le_of_le_ord (le_of_lt hξ)
    let A : Ordinal → Set (ℝ × ℝ) := fun α ↦ if h : α < c then A₀ ⟨α, h⟩ else Set.univ
    have hA_def : A = fun α ↦ if h : α < c then A₀ ⟨α, h⟩ else Set.univ := rfl
    have hA : ∀ (ζ : Ordinal) (hζ : ζ < ξ), Cardinal.mk (A ζ) < Cardinal.aleph0 := by
      intros ζ hζ
      have this₁ := lt_of_le_of_lt (hA₀ ζ hζ).1 (Cardinal.nat_lt_aleph0 2)
      have this₂ : A ζ = A₀ ⟨ζ, lt_trans hζ hξ⟩ := by
        by_cases h : ζ < c
        rw [hA_def]
        simp only [h]
        rfl
        exfalso
        exact h (lt_trans hζ hξ)
      rw [← this₂] at this₁
      exact this₁
    have this₂ := Cardinal.mk_iUnion_Ordinal_lift_le_of_le ho Cardinal.aleph0_le_continuum A hA
    apply_fun Cardinal.mk at hB
    have : ↑(⋃ j, ⋃ (_ : j < ξ), A j) = ↑(⋃ ζ, ⋃ (hζ : ζ < ξ), A₀ ⟨ζ, lt_trans hζ hξ⟩) := by
      rw [hA_def]
      apply Set.ext
      intro S
      refine ⟨?_, ?_⟩
      sorry
    rw [this, ← hB] at this₂
    exact this₂
  let 𝒢 := {S | 2 ≤ Cardinal.mk ↑(S ∩ B) ∧ ∃ a b c, S = Line a b c}
  have h𝒢_le := Cardinal.mk 𝒢 ≤ (Cardinal.mk B)^2-- or directly `< Cardinal.continuum`
  let n := Nat.card (B ∩ (Lines ⟨ξ, hξ⟩) : Set (ℝ × ℝ))
  have byP : n ≤ 2 := sorry
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
  · convert hA₀ η hη
    simp only [dite_eq_ite, ite_eq_left_iff, not_lt]
    intro h
    sorry
