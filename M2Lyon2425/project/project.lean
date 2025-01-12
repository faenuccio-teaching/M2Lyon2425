import Mathlib.Data.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.EReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Real.Cardinality
import Mathlib.Data.Set.Card
import Mathlib.Analysis.MeanInequalities

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

lemma F1_Nonempty : F1.Nonempty := by
    refine ⟨⟨1, 1⟩, ?_⟩
    change 1*1 = 1
    rw [mul_one]

lemma F2_Nonempty : F2.Nonempty := ⟨⟨0, 0⟩, by rfl⟩

noncomputable instance : Dist (ℝ × ℝ) where
  dist := fun p q ↦ ((q.1 - p.1)^(2 : ℕ) + (q.2 - p.2)^(2 : ℕ))^(1/(2 : ℝ))

/- The Euclidean distance is symmetric. -/
lemma Euclidean_dist_comm : ∀ (p q : ℝ × ℝ), dist p q = dist q p := by
  intros p q
  change ((q.1 - p.1)^(2 : ℕ) + (q.2 - p.2)^(2 : ℕ))^(1/(2 : ℝ)) =
    ((p.1 - q.1)^(2 : ℕ) + (p.2 - q.2)^(2 : ℕ))^(1/(2 : ℝ))
  rw [← even_two.pow_abs, ← even_two.pow_abs (q.2 - p.2), abs_sub_comm,
    abs_sub_comm q.2 p.2, even_two.pow_abs, even_two.pow_abs]

/- A special case of Minkowski's inequality. We need it to prove
the triangle inequality for the Euclidean distance. -/
lemma minkowski (x y z : ℝ × ℝ) : ((dist z.1 y.1 + dist y.1 x.1) ^ 2
    + (dist z.2 y.2 + dist y.2 x.2) ^ 2)^(1/(2 : ℝ)) ≤
    (dist z.1 y.1 ^ 2 + dist z.2 y.2 ^ 2)^(1/(2 : ℝ))
    + (dist y.1 x.1 ^ 2 + dist y.2 x.2 ^ 2)^(1/(2 : ℝ)) := by
  set s := ({0,1} : Set ℝ).toFinset with hs
  set f := fun (t : ℝ) ↦ if t = 0 then dist z.1 y.1 else dist z.2 y.2
    with f_def
  set g := fun (t : ℝ) ↦ if t = 0 then dist y.1 x.1 else dist y.2 x.2
    with g_def
  have hfg : ∑ i ∈ s, |f i + g i| ^ (2 : ℝ) =
      (dist z.1 y.1 + dist y.1 x.1) ^ 2 + (dist z.2 y.2 + dist y.2 x.2) ^ 2 := by
    rw [f_def, g_def, hs]
    field_simp
  have hf : ∑ i ∈ s, |f i| ^ (2 : ℝ) = dist z.1 y.1 ^ 2 + dist z.2 y.2 ^ 2 := by
    rw [f_def, hs]
    field_simp
  have hg : ∑ i ∈ s, |g i| ^ (2 : ℝ) = dist y.1 x.1 ^ 2 + dist y.2 x.2 ^ 2 := by
    rw [g_def, hs]
    field_simp
  rw [← hfg, ← hf, ← hg]
  exact Real.Lp_add_le s f g one_le_two

/- The triangle inequality holds for the Euclidean distance. -/
lemma Euclidean_dist_triangle :
    ∀ (x y z : ℝ × ℝ), dist x z ≤ dist x y + dist y z := by
  intros x y z
  change ((z.1 - x.1)^(2 : ℕ) + (z.2 - x.2)^(2 : ℕ))^(1/(2 : ℝ)) ≤
    ((y.1 - x.1)^(2 : ℕ) + (y.2 - x.2)^(2 : ℕ))^(1/(2 : ℝ)) +
    ((z.1 - y.1)^(2 : ℕ) + (z.2 - y.2)^(2 : ℕ))^(1/(2 : ℝ))
  rw [← even_two.pow_abs, ← even_two.pow_abs (z.2 - x.2)]
  have := dist_triangle z.1 y.1 x.1
  have h : dist z.1 x.1 ^ 2 ≤ (dist z.1 y.1 + dist y.1 x.1) ^ 2 := by
    rwa [← pow_le_pow_iff_left dist_nonneg
    (Left.add_nonneg dist_nonneg dist_nonneg)
    (Nat.zero_ne_add_one 1).symm] at this
  have := dist_triangle z.2 y.2 x.2
  have h₂ : dist z.2 x.2 ^ 2 ≤ (dist z.2 y.2 + dist y.2 x.2) ^ 2 := by
    rwa [← pow_le_pow_iff_left dist_nonneg
    (Left.add_nonneg dist_nonneg dist_nonneg)
    (Nat.zero_ne_add_one 1).symm] at this
  have h₃ : (dist z.1 x.1 ^ 2 + dist z.2 x.2 ^ 2)^(1/(2 : ℝ)) ≤
      ((dist z.1 y.1 + dist y.1 x.1) ^ 2 + (dist z.2 y.2
      + dist y.2 x.2) ^ 2)^(1/(2 : ℝ)) := by
    simp only [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (add_le_add h h₂)
  rw [← even_two.pow_abs (y.1 - x.1), ← even_two.pow_abs (y.2 - x.2),
    ← even_two.pow_abs (z.1 - y.1), ← even_two.pow_abs (z.2 - y.2),
    add_comm ((|y.1 - x.1| ^ 2 + |y.2 - x.2| ^ 2) ^ (1 / 2)) _]
  exact h₃.trans (minkowski x y z)

def set_dist (A B : Set (ℝ × ℝ)) : Set ℝ := setOf (∃ p ∈ A, ∃ q ∈ B, dist p q = ·)

noncomputable def distance (A B : Set (ℝ × ℝ)) := sInf (set_dist A B)

/- Given two subsets A, B of the Euclidean plane, the set of distances between
points of A and B is nonempty as long as A and B are nonempty. -/
lemma set_dist_nonempty {A B : Set (ℝ × ℝ)} (hA : A.Nonempty)
    (hB : B.Nonempty) : (set_dist A B).Nonempty := by
  obtain ⟨a, hA⟩ := hA
  obtain ⟨b, hB⟩ := hB
  exact ⟨dist a b, a, hA, b, hB, by rfl⟩

/- dist is actually a distance. In particular, it's always positive. -/
lemma dist_on_prod_pos (A B : Set (ℝ × ℝ)) : ∀ d ∈ set_dist A B, 0 ≤ d := by
  rintro a ⟨p, ⟨_, ⟨q, ⟨_, hdist⟩⟩⟩⟩
  rw [← hdist]
  change 0 ≤ ((q.1 - p.1)^2 + (q.2 - p.2)^2)^(1/2)
  rw [← Real.sqrt_eq_rpow]
  exact Real.sqrt_nonneg _

lemma distance_F1_F2_neg : distance F1 F2 ≤ 0 := by
  rw [distance, Real.sInf_le_iff ⟨0, dist_on_prod_pos F1 F2⟩
    (set_dist_nonempty F1_Nonempty F2_Nonempty)]
  refine fun ε hε ↦ ⟨dist (2 / ε, ε / 2) (2 / ε, 0), ⟨?_, ?_⟩⟩
  · refine ⟨(2 / ε, ε / 2), ⟨?_, ⟨(2 / ε, 0), ⟨(by rw [Set.mem_def]; rfl), rfl⟩⟩⟩⟩
    change (2/ε) * (ε/2) = 1
    norm_num
    exact div_self (ne_of_gt hε)
  · change ((2/ε - 2/ε)^2 + (0 - ε/2)^2)^(1/2) < 0 + ε
    rw [sub_self, zero_pow, zero_add, zero_sub, Even.neg_pow, zero_add, ← Real.sqrt_eq_rpow]
    field_simp
    exact hε
    exact Nat.even_iff.2 (by rfl)
    exact (Nat.zero_ne_add_one 1).symm

lemma distance_F1_F2_pos : 0 ≤ distance F1 F2 :=
  le_csInf (set_dist_nonempty F1_Nonempty F2_Nonempty) (dist_on_prod_pos F1 F2)

lemma distance_F1_F2_eq_zero : distance F1 F2 = 0 :=
  (LE.le.ge_iff_eq distance_F1_F2_neg).1 distance_F1_F2_pos

/- F1 and F2 are a counterexample for the following statement:
given A and B two subsets of the Euclidean plane, if their distance
is zero, then they are disjoint. However, the other implication
is true and is proven below. -/
lemma dist_eq_zero_of_inter (A B : Set (ℝ × ℝ)) :
    (A ∩ B).Nonempty → distance A B = 0 := by
  intro h
  obtain ⟨x, hx⟩ := h
  have : dist x x = 0 := by
    change ((x.1 - x.1)^(2 : ℕ) + (x.2 - x.2)^(2 : ℕ))^(1/(2 : ℝ)) = 0
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, one_div, inv_eq_zero, Real.zero_rpow]
  have this₂ : BddBelow (set_dist A B) := by
    rw [bddBelow_def]
    exact ⟨0, fun d hd ↦ dist_on_prod_pos A B d hd⟩
  have dist_neg : distance A B ≤ 0 := by
    rw [distance, Real.sInf_le_iff this₂ (set_dist_nonempty ⟨x, hx.1⟩ ⟨x, hx.2⟩)]
    intros ε hε
    exact ⟨dist x x, ⟨x, hx.1, x, hx.2, by rfl⟩, by rwa [this, zero_add]⟩
  have dist_pos : 0 ≤ distance A B := by
    rw [distance]
    exact le_csInf (set_dist_nonempty ⟨x, hx.1⟩ ⟨x, hx.2⟩)
      (fun b hb ↦ dist_on_prod_pos A B b hb)
  exact dist_neg.ge_iff_eq.1 dist_pos

-- Counterexample 2: A bounded plane set contained in no minimum closed disk

def IsClosedDisk (D : Set (ℝ × ℝ)) (h k r : ℝ) (_ : 0 < r) : Prop :=
    ∀ x ∈ D, (x.1 - h)^2 + (x.2 - k)^2 ≤ r^2

/- Given a bounded subset A of the Euclidean plane, a minimum closed disk for A
is a closed disk containing A and contained in all closed disks containing A. -/
def IsMinimumClosedDisk {A D : Set (ℝ × ℝ)} {h k r : ℝ} {hr : 0 < r}
    (_ : IsClosedDisk D h k r hr ∧ A ⊆ D) : Prop :=
    ∀ D', ∃ h' k' r', (hr' : 0 < r') → IsClosedDisk D' h' k' r' hr' ∧ A ⊆ D' → D ⊆ D'

def Line (a b c : ℝ) : Set (ℝ × ℝ) := setOf (fun x ↦ a*x.1 + b*x.2 = c)

/- A two-point set is a subset of the Euclidean plane which intersects
every line in exactly two points. -/
def IsTwoPointSet (S : Set (ℝ × ℝ)) : Prop :=
  ∀ (a b c : ℝ), Cardinal.mk (Line a b c ∩ S : Set (ℝ × ℝ)) = 2

/- Given a closed disk D, we find a line which doesn't intersect it. -/
lemma line_inter_disk {D : Set (ℝ × ℝ)} {h k r : ℝ} {hr : 0 < r}
    (hD : IsClosedDisk D h k r hr) :
    Line 1 0 (h + r + 1) ∩ D = ∅ := by
  ext w
  refine ⟨fun ⟨hw, hw₂⟩ ↦ ?_, fun hx ↦ ?_⟩
  · replace hw := hw.out
    rw [one_mul, zero_mul, add_zero] at hw
    specialize hD w hw₂
    rw [hw, add_sub_right_comm, add_sub_right_comm, sub_self, zero_add] at hD
    have : r ^ 2 < (r + 1) ^ 2 + (w.2 - k) ^ 2 := by
      rw [add_comm]
      exact lt_add_of_nonneg_of_lt (sq_nonneg (w.2 - k)) (by linarith)
    exact not_lt.2 hD this
  · exfalso
    exact hx

example {S : Set (ℝ × ℝ)} (hS : IsTwoPointSet S) :
    ¬(∃ D h k r, ∃ (hr : 0 < r) (hD : IsClosedDisk D h k r hr ∧ S ⊆ D),
    IsMinimumClosedDisk hD) := by
  intro h
  obtain ⟨D, h, k, r, hr, ⟨hD, hD₂⟩, hD₃⟩ := h
  have := line_inter_disk hD
  have : Line 1 0 (h + r + 1) ∩ S = ∅ := by
    ext x
    refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
    · rw [Set.ext_iff] at this
      exact (this x).1 ⟨h'.1, hD₂ h'.2⟩
    · exfalso
      exact h'
  specialize hS 1 0 (h + r + 1)
  apply_fun Cardinal.mk at this
  rw [hS, Cardinal.mk_eq_zero] at this
  exact two_ne_zero this

/- Let A ⊆ ℝ × ℝ. A is bounded if ∃ r > 0 such that
∀ a₁, a₂ ∈ A, dist a₁ a₂ < r. We use this definition
to define a bornology on ℝ × ℝ. This allows us to later
use Bornology.IsBounded. -/
def bornology_plane : Bornology (ℝ × ℝ) :=
    Bornology.ofDist dist Euclidean_dist_comm Euclidean_dist_triangle

/- A two-point set is a counterexample for the following statement :
A subset of the Euclidean plane is bounded if and only if it is
contained in a minimum closed disk. However, one implication of this
statement is true and is proven below. -/
lemma bounded_of_exists_MinimumClosedDisk (A : Set (ℝ × ℝ)) : (∃ D h k r hr,
    ∃ (hD : IsClosedDisk D h k r hr ∧ A ⊆ D), IsMinimumClosedDisk hD) →
    @Bornology.IsBounded _ bornology_plane A := by
  intro h
  rw [Bornology.isBounded_def, Bornology.cobounded, Bornology.cobounded', bornology_plane,
  Bornology.ofDist, Bornology.ofBounded]
  simp only [Prod.forall, Set.mem_setOf_eq, Filter.mem_comk, compl_compl]
  obtain ⟨D, h, k, r, hr, hD, _⟩ := h
  refine ⟨r*2, fun a b hab c d hcd ↦ ?_⟩
  by_contra h₂
  push_neg at h₂
  have hr₂ := lt_of_lt_of_le h₂ (Euclidean_dist_triangle (a, b) (h, k) (c, d))
  have hr₃ : (r^2)^(1/(2 : ℝ)) = r := by
      rw [← Real.sqrt_eq_rpow, pow_two, Real.sqrt_mul_self (le_of_lt hr)]
  have hab₂ : dist (a, b) (h, k) ≤ r := by
    rw [Euclidean_dist_comm (a, b) (h, k)]
    have : (((a, b).1 - h) ^ 2 + ((a, b).2 - k) ^ 2)^(1/(2 : ℝ)) ≤ (r ^ 2)^(1/(2 : ℝ)) := by
      simp only [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt (hD.1 (a, b) (hD.2 hab))
    rwa [hr₃] at this
  have hcd₂ : dist (h, k) (c, d) ≤ r := by
    have : (((c, d).1 - h) ^ 2 + ((c, d).2 - k) ^ 2)^(1/(2 : ℝ)) ≤ (r ^ 2)^(1/(2 : ℝ)) := by
      simp only [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt (hD.1 (c, d) (hD.2 hcd))
    rwa [hr₃] at this
  have : r * 2 < r + r := by
    exact lt_add_of_lt_add_right (lt_add_of_lt_add_left hr₂ hcd₂) hab₂
  exact (lt_self_iff_false (r * 2)).1 (by rwa [(mul_two r).symm] at this)

-- Construction of the two-point set

-- This is proven in mathlib4.
universe v u

theorem Cardinal.mk_iUnion_Ordinal_lift_le_of_le {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
    (ho : Cardinal.lift.{v, u} o.card ≤ Cardinal.lift.{u, v} c) (hc : Cardinal.aleph0 ≤ c)
    (A : Ordinal.{u} → Set β) (hA : ∀ j < o, Cardinal.mk ↑(A j) ≤ c) :
    Cardinal.mk ↑(⋃ (j : Ordinal.{u}), ⋃ (_ : j < o), A j) ≤ c := sorry
--

-- Definitions

def IsColinear (a b : ℝ × ℝ) : Prop :=
  ∃ a' b' c', a ∈ Line a' b' c' ∧ b ∈ Line a' b' c'

def ordinals_lt (o : Ordinal) : Set Ordinal := setOf (· < o)

def ordinals_le (o : Ordinal) : Set Ordinal := setOf (· ≤ o)

def fae_NoThreeColinearPoints (s : Set (ℝ × ℝ)) : Prop :=
  ¬ (∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ IsColinear a b ∧ IsColinear b c)

noncomputable
abbrev c := Cardinal.continuum.ord

def union_le_fae (A : ordinals_lt c → Set (ℝ × ℝ)) (o : ordinals_lt c) : Set (ℝ × ℝ) :=
  (⋃ (b : ordinals_le o), A ⟨b, (lt_of_le_of_lt b.2 o.2.out)⟩)

-- Should I prove this?
def Lines : ordinals_lt Cardinal.continuum.ord → setOf (∃ a b c, · = Line a b c) := sorry

lemma Lines_bijective : Lines.Bijective := sorry
--

/- This is the condition that `(I)`, `(P)` and `(D)` on page 81 are satisfied up to a certain `ξ`.
The function `A` is total, but the property only holds up to `ξ`-/
def prop_fae (A : ordinals_lt c → Set (ℝ × ℝ)) (ξ : ordinals_lt c) : Prop :=
  Cardinal.mk (A ξ) ≤ 2 ∧
  fae_NoThreeColinearPoints (union_le_fae A ξ) ∧
  Nat.card ((union_le_fae A ξ) ∩ (Lines ξ) : Set (ℝ × ℝ)) = 2
-- To think about: Nat.card or Cardinal.mk?

/- We find a union which has the same cardinality as the set of ordinals less than o
(o being an ordinal). It's the union of the singleton sets {j} where j is an ordinal
less than o. We do this because we know the cardinality of an indexed union. -/
def Equiv.iUnion_ordinals_lt (o : Ordinal) :
    ⋃ j, ⋃ (_ : j < o), (fun α ↦ setOf (· = α)) j ≃ ordinals_lt o := by
  refine ⟨fun a ↦ ⟨a.1, ?_⟩, fun a ↦ ⟨a.1,
    Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨a.2, rfl⟩⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  obtain ⟨a, ha⟩ := a
  simp only [Set.mem_iUnion] at ha
  obtain ⟨i, hi, hi₂⟩ := ha
  rwa [← hi₂] at hi

open Cardinal in
/- We show this statement by proving that
1) The cardinality of (ordinals_lt ξ) is less or equal to ℵ₀ + #ξ (we know the cardinality
of an indexed union)
2) ℵ₀ + #ξ is less than the cardinality of the continuum (we know that if two cardinal numbers are
less than a certain cardinal c than their sum is less than c) -/
theorem Cardinal.mk_ordinals_lt_lt_continuum (ξ : ordinals_lt c) :
    mk (ordinals_lt ξ) < continuum := by
  rw [← mk_congr (Equiv.iUnion_ordinals_lt ξ)]
  have : aleph0 + lift.{u_1 + 1, u_1} ξ.1.card < continuum :=
    add_lt_of_lt aleph0_le_continuum aleph0_lt_continuum (lift_lt_continuum.2 (lt_ord.1 ξ.2))
  refine lt_of_le_of_lt (mk_iUnion_Ordinal_lift_le_of_le ?_ ?_ (fun α ↦ setOf (· = α)) ?_) this
  · simp only [Ordinal.lift_card, lift_add, lift_aleph0, Ordinal.lift_lift,
    self_le_add_left]
  · simp only [Ordinal.lift_card, self_le_add_right]
  · intros j _
    simp only [Set.setOf_eq_eq_singleton, mk_fintype, Fintype.card_ofSubsingleton,
    Nat.cast_one, Ordinal.lift_card]
    exact le_trans one_le_aleph0 (self_le_add_right _ _)

open Cardinal in
/- We have a sequence A₀ of subsets of the plane such that the elements (up to a certain rank)
satisfy the conditions (I), (P) and (D). We show that the cardinality of the union of
the sequence A₀ (up to a certain rank ξ) is less than the cardinality of the continuum.
A few comments on the proof:
1) The cardinality of A₀ (up to the rank ξ) is bounded by the cardinality of (ordinals_lt ξ)
(which we know thanks to the statement above)
2) To conclude, we use the fact that the multiplication of two cardinal numbers (less than
a cardinal number c) is less than c. -/
theorem Cardinal.mk_sUnion_lt_continuum (ξ : ordinals_lt c)
    (A₀ : ordinals_lt c → Set (ℝ × ℝ)) (H : ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    mk (⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)) < continuum := by
  set fB := fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩
  let pre_B := Set.range fB
  let fcard_pre_B := fun (i : pre_B) ↦ mk i
  have card_pre_B : mk pre_B < continuum := by
    have := mk_subset_ge_of_subset_image_lift fB (subset_of_eq Set.image_univ.symm)
    simp only [Set.mem_univ, Set.mem_range, exists_apply_eq_apply, and_self, Set.setOf_true,
      mk_univ, lift_id'] at this
    exact lift_lt_continuum.1 (lt_of_le_of_lt this (mk_ordinals_lt_lt_continuum ξ))
  have card_iSup : ⨆ (s : pre_B), mk s ≤ mk pre_B * 2 := by
    have this := iSup_le_sum fcard_pre_B
    have this₂ : sum fcard_pre_B ≤ mk pre_B * 2 := by
      rw [← sum_const']
      refine sum_le_sum _ _ ?_
      intro i
      obtain ⟨y, hy⟩ := i.2
      apply_fun mk at hy
      have this₂ := (H y).1
      rwa [hy] at this₂
    exact le_trans this this₂
  exact lt_of_le_of_lt (mk_sUnion_le pre_B) (mul_lt_of_lt aleph0_le_continuum card_pre_B
    (lt_of_le_of_lt card_iSup (mul_lt_of_lt aleph0_le_continuum card_pre_B
    (nat_lt_continuum 2))))

theorem exists_of_two_lt_card {α : Type*} {S : Set α} (h : 2 < Nat.card S) : ∃ a b c, a ≠ b ∧
    b ≠ c ∧ a ≠ c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S := by
  let e := Nat.equivFinOfCardPos (Nat.not_eq_zero_of_lt h)
  have e_inj := e.symm.injective
  refine ⟨e.2 ⟨0, Nat.zero_lt_of_lt h⟩, e.2 ⟨1, Nat.lt_of_succ_lt h⟩, e.2 ⟨2, h⟩, ?_, ?_, ?_,
    (e.2 ⟨0, _⟩).2, (e.2 ⟨1, _⟩).2, (e.2 ⟨2, _⟩).2⟩
  · intro he
    exact zero_ne_one (Fin.mk.inj_iff.1 (e_inj (Subtype.eq he)))
  · intro he
    exact OfNat.one_ne_ofNat 2 (Fin.mk.inj_iff.1 (e_inj (Subtype.eq he)))
  · intro he
    exact two_ne_zero (Fin.mk.inj_iff.1 (e_inj (Subtype.eq he))).symm

/- We show that if three points belong to the union of A₀ (up to a certain rank ξ), then
there exists a rank ζ such that a, b and c belong to the union of A₀ up to the rank ζ.
This rank ζ is the maximum of the indices of the sets to which a, b and c belong. -/
theorem mem_union_le_fae (ξ : ordinals_lt c) (A₀ : ordinals_lt c → Set (ℝ × ℝ)) (a b c : ℝ × ℝ)
    (ha : a ∈ ⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    (hb : b ∈ ⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    (hc : c ∈ ⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    ∃ (ζ : ordinals_lt ξ), a ∈ union_le_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩
    ∧ b ∈ union_le_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩
    ∧ c ∈ union_le_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩ := by
  rw [Set.mem_sUnion] at ha hb hc
  cases' ha with t₁ ht₁
  cases' hb with t₂ ht₂
  cases' hc with t₃ ht₃
  rw [Set.mem_range] at ht₁ ht₂ ht₃
  obtain ⟨⟨x₁, hx₁⟩, hx₁'⟩ := ht₁
  obtain ⟨⟨x₂, hx₂⟩, hx₂'⟩ := ht₂
  obtain ⟨⟨x₃, hx₃⟩, hx₃'⟩ := ht₃
  refine ⟨⟨(x₁.1 ⊔ x₂.1) ⊔ x₃.1, ?_⟩, ?_, ?_, ?_⟩
  · change (x₁.1 ⊔ x₂.1) ⊔ x₃.1 < ξ.1
    simp only [sup_lt_iff]
    exact ⟨⟨x₁.2, x₂.2⟩, x₃.2⟩
  · rw [union_le_fae, Set.mem_iUnion]
    refine ⟨⟨x₁.1, ?_⟩, by rwa [← hx₁] at hx₁'⟩
    dsimp
    change x₁.1 ≤ x₁.1 ⊔ x₂.1 ⊔ x₃.1
    simp only [le_sup_iff, le_sup_left, Subtype.coe_le_coe, true_or]
    left
    left
    exact Preorder.le_refl x₁
  · rw [union_le_fae, Set.mem_iUnion]
    refine ⟨⟨x₂.1, ?_⟩, by rwa [← hx₂] at hx₂'⟩
    dsimp
    change x₂.1 ≤ x₁.1 ⊔ x₂.1 ⊔ x₃.1
    simp only [le_sup_iff, le_sup_left, Subtype.coe_le_coe, true_or]
    left
    right
    exact Preorder.le_refl x₂
  · rw [union_le_fae, Set.mem_iUnion]
    refine ⟨⟨x₃.1, ?_⟩, by rwa [← hx₃] at hx₃'⟩
    dsimp
    change x₃.1 ≤ x₁.1 ⊔ x₂.1 ⊔ x₃.1
    simp only [le_sup_iff, le_sup_left, Subtype.coe_le_coe, true_or]
    right
    exact Preorder.le_refl x₃

/- Earlier, we had indexed the set of lines of the plane using (ordinals_lt Cardinal.continuum.ord).
This is all the ordinals less than the smallest ordinal with cardinality the cardinality of the continuum.
We show that the union of A₀ (up to a certain rank ξ) intersects the line indexed by ξ
in two points at most. This is true because otherwise, we would get a union of elements of A₀ with
three colinear points. -/
theorem contradiction_of_exists (ξ : ordinals_lt c) (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (H : ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    ¬(∃ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c
    ∧ a ∈ ((⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) ∩ Lines ξ)
    ∧ b ∈ ((⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) ∩ Lines ξ)
    ∧ c ∈ ((⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) ∩ Lines ξ)) := by
  intro h
  obtain ⟨a, b, c, _, _, _, ⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩, ⟨hc₁, hc₂⟩⟩ := h
  obtain ⟨ζ, h'⟩ := mem_union_le_fae ξ A₀ a b c ha₁ hb₁ hc₁
  apply (H ζ).2.1
  refine ⟨a, b, c, h'.1, h'.2.1, h'.2.2, ?_⟩
  obtain ⟨a', b', c', h''⟩ := (Lines ξ).2
  exact ⟨⟨a', b', c', by rwa [h''] at ha₂, by rwa [h''] at hb₂⟩, ⟨a', b', c',
    by rwa [h''] at hb₂, by rwa [h''] at hc₂⟩⟩

/- We reformulate the statement above so it fits in the
proof of the main result "fae". To be precise, the following statement is weaker than the one above :
if the Nat.card of a set is less or equal to 2, then the set is either of cardinality 0, 1, 2
or infinite. We later show that the intersection is a finite set
(please see the theorem "inter_Finite"). -/
theorem card_inter_line_le_two (ξ : ordinals_lt c) (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (H : ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    Nat.card ((⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    ∩ Lines ξ : Set (ℝ × ℝ)) ≤ 2 := by
  by_contra h
  push_neg at h
  exact contradiction_of_exists ξ A₀ H (exists_of_two_lt_card h)

theorem exists_of_Infinite {α : Type*} {S : Set α} [DecidableEq α] (hS : S.Infinite) :
    ∃ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S := by
    obtain ⟨t, hsub, hcard⟩ := Set.Infinite.exists_subset_card_eq hS 3
    obtain ⟨x, y, z, hxy, hxz, hyz, ht⟩ := Finset.card_eq_three.1 hcard
    exact ⟨x, y, z, hxy, hyz, hxz, hsub (by simp only [ht, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]),
      hsub (by simp only [ht, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]), hsub
      (by simp only [ht, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff, or_true])⟩

theorem inter_Finite (ξ : ordinals_lt c) (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (H : ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    ((⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) ∩ Lines ξ).Finite := by
  by_contra h
  rw [← Set.Infinite] at h
  exact contradiction_of_exists ξ A₀ H (exists_of_Infinite h)

-- Should I prove this?
theorem lines_inter (L L' : Set (ℝ × ℝ)) (hL : ∃ a b c, L = Line a b c)
    (hL' : ∃ a' b' c', L' = Line a' b' c') : Cardinal.mk (L ∩ L' : Set (ℝ × ℝ)) ≤ 1 := sorry
--

/- Starting from a sequence A₀ which satisfies the conditions (I), (P), (D), we build
a new sequence A of subsets of the plane which satisfies (I). We build this new sequence
by replacing an element of A₀ (at a specific rank) with the empty set. -/
theorem I_true (ξ : ordinals_lt c) (δ : ordinals_le ξ) (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (hA₀ : ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    (A : ordinals_lt c → Set (ℝ × ℝ)) (A_def : A = fun α ↦ if hα : α = ξ then ∅ else A₀ α) :
    Cardinal.mk (A ⟨δ, lt_of_le_of_lt δ.2.out ξ.2⟩) ≤ 2 := by
  by_cases hδ : δ.1 < ξ
  · have hA : A ⟨δ.1, lt_of_le_of_lt δ.2.out ξ.2⟩ = A₀ ⟨δ.1, lt_of_le_of_lt δ.2.out ξ.2⟩ := by
      rw [A_def]
      simp only [dite_eq_ite, ite_eq_right_iff]
      intro h
      exfalso
      exact ne_of_lt hδ (Subtype.ext_iff_val.1 h)
    have := (hA₀ ⟨δ.1, hδ⟩).1
    rwa [← hA] at this
  · have hA : A ⟨δ.1, lt_of_le_of_lt δ.2.out ξ.2⟩ = ∅ := by
      rw [A_def]
      simp only [dite_eq_ite, Subtype.coe_eta, eq_of_le_of_not_lt δ.2.out hδ, ↓reduceIte]
    rw [hA, Cardinal.mk_emptyCollection]
    exact Cardinal.zero_le 2

/- The sequence A is defined as above. By definition, the union of A (up to a rank δ < ξ < c)
is equal the union of A₀ up to that rank. -/
theorem ulf_eq_ulf (ξ : ordinals_lt c) (δ : ordinals_le ξ) (hδ : δ.1 < ξ)
    (A₀ : ordinals_lt c → Set (ℝ × ℝ)) (A : ordinals_lt c → Set (ℝ × ℝ))
    (A_def : A = fun α ↦ if α = ξ then ∅ else A₀ α) :
    union_le_fae A ⟨δ.1, lt_of_le_of_lt δ.2.out ξ.2⟩ =
    union_le_fae A₀ ⟨δ.1, lt_of_le_of_lt δ.2.out ξ.2⟩ := by
  simp only [union_le_fae]
  ext
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · simp only [Set.iUnion_coe_set, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hi₂⟩ := hx
    refine ⟨i, hi, ?_⟩
    rw [A_def] at hi₂
    have : ⟨i, lt_of_le_of_lt (hi.trans δ.2.out) ξ.2⟩ ≠ ξ :=
      Subtype.coe_ne_coe.1 (ne_of_lt (lt_of_le_of_lt hi hδ))
    simp only [this, ↓reduceIte] at hi₂
    exact hi₂
  · simp only [Set.iUnion_coe_set, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hi₂⟩ := hx
    refine ⟨i, hi, ?_⟩
    rw [A_def]
    have : ⟨i, lt_of_le_of_lt (hi.trans δ.2.out) ξ.2⟩ ≠ ξ :=
      Subtype.coe_ne_coe.1 (ne_of_lt (lt_of_le_of_lt hi hδ))
    simp only [this, ↓reduceIte]
    exact hi₂

/- Starting from a sequence A₀ which satisfies the conditions (I), (P), (D), we build
a new sequence A of subsets of the plane which satisfies (P) (For this, we do a proof by cases.
The first case is below.). As above, we build the new sequence by replacing an element of A₀
(at a specific rank) with the empty set. -/
theorem P_true_for_lt (ξ : ordinals_lt c) (δ : ordinals_le ξ) (hδ : δ.1 < ξ)
    (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (hA₀ : ∀ (ζ : ordinals_lt ξ.1), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    (A : ordinals_lt c → Set (ℝ × ℝ))
    (A_def : A = fun α ↦ if α = ξ then ∅ else A₀ α) :
    fae_NoThreeColinearPoints (union_le_fae A ⟨δ, lt_of_le_of_lt δ.2.out ξ.2⟩) := by
  rw [ulf_eq_ulf ξ δ hδ A₀ A A_def]
  exact (hA₀ ⟨δ.1, hδ⟩).2.1

/- Let ξ be an ordinal less than c. If the union of A₀ up to an ordinal ζ < ξ has no more
than two colinear points, then the union of all the elements of A₀ (indexed by ordinals
less than ξ) has no more than two colinear points. Otherwise, there would exist a union
of elements of A₀ (up to a specific rank) which would contain at least three colinear points
and we would get a contradiction. -/
theorem union_NoThreeColinearPoints (ξ : ordinals_lt c) (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (hA₀ : ∀ (ζ : ordinals_lt ξ.1), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    fae_NoThreeColinearPoints (⋃ (b : ordinals_lt ξ), A₀ ⟨b, b.2.out.trans ξ.2⟩) := by
  intro h
  obtain ⟨a, b, c, ha, hb, hc, h⟩ := h
  simp only [Set.iUnion_coe_set, Set.mem_iUnion] at ha hb hc
  obtain ⟨ia, hia, ha⟩ := ha
  obtain ⟨ib, hib, hb⟩ := hb
  obtain ⟨ic, hic, hc⟩ := hc
  let ζ := max ia (max ib ic)
  have hζ : ζ ∈ ordinals_lt ξ := by
    change max ia (max ib ic) < ξ.1
    simp only [max_lt_iff]
    exact ⟨hia, hib, hic⟩
  apply (hA₀ ⟨ζ, hζ⟩).2.1
  refine ⟨a, b, c, ?_, ?_, ?_, h⟩
  · rw [union_le_fae]
    simp only [Set.iUnion_coe_set, Set.mem_iUnion]
    refine ⟨ia, ?_, ha⟩
    change ia ≤ max ia (max ib ic)
    simp only [le_max_iff, le_refl, true_or]
  · rw [union_le_fae]
    simp only [Set.iUnion_coe_set, Set.mem_iUnion]
    refine ⟨ib, ?_, hb⟩
    change ib ≤ max ia (max ib ic)
    simp only [le_max_iff, le_refl, true_or, or_true]
  · rw [union_le_fae]
    simp only [Set.iUnion_coe_set, Set.mem_iUnion]
    refine ⟨ic, ?_, hc⟩
    change ic ≤ max ia (max ib ic)
    simp only [le_max_iff, le_refl, or_true]

/- If we build a new sequence A as above, taking the union of elements of A (up to a rank ξ < c)
is the same as taking the union of elements of A₀ (indexed by ordinals less than ξ). This is
because we defined the element of A (at the rank ξ) to be the empty set. -/
theorem union_eq (ξ : ordinals_lt c) (δ : ordinals_le ξ) (heq : δ = ξ.1)
    (A₀ : ordinals_lt c → Set (ℝ × ℝ)) (A : ordinals_lt c → Set (ℝ × ℝ))
    (A_def : A = fun α ↦ if α = ξ then ∅ else A₀ α) :
    ⋃ (b : ordinals_le δ), A ⟨b, lt_of_le_of_lt b.2.out (lt_of_le_of_lt δ.2 ξ.2)⟩ =
    ⋃ (b : ordinals_lt ξ), A₀ ⟨b, b.2.out.trans ξ.2⟩ := by
  ext
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · simp only [Set.iUnion_coe_set, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hi₂⟩ := hx
    by_cases hi₃ : i < ξ
    · refine ⟨i, hi₃, ?_⟩
      rw [A_def] at hi₂
      have : ⟨i, hi₃.trans ξ.2⟩ ≠ ξ := Subtype.coe_ne_coe.1 (ne_of_lt hi₃)
      simp only [this] at hi₂
      exact hi₂
    · exfalso
      rw [A_def] at hi₂
      have : i = ξ.1 := eq_of_le_of_not_lt (hi.out.trans δ.2) hi₃
      simp only [this] at hi₂
      exact Set.not_mem_empty _ hi₂
  · simp only [Set.iUnion_coe_set, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hi₂⟩ := hx
    refine ⟨i, ?_, ?_⟩
    · rw [heq]
      exact le_of_lt hi.out
    · rw [A_def]
      have : ⟨i, hi.out.trans ξ.2⟩ ≠ ξ := Subtype.coe_ne_coe.1 (ne_of_lt hi)
      simp only [this, ↓reduceDIte]
      exact hi₂

/- If we build a new sequence A as above, A satisfies the condition (D).
We do a proof by cases and contrarily to before (when we proved (I) and (P) were satisfied),
we need the hypothesis hn from "fae" (i.e. the union of A₀ up to a rank ξ < c intersects
the line indexed by ξ in exactly two points). -/
theorem D_true (ξ : ordinals_lt c) (δ : ordinals_le ξ)
    (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (hA₀ : ∀ (ζ : ordinals_lt ξ.1), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    (A : ordinals_lt c → Set (ℝ × ℝ))
    (A_def : A = fun α ↦ if α = ξ then ∅ else A₀ α)
    (hn : Nat.card ((⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    ∩ (Lines ξ) : Set (ℝ × ℝ)) = 2) :
    Nat.card ((union_le_fae A ⟨δ, lt_of_le_of_lt δ.2.out ξ.2⟩) ∩
    Lines ⟨δ, lt_of_le_of_lt δ.2.out ξ.2⟩ : Set (ℝ × ℝ)) = 2 := by
  by_cases hδ : δ.1 < ξ
  · rw [ulf_eq_ulf ξ δ hδ A₀ A A_def]
    exact (hA₀ ⟨δ.1, hδ⟩).2.2
  · have heq := eq_of_le_of_not_lt δ.2.out hδ
    have this : union_le_fae A ⟨δ, lt_of_le_of_lt δ.2.out ξ.2⟩ =
        ⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩ := by
      rw [union_le_fae, union_eq ξ δ heq A₀ A A_def]
      rfl
    rw [this]
    simp only [heq]
    exact hn

theorem rw_inter_sUnion (ξ : ordinals_lt c) (𝒢 : Set (Set (ℝ × ℝ))) :
    (Lines ξ).1 ∩ ⋃₀ 𝒢 = ⋃ ℒ, ⋃ (_ : ℒ ∈ 𝒢), (Lines ξ).1 ∩ ℒ := by
  ext
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_sUnion] at hx
    simp only [Set.mem_setOf_eq, Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_inter_iff,
      exists_and_left, exists_prop]
    exact hx
  · rw [Set.mem_iUnion₂] at hx
    obtain ⟨i, hi, hi₂, hi₃⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_sUnion]
    exact ⟨hi₂, i, hi, hi₃⟩

/- In the following proof, we start by rewriting the intersection (Lines ξ).1 ∩ ⋃₀ 𝒢
using the previous statement. It becomes a union. We can then bound it. -/
theorem card_bounded (ξ : ordinals_lt c) (𝒢 : Set (Set (ℝ × ℝ))) (B : Set (ℝ × ℝ))
    (𝒢_def : 𝒢 = {S | (2 ≤ Nat.card (S ∩ B : Set (ℝ × ℝ)) ∨ ¬(S ∩ B).Finite)
    ∧ ∃ a b c, S = Line a b c}) :
    Cardinal.mk ((Lines ξ).1 ∩ ⋃₀ 𝒢 : Set (ℝ × ℝ)) ≤ Cardinal.mk 𝒢 := by
  rw [rw_inter_sUnion]
  have : ⨆ (x : 𝒢), Cardinal.mk ((Lines ξ).1 ∩ x : Set (ℝ × ℝ)) ≤ 1 := by
    have hninter : ∀ ℒ ∈ 𝒢, Cardinal.mk ((Lines ξ).1 ∩ ℒ : Set (ℝ × ℝ)) ≤ 1 := by
      intros ℒ hℒ
      simp only [𝒢_def] at hℒ
      exact lines_inter (Lines ξ).1 ℒ (Lines ξ).2 hℒ.2
    have : Cardinal.lift.{0, 0} (iSup fun (x : 𝒢) ↦
        Cardinal.mk ((Lines ξ).1 ∩ x : Set (ℝ × ℝ))) ≤ 1 := by
        refine Cardinal.lift_iSup_le ?_ (fun ℒ ↦ ?_)
        · rw [bddAbove_def]
          refine ⟨1, fun y ⟨ℒ, hℒ⟩ ↦ ?_⟩
          rw [← hℒ]
          exact hninter ℒ ℒ.2
        · rw [Cardinal.lift_le_one_iff]
          exact (hninter ℒ ℒ.2)
    rwa [Cardinal.lift_le_one_iff] at this
  have := mul_le_mul_left' this (Cardinal.mk 𝒢)
  rw [mul_one] at this
  exact le_trans (Cardinal.mk_biUnion_le (fun ℒ ↦ (Lines ξ).1 ∩ ℒ) 𝒢) this

theorem zero_or_one {α : Type*} {S : Set α} (hS : Cardinal.mk S < 2) :
    Cardinal.mk S = 0 ∨ Cardinal.mk S = 1 := by
  obtain ⟨m, hm, hm₂⟩ := Cardinal.exists_nat_eq_of_le_nat (le_of_lt hS)
  have : m = 0 ∨ m = 1 := by
    cases' (Nat.le_iff_lt_or_eq.1 hm) with hm hm'
    · exact Nat.le_one_iff_eq_zero_or_eq_one.1 (Nat.lt_succ_iff.1 hm)
    · rw [hm'] at hm₂
      rw [hm₂] at hS
      exfalso
      exact (not_lt_of_gt hS) hS
  rwa [← Nat.cast_inj (R := Cardinal), ← Nat.cast_inj (R := Cardinal),
    Nat.cast_zero, Nat.cast_one, ← hm₂] at this

/- 𝒢 is the set of lines which intersect B at two points at least.
To bound the cardinality of 𝒢, we build an injective map from 𝒢 to B × B: we send
each line ℒ of 𝒢 to two points of ℒ ∩ B. It's injective because
given ℒ₁ and ℒ₂ two lines of 𝒢, if they both intersect B at two
points x and y, then they are equal. -/
theorem h𝒢_le (B : Set (ℝ × ℝ)) (𝒢 : Set (Set (ℝ × ℝ)))
    (𝒢_def : 𝒢 = {S | (2 ≤ Nat.card (S ∩ B : Set (ℝ × ℝ)) ∨ ¬(S ∩ B).Finite)
    ∧ ∃ a b c, S = Line a b c}) :
    Cardinal.mk 𝒢 ≤ (Cardinal.mk B)^2 := by
  rw [pow_two (Cardinal.mk B), Cardinal.mul_def]
  refine Function.Embedding.cardinal_le ⟨fun ℒ ↦ ?_, ?_⟩
  · have hℒ := ℒ.2
    simp only [𝒢_def] at hℒ
    replace hℒ := hℒ.1
    by_cases hℒ₁ : 2 ≤ Nat.card (ℒ.1 ∩ B : Set (ℝ × ℝ))
    · by_cases htwo : 2 = Nat.card (ℒ.1 ∩ B : Set (ℝ × ℝ))
      · have := htwo.symm
        rw [Nat.card_eq_two_iff] at this
        let x := this.choose.1
        have hx := this.choose.2.2
        let y := this.choose_spec.choose.1
        have hy := this.choose_spec.choose.2.2
        exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      · have := exists_of_two_lt_card (Nat.lt_of_le_of_ne hℒ₁ htwo)
        let a := this.choose
        have ha := this.choose_spec.choose_spec.choose_spec.2.2.2.1.2
        let b := this.choose_spec.choose
        have hb := this.choose_spec.choose_spec.choose_spec.2.2.2.2.1.2
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    · rw [or_iff_right hℒ₁] at hℒ
      have this := Set.Infinite.exists_subset_card_eq hℒ 3
      have ht' := this.choose_spec.1
      have ht₂ : 2 < this.choose.card := by
        rw [this.choose_spec.2]
        exact Nat.lt_add_one 2
      rw [← Nat.card_eq_finsetCard] at ht₂
      have ht₃ := exists_of_two_lt_card ht₂
      let a := ht₃.choose
      have ha := (ht' ht₃.choose_spec.choose_spec.choose_spec.2.2.2.1).2
      let b := ht₃.choose_spec.choose
      have hb := (ht' ht₃.choose_spec.choose_spec.choose_spec.2.2.2.2.1).2
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  · intros a₁ a₂ h
    by_cases ha₁ : 2 ≤ Nat.card (a₁ ∩ B : Set (ℝ × ℝ))
    · by_cases htwo : 2 = Nat.card (a₁ ∩ B : Set (ℝ × ℝ))
      · simp only [ha₁, htwo, le_refl (Nat.card (a₁ ∩ B : Set (ℝ × ℝ)))] at h
        dsimp at h
        sorry
      · sorry
    · sorry

lemma I_true_card1 (x : ℝ × ℝ) (ξ : ordinals_lt c)
    (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (hA₀ : ∀ (ζ : ordinals_lt ξ.1), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    (A : ordinals_lt c → Set (ℝ × ℝ))
    (A_def : A = fun α ↦ if α = ξ then {x} else A₀ α)
    (ζ : ordinals_le ξ.1)
    : Cardinal.mk (A ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩) ≤ 2 := by
  by_cases h : ζ < ξ.1
  · have hζ : ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ ≠ ξ := ne_of_lt h
    simp only [A_def, hζ, ↓reduceDIte, ge_iff_le]
    exact (hA₀ ⟨ζ.1, h⟩).1
  · have hζ : ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ = ξ := eq_of_le_of_not_lt ζ.2 h
    simp only [A_def, hζ, ↓reduceIte, Cardinal.mk_fintype,
      Fintype.card_ofSubsingleton, Nat.cast_one, Nat.one_le_ofNat]

lemma rw_union_le_fae (ξ : ordinals_lt c) (ζ : ordinals_le ξ.1)
    (hζ : ζ.1 < ξ.1) (x : ℝ × ℝ) (A₀ : ordinals_lt c → Set (ℝ × ℝ)) :
    union_le_fae (fun α ↦ if α = ξ then {x} else A₀ α)
    ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ = union_le_fae A₀
    ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ := by
  simp only [union_le_fae]
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · simp only [Set.iUnion_coe_set, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hi₂⟩ := hx
    have hi₃ : ⟨i, (lt_of_le_of_lt hi hζ).trans ξ.2⟩ ≠ ξ := by
      have := lt_of_le_of_lt hi.out hζ
      exact ne_of_lt this
    simp only [hi₃, ↓reduceIte] at hi₂
    exact ⟨i, hi, hi₂⟩
  · simp only [Set.iUnion_coe_set, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hi₂⟩ := hx
    refine ⟨i, hi, ?_⟩
    have hi₃ : ⟨i, (lt_of_le_of_lt hi hζ).trans ξ.2⟩ ≠ ξ := by
      have := lt_of_le_of_lt hi.out hζ
      exact ne_of_lt this
    simp only [hi₃, ↓reduceIte]
    exact hi₂

lemma mem_iUnion_of_mem_union_le_fae (x y : ℝ × ℝ) (ξ : ordinals_lt c)
    (ζ : ordinals_le ξ) (eq_ξ : ζ.1 = ξ.1)
    (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (A : ordinals_lt c → Set (ℝ × ℝ))
    (A_def : A = fun α ↦ if α = ξ then {x} else A₀ α)
    (hy : y ∈ union_le_fae A ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩) :
    y ∈ (⋃ (b : ordinals_lt ξ), A₀ ⟨b, b.2.trans ξ.2.out⟩) ∪ {x} := by
  rw [union_le_fae] at hy
  simp only [Set.iUnion_coe_set, Set.mem_iUnion,
    Set.union_singleton, Set.mem_insert_iff] at hy ⊢
  obtain ⟨i, hi, hi₂⟩ := hy
  by_cases hi₃ : i < ζ
  · have hi₄ : ⟨i, lt_of_le_of_lt (hi.trans ζ.2) ξ.2.out⟩ ≠ ξ := by
      have := lt_of_lt_of_le hi₃ ζ.2
      exact ne_of_lt this
    simp only [A_def, hi₄, ↓reduceIte] at hi₂
    right
    refine ⟨i, lt_of_lt_of_le hi₃ ζ.2, hi₂⟩
  · have := (eq_of_le_of_not_lt hi hi₃).trans eq_ξ
    simp only [A_def, this, ↓reduceIte, Set.mem_singleton_iff] at hi₂
    left
    exact hi₂

lemma mem_union_le_fae_of_mem_iUnion (ξ : ordinals_lt c) (ζ : ordinals_le ξ)
    (eq_ξ : ζ.1 = ξ.1) (A₀ : ordinals_lt c → Set (ℝ × ℝ)) (x y : ℝ × ℝ)
    (hy : y ∈ (⋃ (b : ordinals_lt ξ), A₀ ⟨b, b.2.trans ξ.2.out⟩) ∪ {x})
    (A : ordinals_lt c → Set (ℝ × ℝ))
    (A_def : A = fun α ↦ if α = ξ then {x} else A₀ α) :
    y ∈ union_le_fae A ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ := by
  rw [union_le_fae]
  simp only [Set.iUnion_coe_set, Set.mem_iUnion,
    Set.union_singleton, Set.mem_insert_iff] at hy ⊢
  cases' hy with hy₁ hy₂
  · refine ⟨ζ, Preorder.le_refl ζ, ?_⟩
    simp only [A_def, eq_ξ, ↓reduceIte, Set.mem_singleton_iff]
    exact hy₁
  · obtain ⟨i, hi, hi₂⟩ := hy₂
    rw [← eq_ξ] at hi
    refine ⟨i, le_of_lt hi.out, ?_⟩
    have hi₃ : ⟨i, lt_of_le_of_lt (le_of_lt hi.out) (lt_of_le_of_lt ζ.2 ξ.2)⟩ ≠ ξ := by
      have := lt_of_lt_of_le hi.out ζ.2.out
      exact ne_of_lt this
    simp only [A_def, hi₃, ↓reduceIte]
    exact hi₂

lemma union_le_fae_eq_iUnion (x : ℝ × ℝ) (ξ : ordinals_lt c) (ζ : ordinals_le ξ)
    (eq_ξ : ζ.1 = ξ.1) (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (A : ordinals_lt c → Set (ℝ × ℝ))
    (A_def : A = fun α ↦ if α = ξ then {x} else A₀ α) :
    union_le_fae A ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ =
    (⋃ (b : ordinals_lt ξ.1), A₀ ⟨b, b.2.out.trans ξ.2⟩) ∪ {x} := by
  ext y
  exact ⟨fun hy ↦ mem_iUnion_of_mem_union_le_fae x y ξ ζ eq_ξ A₀ A A_def hy,
    fun hy ↦ mem_union_le_fae_of_mem_iUnion ξ ζ eq_ξ A₀ x y hy A A_def⟩

lemma P_true_card1 (ξ : ordinals_lt c) (ζ : ordinals_le ξ.1)
    (A₀ : ordinals_lt c → Set (ℝ × ℝ))
    (hA₀ : ∀ (ζ : ordinals_lt ξ.1), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    (B : Set (ℝ × ℝ))
    (hB : B = ⋃₀ Set.range fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩)
    (𝒢 : Set (Set (ℝ × ℝ)))
    (𝒢_def : 𝒢 = {S | (2 ≤ Nat.card (S ∩ B : Set (ℝ × ℝ)) ∨ ¬(S ∩ B).Finite)
    ∧ ∃ a b c, S = Line a b c}) (x : ℝ × ℝ) (hx : x ∈ (Lines ξ).1 \ ⋃₀ 𝒢)
    (A : ordinals_lt c → Set (ℝ × ℝ))
    (A_def : A = fun α ↦ if α = ξ then {x} else A₀ α) :
    fae_NoThreeColinearPoints (union_le_fae A ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩) := by
  by_cases hζ : ζ.1 < ξ.1
  · have h : ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ ≠ ξ := ne_of_lt hζ
    have hf : (fun α ↦ if α = ξ then {x} else A₀ α) ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ =
        A₀ ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ := by
      simp only [h, ↓reduceIte]
    have hunion := rw_union_le_fae ξ ζ hζ x A₀
    rw [A_def, hunion]
    exact (hA₀ ⟨ζ.1, hζ⟩).2.1
  · rw [union_le_fae_eq_iUnion x ξ ζ (eq_of_le_of_not_lt ζ.2 hζ) A₀ A A_def,
      fae_NoThreeColinearPoints]
    intro h
    obtain ⟨a, b, c, ha, hb, hc, h⟩ := h
    simp only [Set.iUnion_coe_set, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_iUnion] at ha hb hc
    cases' ha with ha₁ ha₂
    · cases' hb with hb₁ hb₂
      · cases' hc with hc₁ hc₂
        · --fae_NoThreeColinearPoints might be wrong. We might have to impose that
          --the points are different from each other.
          sorry
        · sorry
      · cases' hc with hc₁ hc₂
        · sorry
        · sorry
    · cases' hb with hb₁ hb₂
      · cases' hc with hc₁ hc₂
        · sorry
        · sorry
      · cases' hc with hc₁ hc₂
        · sorry
        · sorry

/- To construct a two-point set, we will start by building a sequence {A_ξ | ξ < c}
of subsets of the Euclidean plane. This sequence will be such that ⋃ δ ≤ ξ, A_δ
will contain exactly two points of L_ξ (the line indexed by ξ).
Then, ⋃ ξ < c, A_ξ will contain exactly two points of all lines of the plane.

To construct the sequence, we suppose the sequence {A_ζ | ζ < ξ} has already been
constructed and we choose A_ξ. There are three cases:
-L_ξ intersects ⋃ ζ < ξ, A_ζ in exactly 2 points.
In this case, we pick A_ξ to be the empty set.
So, ⋃ ζ ≤ ξ, A_ζ will contain exactly 2 points from L_ξ
-L_ξ intersects ⋃ ζ < ξ, A_ζ in exactly 1 point.
In this case, A_ξ is a singleton set : we pick the point from L_ξ but it
shouldn't belong to a line which intersects ⋃ ζ < ξ, A_ζ in two points or more.
Otherwise, there's a clash with the condition (P).
-L_ξ doesn't intersect ⋃ ζ < ξ, A_ζ
In this case, we pick A_ξ = {x, y} where x, y are chosen from L_ξ in the same manner.

"fae" is the construction of the sequence. -/
theorem fae (ξ : ordinals_lt c)
  (H : ∃ A₀ : ordinals_lt c → Set (ℝ × ℝ), ∀ (ζ : ordinals_lt ξ), prop_fae A₀ ⟨ζ, ζ.2.out.trans ξ.2⟩) :
    ∃ A : ordinals_lt c → Set (ℝ × ℝ),
    ∀ ζ : ordinals_le ξ, prop_fae A ⟨ζ, lt_of_le_of_lt ζ.2.out ξ.2⟩ := by
  obtain ⟨A₀, hA₀⟩ := H
  set B := ⋃₀ Set.range (fun (ζ : ordinals_lt ξ) ↦ A₀ ⟨ζ, lt_trans ζ.2.out ξ.2⟩) with hB
  have hB_le : Cardinal.mk B < Cardinal.continuum := Cardinal.mk_sUnion_lt_continuum ξ A₀ hA₀
  let 𝒢 := {S | (2 ≤ Nat.card ↑(S ∩ B) ∨ ¬(Set.Finite ↑(S ∩ B))) ∧ ∃ a b c, S = Line a b c}
  have h𝒢_le : Cardinal.mk 𝒢 ≤ (Cardinal.mk B)^2 := h𝒢_le B 𝒢 (by rfl)
  have h𝒢_le₂ : Cardinal.mk 𝒢 < Cardinal.continuum := sorry -- or directly < Cardinal.continuum
  --(instead of proving h𝒢_le first)
  set n := Nat.card (B ∩ (Lines ξ) : Set (ℝ × ℝ)) with ndef -- Nat.card or Cardinal.mk?
  have byP : n ≤ 2 ∧ Set.Finite (B ∩ (Lines ξ)) := ⟨card_inter_line_le_two ξ A₀ hA₀,
    inter_Finite ξ A₀ hA₀⟩
  by_cases hn : n = 2
  · let Aξ : Set (ℝ × ℝ) := ∅
    set A : ordinals_lt c → Set (ℝ × ℝ) := by
      intro α
      by_cases hα : α = ξ
      exact Aξ
      exact A₀ α with A_def
    refine ⟨A, fun δ ↦ ⟨I_true ξ δ A₀ hA₀ A A_def, if hδ : δ.1 < ξ
      then P_true_for_lt ξ δ hδ A₀ hA₀ A A_def else ?_, D_true ξ δ A₀ hA₀ A A_def hn⟩⟩
    rw [union_le_fae, union_eq ξ δ (eq_of_le_of_not_lt δ.2.out hδ) A₀ A A_def]
    exact union_NoThreeColinearPoints ξ A₀ hA₀
  · have hn_ne_two : ∃ x y, x ∈ (Lines ξ).1 \ ⋃₀ 𝒢 ∧ y ∈ (Lines ξ).1 \ ⋃₀ 𝒢
        ∧ x ≠ y := by
      have hninter : Cardinal.mk ((Lines ξ).1 ∩ ⋃₀ 𝒢 : Set (ℝ × ℝ)) < Cardinal.continuum :=
        lt_of_le_of_lt (card_bounded ξ 𝒢 B (by rfl)) h𝒢_le₂
      have hninter₂ : Cardinal.mk ((Lines ξ).1 \ ⋃₀ 𝒢 : Set (ℝ × ℝ)) ≥ 2 := by
        by_contra h
        push_neg at h
        cases' (zero_or_one h) with this₁ this₂
        · have := Set.inter_eq_self_of_subset_left (Set.diff_eq_empty.1
              (Set.isEmpty_coe_sort.1 (Cardinal.mk_eq_zero_iff.1 this₁)))
          apply_fun Cardinal.mk at this
          rw [this] at hninter
          have : Cardinal.mk (Lines ξ).1 = Cardinal.continuum := sorry
          exact ne_of_lt hninter this
        · have := Cardinal.le_mk_diff_add_mk (Lines ξ).1 (⋃₀ 𝒢)
          rw [this₂] at this
          have := Cardinal.mk_sUnion_le 𝒢
          sorry
      sorry
    obtain ⟨x, y, hn_ne_two⟩ := hn_ne_two
    by_cases hn₁ : n = 1
    · let Aξ : Set (ℝ × ℝ) := {x}
      set A : ordinals_lt c → Set (ℝ × ℝ) := by
        intro α
        by_cases hα : α = ξ
        exact Aξ
        exact A₀ α with A_def
      refine ⟨A, fun ζ ↦ ⟨I_true_card1 x ξ A₀ hA₀ A A_def ζ,
        P_true_card1 ξ ζ A₀ hA₀ B hB 𝒢 (by rfl) x hn_ne_two.1 A A_def, ?_⟩⟩
      sorry
    · let Aξ : Set (ℝ × ℝ) := {x, y}
      sorry

  /- let Aξ : Set (ℝ × ℝ) :=
    if n = 2 then ∅
    else
      if n = 1 then {x}
      else {x, y}
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
    sorry -/
