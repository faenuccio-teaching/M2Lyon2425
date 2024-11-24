import Mathlib.GroupTheory.PresentedGroup
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Formalising braid groups and the word problem

The point of this project is to formalise the braid group Bₙ as the Ore localisation of the monoid of positive braids. I will try follow the proofs given by P.Dehornoy in the book "Le calcul des tresses" (Similar reasonning to the attached pdf, part II).

* In the first part we define the monoid of positive braids pBₙ.

To do this we consider the positive braid word monoids p𝓑𝓦ₙ (the free monoid on "positive" crossings) and define the braid relations on those. The congruence spanned by these relations gives us the correct positive braid monoids. Now we want to apply Ore's theorem to show that the fractions of these monoids induce a group. We need pBₙ to verify the two hypotheses.

* In the second part we show that all elements in pBₙ have a common right multiple.

To show that this is the case for pBₙ, we show that it is the case for simple letters then use induction on the length of the words.

* In the third part IF THERE IS TIME we will show that pBₙ is simplifiable.
A monoid is said to be simplifiable if (ab = ac => b = c <= ba = ca).
-/

/-!
## The positive braid monoids
-/

/-- The free monoids of braid words with only positive crossings -/
def p𝓑𝓦 := FreeMonoid ℕ

/-- The submonoids of p𝓑𝓦 With only n strands -/
def p𝓑𝓦ₙ (n : ℕ) := Submonoid.closure (FreeMonoid.of '' { i : ℕ | i ≤ n })

/-- Every positive braid word monoid is a submonoid of next -/
theorem p𝓑𝓦ₙ_inclusion_step (n : ℕ) : p𝓑𝓦ₙ n ≤ p𝓑𝓦ₙ (n + 1) := by
  apply Submonoid.closure_mono
  apply Set.monotone_image
  simp only [Set.le_eq_subset, Set.setOf_subset_setOf]
  intro _ h
  exact Nat.le_add_right_of_le h

/-- We have a chain of inclusions between positive braid word monoids -/
theorem p𝓑𝓦ₙ_inclusion (n m : ℕ) (h : n ≤ m) : p𝓑𝓦ₙ n ≤ p𝓑𝓦ₙ m := by
  induction h
  · trivial
  · have : p𝓑𝓦ₙ m <= p𝓑𝓦ₙ (m + 1) := p𝓑𝓦ₙ_inclusion_step m
    sorry -- Just need transitivity of submonoid relation ≤

/-- σᵢσⱼ = σⱼσᵢ -/
def slide : p𝓑𝓦 → p𝓑𝓦 → Prop := fun b1 ↦
  match b1 with
  | i :: j :: tl => fun b2 ↦ ((i - j ≥ 2) ∨ (j - i ≥ 2)) ∧
    match b2 with
    | a :: b :: tl' => (a = j) ∧ (b = i) ∧ (tl = tl')
    | _ => False
  | _ => (fun _ ↦ False)

/-- σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁ -/
def braiding : p𝓑𝓦 → p𝓑𝓦 → Prop := fun b1 ↦
  match b1 with
  | i :: j :: k :: tl => fun b2 ↦ (k = i) ∧ (j = i + 1) ∧
    match b2 with
    | a :: b :: c :: tl' => (a = i + 1) ∧ (b = i) ∧ (c = i+1) ∧ (tl = tl')
    | _ => False
  | _ => (fun _ ↦ False)

def braid_relations : p𝓑𝓦 → p𝓑𝓦 → Prop := fun b1 b2 ↦ (slide b1 b2) ∨ (braiding b1 b2)

/- IDK why the Mul structure is not inherited from Semigroup from Monoid -/
instance isMulBW : Mul p𝓑𝓦 := by exact { mul := fun a a_1 ↦ a }

def braid_congruence : Con p𝓑𝓦 := conGen braid_relations

/-- The positive braid monoid -/
def pB := Con.Quotient braid_congruence

-- We want to extend this structure to the submonoids 𝓑𝓦ₙ.
-- We prove that the congruence induces a congruence on each of these monoids.

lemma braid_rel_same_size (w1 w2 : p𝓑𝓦) (hbr : braid_relations w1 w2)
  : w1.length = w2.length := by
  induction' hbr with hbr ih
  · sorry
  · sorry

lemma braid_rel_same_letters (w1 w2 : p𝓑𝓦) (hbr : braid_relations w1 w2) (i : ℕ)
  : w1.contains i ↔ w2.contains i := by
  induction' hbr with ih ih
  · sorry
  · sorry

/-- Two congruent positive braid words have same length -/
theorem braid_con_same_size (w1 w2 : p𝓑𝓦) (hbc : braid_congruence w1 w2) :
  w1.length = w2.length := by
  induction' hbc
  with x y ih _ _ _ _ ih _ _ _ _ _ ih1 ih2 _ _ _ _ _ _ ih
  · exact braid_rel_same_size x y ih
  · rfl
  · rw [←ih]
  · rw [ih1, ih2]
  · exact ih

/-- Two congruent positive braid words have the same letters -/
theorem braid_con_same_letters (w1 w2 : p𝓑𝓦) (hbc : braid_congruence w1 w2) (i : ℕ) :
  w1.contains i ↔ w2.contains i := by
  induction' hbc
  with x y ih _ _ _ _ ih _ _ _ _ _ ih1 ih2 _ _ _ _ _ _ ih
  · exact braid_rel_same_letters x y ih i
  · simp
  · exact Iff.symm ih
  · exact Iff.trans ih1 ih2
  · exact ih

/-- Two congruent positive braid words are in the same submonoid -/
lemma braid_con_same_subset (w1 w2 : p𝓑𝓦) (hbc : braid_congruence w1 w2) (n : ℕ) :
  w1 ∈ p𝓑𝓦ₙ n → w2 ∈ p𝓑𝓦ₙ n := by sorry
  -- If every letter in w1 is < n, then by braid_con_same_letters the same goes for w2

def braid_congruenceₙ (n : ℕ) : Con (p𝓑𝓦ₙ n) where
  r := fun w1 w2 ↦ sorry
  mul' := sorry
  iseqv := sorry

def pBₙ (n : ℕ) := Con.Quotient (braid_congruenceₙ n)

/-!
## Common right multiples in pBₙ
-/
