import Mathlib.GroupTheory.PresentedGroup
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence.Basic

/-!
# Formalising braid groups and the word problem

The point of this project is to formalise the braid group Bₙ as the Ore localisation of the monoid of positive braids pBₙ. I will try follow the proofs given by P.Dehornoy in the book "Le calcul des tresses" (Similar reasonning to the attached pdf, part II). For this two properties are required :

- Having right multiples
- Being simplifiable

I chose to work on the first of these hypothesese, working towards a proof that all generators have common right multiple.

* In the first part we define the monoid of positive braids pBₙ.

To do this we consider the positive braid word monoids p𝓑𝓦ₙ (the free monoid on "positive" crossings) and define the braid relations on those. The congruence spanned by these relations gives us the correct positive braid monoids. Now we want to apply Ore's theorem to show that the fractions of these monoids induce a group. We need pBₙ to verify the two hypotheses, that is :

* In the second part aim to show that all elements in pBₙ have a common right multiple.

We want to show that for every `a,b` there are `x,y` such that `a * x = b * y` is a common (right) multiple. To show this is the case for, we show that every pair of simple letters has a common right multiple, and extend the result to whole words.

At the time of completing this project (5th January 2025) Mathlib4's `OreSet` class requires num and denom functions satisfying an equality : it is easy to see that these are just explicit functions giving `x` and `y`. However, they are required to give a left common multiple. It happens that pBₙ also has left common multiples but we are only interested in the right case for this project.

As of Jan 5th, I was only able to reach definition of the braid Δₙ and key properties. One can show that this braid is a right multiple of any σᵢ (i < n), and extend this to Δₙˡ being right multiple of every word in p𝓑𝓦ₙ₋₁ of length at most l.
-/

/-!
## The positive braid monoids
-/

/-!
### The free monoids of positive braid words
-/

/-- The free monoids of braid words with only positive crossings -/
abbrev p𝓑𝓦  := FreeMonoid ℕ

/-- The submonoids of p𝓑𝓦 With only n strands -/
def p𝓑𝓦ₙ (n : ℕ) := Submonoid.closure (FreeMonoid.of '' { i : ℕ | i ≤ n })

-- The  p𝓑𝓦ₙ are defined as submonoids of p𝓑𝓦 to allow for easy embedding
-- of a braid of n strands in the braids of n + k strands.

/-- We give a nice characterisation of p𝓑𝓦ₙ -/
lemma p𝓑𝓦ₙ_charac (w : p𝓑𝓦) (n : ℕ) : (w ∈ p𝓑𝓦ₙ n) ↔ ∀ x, (w.contains x → x ≤ n) := by
  constructor
  · intro hw
    exact (Submonoid.closure_induction hw
    (by
      intro x hx x1 hx1
      simp at hx
      change ∃ x2 ≤ n, [x2] = x at hx
      cases hx
      · case intro x2 h =>
        rw [←h.right] at hx1
        simp at hx1
        rw [hx1]
        exact h.left
    )
    (by
      intro x
      change ([].contains x) → x ≤ n
      simp
    )
    (by
      intro xs ys ihxs ihys
      change ∀ z : ℕ, (List.append xs ys).contains z → z ≤ n
      intro z a
      simp_all only [List.elem_eq_mem, decide_eq_true_eq, List.append_eq, List.mem_append, Bool.decide_or,
        Bool.or_eq_true]
      cases a with
      | inl h => simp_all only
      | inr h_1 => simp_all only
    )
    )
  · intro h
    simp_all only [List.elem_eq_mem, decide_eq_true_eq]
    induction w
    · exact Submonoid.one_mem (p𝓑𝓦ₙ n)
    · case mpr.cons head tail ih =>
        change List.append [head] tail ∈ p𝓑𝓦ₙ n
        have hd : [head] ∈ (p𝓑𝓦ₙ n) := by
          apply Submonoid.subset_closure
          have : head ≤ n := by
            exact h head (List.mem_cons_self head tail)
          simp
          apply Exists.intro
          · apply And.intro
            on_goal 2 => {rfl
            }
            · simp_all only
        have tl : tail ∈ (p𝓑𝓦ₙ n) := by
          simp_all only [List.mem_cons, or_true, implies_true, true_implies, forall_eq_or_imp]
        exact (Submonoid.mul_mem (p𝓑𝓦ₙ n) hd tl)

/-- Every positive braid word monoid is a submonoid of the next -/
theorem p𝓑𝓦ₙ_inclusion_step (n : ℕ) : p𝓑𝓦ₙ n ≤ p𝓑𝓦ₙ (n.succ) := by
  apply Submonoid.closure_mono
  apply Set.monotone_image
  simp only [Set.le_eq_subset, Set.setOf_subset_setOf]
  intro _ h
  exact Nat.le_succ_of_le h

/-- We have a chain of inclusions between positive braid word monoids -/
theorem p𝓑𝓦ₙ_inclusion (n m : ℕ) (h : n ≤ m) : p𝓑𝓦ₙ n ≤ p𝓑𝓦ₙ m := by
  induction' h with m _ ih
  · trivial
  · trans (p𝓑𝓦ₙ m)
    · exact ih
    · apply p𝓑𝓦ₙ_inclusion_step m

/-!
### Braid relations on p𝓑𝓦 and definition of the positive braid monoid pB
-/

-- We define the braid relations on words of arbitrary size as the least congruence
-- containing the following elementary rewriting rules.

/-- σᵢσⱼ = σⱼσᵢ -/
def slide : p𝓑𝓦 → p𝓑𝓦 → Prop
  | [i, j], [a, b] => (a = j) ∧ (b = i) ∧ ((i - j ≥ 2) ∨ (j - i ≥ 2))
  | _, _ => False

/-- σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁ -/
def braiding : p𝓑𝓦 → p𝓑𝓦 → Prop
  | [i, j, k], [a, b, c] => (k = i) ∧ (a = j) ∧ (c = j) ∧ (b = i) ∧ (j = i + 1)
  | _, _ => False

def braid_relations : p𝓑𝓦 → p𝓑𝓦 → Prop := fun b1 b2 ↦ (slide b1 b2) ∨ (braiding b1 b2)

def braid_congruence : Con p𝓑𝓦 := conGen braid_relations

/-- The positive braid monoid -/
def pB := Con.Quotient braid_congruence

instance positive_braid_monoid : Monoid pB := Con.monoid braid_congruence

/-!
### Braid relations on p𝓑𝓦ₙ and definition of the positive braid monoids pBₙ
-/

-- We want to extend this structure to the submonoids 𝓑𝓦ₙ.
-- We prove that the congruence induces a congruence on each of these monoids.

/-- Slide preserves size -/
lemma slide_size (w1 w2 : p𝓑𝓦) : slide w1 w2 → w1.length = w2.length := by
  contrapose
  delta slide
  split
  all_goals simp

/-- Braiding preserves size -/
lemma braiding_size (w1 w2 : p𝓑𝓦) : braiding w1 w2 → w1.length = w2.length := by
  contrapose
  delta braiding
  split
  all_goals simp

/-- Braid relations preserve size -/
lemma braid_rel_same_size (w1 w2 : p𝓑𝓦) (h : braid_relations w1 w2)
  : w1.length = w2.length := by
  induction' h with hslide hbraiding
  · exact (slide_size w1 w2 hslide)
  · exact (braiding_size w1 w2 hbraiding)

/-- Slide preserves letters -/
lemma slide_letters (w1 w2 : p𝓑𝓦) : slide w1 w2  → (x : ℕ) → (w1.contains x ↔ w2.contains x) := by
  delta slide
  aesop

/-- Braiding preserves letters -/
lemma braiding_letters (w1 w2 : p𝓑𝓦) : braiding w1 w2 → (x : ℕ) → (w1.contains x ↔ w2.contains x) := by
  delta braiding
  aesop

/-- Braid relations preserve letters -/
lemma braid_rel_same_letters (w1 w2 : p𝓑𝓦) (hbr : braid_relations w1 w2) (i : ℕ)
  : w1.contains i ↔ w2.contains i := by
  induction' hbr with hslide hbraiding
  · exact (slide_letters _ _ hslide _)
  · exact (braiding_letters _ _ hbraiding _)

/-- Two congruent positive braid words have same length -/
theorem braid_con_same_size (w1 w2 : p𝓑𝓦) (hbc : braid_congruence w1 w2) :
  w1.length = w2.length := by
  induction' hbc
  with x y ih _ _ _ _ ih _ _ _ _ _ ih1 ih2 _ _ _ _ _ _ ih
  · exact braid_rel_same_size x y ih
  · rfl
  · rw [←ih]
  · rw [ih1, ih2]
  · case mul x y z w _ _ _ =>
    change List.length (List.append x z) = List.length (List.append y w)
    simp_all only [List.append_eq, List.length_append]

/-- Two congruent positive braid words have the same letters -/
theorem braid_con_same_letters (w1 w2 : p𝓑𝓦) (hbc : braid_congruence w1 w2) (i : ℕ) :
  w1.contains i ↔ w2.contains i := by
  induction' hbc
  with x y ih _ _ _ _ ih _ _ _ _ _ ih1 ih2 _ _ _ _ _ _ ih1 ih2
  · exact braid_rel_same_letters x y ih i
  · simp
  · exact Iff.symm ih
  · exact Iff.trans ih1 ih2
  · case mul x y z w _ _ =>
    simp
    change (i ∈ List.append x z) ↔ (i ∈ List.append y w)
    simp_all only [List.elem_eq_mem, decide_eq_true_eq, List.append_eq, List.mem_append]


/-- Two congruent positive braid words are in the same submonoid -/
lemma braid_con_same_subset (w1 w2 : p𝓑𝓦) (hbc : braid_congruence w1 w2) (n : ℕ) :
  w1 ∈ p𝓑𝓦ₙ n → w2 ∈ p𝓑𝓦ₙ n := by
  intro hw1
  rw [p𝓑𝓦ₙ_charac w1 n] at hw1
  rw [p𝓑𝓦ₙ_charac w2 n]
  intro x hx
  have : w1.contains x := by
    rw [braid_con_same_letters w1 w2 hbc x]
    exact hx
  apply hw1 x this

/-- The braid congruence can be restricted to p𝓑𝓦ₙ's -/
def braid_congruenceₙ (n : ℕ) : Con (p𝓑𝓦ₙ n) where
  r := (Set.restrict (p𝓑𝓦ₙ n) (λ w1 ↦ (Set.restrict (p𝓑𝓦ₙ n) (λ w2 ↦ braid_congruence.r w1 w2))))
  mul' := braid_congruence.mul
  iseqv := by
    constructor
    · case refl =>
        intro x ; simp ; exact (Con.eq braid_congruence).mp rfl
    · case symm =>
        intro x y ; simp ; exact fun a ↦ Con.symm braid_congruence a
    · case trans =>
        intro x y z ; simp ; exact fun a a_1 ↦ Con.trans braid_congruence a a_1

/-- This defines the pBₙ's outside of pB for potential use to model geometric braids. -/
def pBₙ_intrinsic (n : ℕ) := Con.Quotient (braid_congruenceₙ n)

instance  positive_braid_n_monoid (n : ℕ) : Monoid (pBₙ_intrinsic n) := Con.monoid (braid_congruenceₙ n)

/-- The pBₙ's are defined as the submonoids spanned by the p𝓑𝓦ₙ's. -/
def pBₙ (n : ℕ) : Submonoid pB where
  carrier := (λ x ↦ (⟦x⟧ : pB)) '' { w : p𝓑𝓦 | w ∈ (p𝓑𝓦ₙ n)}
  one_mem' := by
    simp
    apply Exists.intro
    · apply And.intro
      · apply OneMemClass.one_mem
      · rfl
  mul_mem' := by
    intro a b ha hb
    simp at ha
    simp at hb
    cases' ha with x hx
    cases' hb with y hy
    obtain ⟨_ , rightx⟩ := hx
    obtain ⟨_ , righty⟩ := hy
    have : ⟦x * y⟧ = a * b := by
      subst rightx righty
      rfl
    rw [←this]
    use (x * y)
    simp
    subst rightx righty
    apply MulMemClass.mul_mem
    · simp_all only
    · simp_all only

-- /-- One might want to show that these two monoids are the same. -/
-- def pBₙ_intrinsic_to_pBₙ (n : ℕ): MulEquiv (pBₙ_intrinsic n) (pBₙ n) where
--   toFun := sorry
--   invFun := sorry
--   left_inv := sorry
--   right_inv := sorry
--   map_mul' := sorry

/-!
## Common right multiples
-/

/-- Not sure why but writing * in the following definition does not work. -/
def p𝓑𝓦_mul (a b : p𝓑𝓦) : p𝓑𝓦 :=
  a * b

/-- σ̠ᵢⱼ is a word with nice swapping properties that we will show later on.-/
def σ_bar (i j : ℕ) : p𝓑𝓦 :=
  if (i = j) then 1 else
    if (i < j) then p𝓑𝓦_mul (.of i)  (σ_bar i.succ j)
    else p𝓑𝓦_mul (σ_bar i j.succ)  (.of j)
termination_by max (i - j) (j - i)

/-- We give an equivalent defintion for easier proofs-/
def σ_bar2 (i j : ℕ) : p𝓑𝓦 :=
  if (i = j) then 1 else
    if (i < j) then p𝓑𝓦_mul (σ_bar2 i (j - 1)) (.of (j-1))
    else p𝓑𝓦_mul (.of (i-1)) (σ_bar2 (i - 1) j)
termination_by max (i - j) (j - i)

lemma σ_bar_eq (i j : ℕ) : σ_bar i j = σ_bar2 i j := by
  induction i,j using σ_bar.induct with
  | case1 =>
    unfold σ_bar
    unfold σ_bar2
    simp
  | case2 i j hneq hinf ih1 =>
    unfold σ_bar at ih1
    unfold σ_bar2 at ih1
    simp at ih1
    split at ih1
    · case case2.isTrue heq =>
      unfold σ_bar
      unfold σ_bar2
      simp [hneq, hinf]
      delta p𝓑𝓦_mul
      unfold σ_bar
      unfold σ_bar2
      have : i = j - 1 := by exact Nat.eq_sub_of_add_eq heq
      rw [heq, this]
      simp
    · case case2.isFalse hneq2 =>
      sorry
  | case3 =>
    sorry

 lemma σ_bar_n (n : ℕ) (i j : ℕ) : (i ≤ (n + 1)) → (j ≤ (n + 1)) → (σ_bar i j) ∈ (p𝓑𝓦ₙ n) := by
  intro hi hj
  rw [p𝓑𝓦ₙ_charac (σ_bar i j) n]
  intro x
  induction i,j using σ_bar.induct with
  | case1 j =>
    unfold σ_bar
    simp
    change x ∈ [] → x ≤ n
    simp
  | case2 i j hneq hinf ih =>
    unfold σ_bar
    simp only [hneq, hinf, if_false, if_true]
    change (i :: (σ_bar i.succ j)).contains x → x ≤ n
    simp only [Nat.le_trans hinf hj, hj, true_implies, true_implies] at ih
    unfold List.contains
    unfold List.elem
    split
    · case case2.h_1 b h =>
      have : x = i := by
        simp_all only [Nat.succ_eq_add_one, List.elem_eq_mem, decide_eq_true_eq, beq_iff_eq]
      simp
      rw [this]
      exact Nat.le_of_lt_succ (LT.lt.trans_le hinf hj)
    · case case2.h_2 _ _ => apply ih
  | case3 i j hneq h ih =>
    unfold σ_bar
    simp only [hneq, h, if_false]
    change (List.append (σ_bar i j.succ) (FreeMonoid.of j)).contains x → x ≤ n
    simp
    simp only [hi, hj, true_implies] at ih
    intro hx
    rw [Nat.not_lt_eq] at h
    have : j < i := by
      exact Nat.lt_of_le_of_ne h fun a ↦ hneq (id (Eq.symm a))
    have hj : j ≤ n := by
      exact Nat.le_of_lt_succ (LE.le.trans_lt' hi this)
    cases hx
    · case case3.inl hx =>
      simp at ih
      exact ih hj hx
    · case case3.inr hx =>
        have : x = j := by
          change x ∈ [j] at hx
          simp_all only [not_lt, Nat.succ_eq_add_one, List.elem_eq_mem, decide_eq_true_eq, List.mem_singleton]
        rw [this]
        exact hj

/-- σₖ σ̠ᵢⱼ ≃  σ̠ᵢⱼ σₖ₋₁ -/
lemma σ_bar_swap_plus (i j k : ℕ) : (j ≥ i + 2) → (i < k) → (k < j)
  → braid_congruence (p𝓑𝓦_mul (.of k) (σ_bar i j)) (p𝓑𝓦_mul (σ_bar i j) (.of (k-1))) := by
  intro h1 h2 h3
  obtain ldef : ∃ l : ℕ, j = l + (i + 2) := by
    use j - (i + 2)
    rw [Nat.sub_add_cancel h1]
  cases ldef
  · case intro l hl =>
    induction l with
    | zero =>
      simp at hl
      have : k = i + 1 := by
        subst hl
        simp_all only [ge_iff_le, le_refl]
        exact Nat.eq_of_le_of_lt_succ h2 h3
      rw [hl, this]
      unfold σ_bar ; simp
      unfold σ_bar ; simp
      unfold σ_bar ; simp
      change braid_congruence [i+1, i, i+1] [i, i+1, i]
      apply braid_congruence.toSetoid.iseqv.symm
      apply ConGen.Rel.of
      delta braid_relations
      right
      delta braiding
      simp
    | succ l ih =>
      have h4 : j ≥ i + 3 := by
        rw [hl]
        conv =>
          lhs
          rw [add_assoc]
          right
          rw [add_comm, add_assoc]
          right
          simp
        rw [add_comm]
        exact Nat.le_add_right (i + 3) l
      obtain pdef : ∃ p : ℕ, k = p + i + 1 := by
        use k - (i + 1)
        exact (Nat.sub_eq_iff_eq_add h2).mp rfl
      cases pdef
      · case succ.intro p hp =>
        induction p with
        | zero =>
          simp at hp
          have : braid_congruence ((.of i.succ) * (σ_bar2 i (j - 1))) ((σ_bar2 i (j - 1)) * (.of i)) := by
            simp_all
            sorry -- TODO: involves ih
          rw [hp]
          simp
          rw [σ_bar_eq]
          unfold σ_bar2
          simp only [Nat.lt_trans h2 h3, Nat.ne_of_lt (Nat.lt_trans h2 h3), if_true, if_false]
          have trans1 : braid_congruence (p𝓑𝓦_mul (FreeMonoid.of (i + 1)) (p𝓑𝓦_mul (σ_bar2 i (j - 1)) (FreeMonoid.of (j - 1)))) (p𝓑𝓦_mul (p𝓑𝓦_mul (σ_bar2 i (j - 1)) (FreeMonoid.of i)) (FreeMonoid.of (j - 1))) := by
            change braid_congruence (p𝓑𝓦_mul (p𝓑𝓦_mul (.of (i+1)) (σ_bar2 i (j-1))) (.of (j-1))) (p𝓑𝓦_mul (p𝓑𝓦_mul (σ_bar2 i (j-1)) (.of i)) (.of (j-1)))
            exact (braid_congruence.mul this (braid_congruence.toSetoid.iseqv.refl _))
          have trans2 : braid_congruence (p𝓑𝓦_mul (p𝓑𝓦_mul (σ_bar2 i (j - 1)) (FreeMonoid.of i)) (FreeMonoid.of (j - 1))) (p𝓑𝓦_mul (p𝓑𝓦_mul (σ_bar2 i (j - 1)) (FreeMonoid.of (j - 1))) (FreeMonoid.of i)) := by
            unfold p𝓑𝓦_mul
            rw [mul_assoc, mul_assoc]
            change braid_congruence (p𝓑𝓦_mul (σ_bar2 i (j - 1)) (p𝓑𝓦_mul (FreeMonoid.of i) (FreeMonoid.of (j - 1)))) (p𝓑𝓦_mul (σ_bar2 i (j - 1)) (p𝓑𝓦_mul (FreeMonoid.of (j - 1)) (FreeMonoid.of i)))
            have : braid_congruence (p𝓑𝓦_mul (FreeMonoid.of i) (FreeMonoid.of (j - 1))) (p𝓑𝓦_mul (FreeMonoid.of (j - 1)) (FreeMonoid.of i)) := by
              apply ConGen.Rel.of
              delta braid_relations
              left
              change slide [i, j-1] [j-1, i]
              delta slide
              omega
            exact (braid_congruence.mul (braid_congruence.toSetoid.iseqv.refl _) this )
          exact (braid_congruence.trans trans1 trans2)
        | succ => sorry

lemma σ_bar_swap_minus (i j k : ℕ) : (j ≥ i + 2) → (i < k) → (k < j)
  → braid_congruence (p𝓑𝓦_mul (.of (k - 1)) (σ_bar j i)) (p𝓑𝓦_mul (σ_bar j i) (.of k)) := by
   sorry -- same thing as before, quite long

/-- Δ_bar n is a common right multiple to all small enough positive braids. -/
def Δ_bar (n : ℕ) : p𝓑𝓦 :=
  match n with
  | 0 => 1
  | n + 1 => (σ_bar 0 (n+1)) * (Δ_bar n)

#eval σ_bar 1 2
#eval Δ_bar 0
#eval Δ_bar 1
#eval Δ_bar 2
#eval Δ_bar 3

/-- This result lets us see that (Δ_bar n+1) is in p𝓑𝓦ₙ and that σᵢ can slide through if i is big enough. -/
lemma Δ_n (n : ℕ) : ∀ x, ((Δ_bar n).contains x) → (x < n ) := by
  intro x h
  induction n with
  | zero =>
    unfold Δ_bar at h
    trivial
  | succ n ih =>
    unfold Δ_bar at h
    change (List.append (σ_bar 0 (n + 1)) (Δ_bar n)).contains x at h
    simp at h
    cases h
    · case succ.inl hin =>
      have : (σ_bar 0 (n+1)) ∈ (p𝓑𝓦ₙ n) := by
        exact σ_bar_n n 0 (n+1) (Nat.le_add_left 0 (n + 1)) (Nat.le_refl (n + 1))
      apply Nat.lt_add_one_of_le
      exact (p𝓑𝓦ₙ_charac (σ_bar 0 (n+1)) n).1 this x (List.elem_eq_true_of_mem hin)
    · case succ.inr hin =>
      trans n
      simp at ih
      exact ih hin
      exact lt_add_one n


lemma slide_through_word (i : ℕ) (w : p𝓑𝓦) : (∀ x, w.contains x → x < i ) → braid_congruence ((.of (i + 1)) * w) (w * (.of (i + 1))) := by
  induction w with
  | nil =>
    intros
    change braid_congruence [i + 1] [i + 1]
    exact (Con.eq braid_congruence).mp rfl
  | cons hd tl ih =>
    intro h
    simp at h
    cases' h with hl hr
    change braid_congruence (p𝓑𝓦_mul [i + 1]  (p𝓑𝓦_mul (.of hd) tl)) (p𝓑𝓦_mul (hd :: tl) [i + 1])
    have trans1 : braid_congruence (p𝓑𝓦_mul [i + 1]  (p𝓑𝓦_mul (.of hd) tl)) (p𝓑𝓦_mul [hd] (p𝓑𝓦_mul [i + 1] tl)) := by
      conv in (p𝓑𝓦_mul [i + 1] (p𝓑𝓦_mul (FreeMonoid.of hd) tl)) =>
        delta p𝓑𝓦_mul
        rw [←mul_assoc]
      conv in (p𝓑𝓦_mul [hd] (p𝓑𝓦_mul [i + 1] tl)) =>
        delta p𝓑𝓦_mul
        rw [←mul_assoc]
      change braid_congruence (p𝓑𝓦_mul [i + 1, hd] tl) (p𝓑𝓦_mul [hd, i + 1] tl)
      have : braid_congruence [i+1, hd] [hd, i+1] := by
        apply ConGen.Rel.of
        delta braid_relations
        left
        delta slide
        simp
        left
        rw [@Nat.succ_le_iff,@Nat.lt_sub_iff_add_lt']
        exact Nat.add_lt_add_right hl 1
      exact braid_congruence.mul
        this
        ((by exact braid_congruence.toSetoid.iseqv.refl tl))
    have trans2 : braid_congruence (p𝓑𝓦_mul [hd]  (p𝓑𝓦_mul [i+1] tl)) (p𝓑𝓦_mul [hd] (p𝓑𝓦_mul tl [i + 1])) := by
      simp_all
      exact braid_congruence.mul
        (braid_congruence.toSetoid.iseqv.refl [hd])
        (ih)
    exact braid_congruence.toSetoid.iseqv.trans trans1 trans2


lemma Δ_swap (n : ℕ) : braid_congruence (Δ_bar (n+1)) ((Δ_bar n) * σ_bar (n + 1) 0) := by
  induction n with
  | zero =>
    simp [Δ_bar, σ_bar, p𝓑𝓦_mul]
    exact braid_congruence.toSetoid.iseqv.refl _
  | succ n ih =>
    match n with
    | 0 =>
      simp
      simp [Δ_bar, σ_bar, p𝓑𝓦_mul]
      rw [mul_assoc]
      exact braid_congruence.toSetoid.iseqv.refl _
    | n + 1 =>
      have trans1 : braid_congruence (Δ_bar (n + 3)) ((σ_bar 0 (n + 2)) * (.of (n + 2)) * (Δ_bar (n+1)) * (σ_bar (n+2) 0)) := by
        conv in (Δ_bar (n + 3)) => unfold Δ_bar
        rw [σ_bar_eq]
        conv in (σ_bar2 0 (n + 3)) => unfold σ_bar2
        simp
        rw [←σ_bar_eq]
        rw [mul_assoc]
        exact braid_congruence.mul (braid_congruence.toSetoid.refl _) ih
      have trans2 : braid_congruence ((σ_bar 0 (n + 2)) * (.of (n + 2)) * (Δ_bar (n+1)) * (σ_bar (n+2) 0)) ((Δ_bar (n+2)) * (σ_bar (n+3) 0)) := by
        conv in  (Δ_bar (n + 2) * σ_bar (n + 3) 0) =>
          simp [σ_bar_eq]
          rw [σ_bar2]
          simp [p𝓑𝓦_mul]
          unfold Δ_bar
          rw [←mul_assoc]
          conv in σ_bar 0 (n + 1 + 1) * Δ_bar (n + 1) * FreeMonoid.of (n + 2) =>
            rw [mul_assoc]
        conv in (σ_bar 0 (n + 2) * FreeMonoid.of (n + 2) * Δ_bar (n + 1)) =>
         rw [mul_assoc]
        rw [←σ_bar_eq]
        exact braid_congruence.mul
          (braid_congruence.mul
            (braid_congruence.toSetoid.refl (σ_bar 0 (n + 2)))
            (slide_through_word (n + 1) (Δ_bar (n+1)) (Δ_n (n+1))))
          (braid_congruence.toSetoid.refl (σ_bar (n + 2) 0))
      exact braid_congruence.toSetoid.iseqv.trans trans1 trans2

lemma Δ_invert (i n : ℕ) : (i < n) → braid_congruence ((.of i) * (Δ_bar n)) ((Δ_bar n) * (.of (n - i - 1))) := by
  intro hn
  induction n with
  | zero => trivial
  | succ n ih =>
    match n with
    | 0 =>
        have : i = 0 := by exact Nat.lt_one_iff.mp hn
        rw [this]
        simp [Δ_bar, σ_bar, p𝓑𝓦_mul,]
        exact braid_congruence.toSetoid.iseqv.refl _
    | n + 1 =>
      match i with
      | 0 =>
        simp
        have trans1 : braid_congruence (FreeMonoid.of 0 * Δ_bar (n + 1 + 1)) (FreeMonoid.of 0 * (Δ_bar (n + 1) * σ_bar (n + 2) 0)) := by
          exact braid_congruence.mul (braid_congruence.toSetoid.iseqv.refl _) (Δ_swap (n + 1))
        have trans2 : braid_congruence (FreeMonoid.of 0 * (Δ_bar (n + 1) * σ_bar (n + 2) 0)) ((Δ_bar (n + 1) * (.of n)) * σ_bar (n + 2) 0) := by
          rw [←mul_assoc]
          exact braid_congruence.mul (ih (Nat.zero_lt_succ n)) (braid_congruence.toSetoid.iseqv.refl _)
        have trans3 : braid_congruence ((Δ_bar (n + 1) * (.of n)) * σ_bar (n + 2) 0) (Δ_bar (n + 1) * ((σ_bar (n + 2) 0) * (.of (n + 1)))) := by
          rw [mul_assoc]
          exact braid_congruence.mul
            (braid_congruence.toSetoid.iseqv.refl _)
            (σ_bar_swap_minus _ _ _ (Nat.le_add_left (0 + 2) n) (Nat.zero_lt_succ n) (Nat.lt_add_one (n + 1)))
        have trans4 : braid_congruence (Δ_bar (n + 1) * ((σ_bar (n + 2) 0) * (.of (n + 1)))) (Δ_bar (n + 2) * (.of (n + 1))) := by
          rw [←mul_assoc]
          exact braid_congruence.mul (braid_congruence.toSetoid.iseqv.symm (Δ_swap (n + 1))) (braid_congruence.toSetoid.iseqv.refl _)
        exact braid_congruence.trans (
           braid_congruence.trans (
             braid_congruence.trans (trans1) trans2
          ) trans3
        ) trans4
      | i + 1 =>
        unfold Δ_bar
        have trans1 : braid_congruence ((.of (i + 1)) * (σ_bar 0 (n + 1 + 1) * Δ_bar (n + 1))) ((σ_bar 0 (n + 1 + 1) * (.of i)) * Δ_bar (n + 1)) := by
          rw [←mul_assoc]
          exact braid_congruence.mul
            (σ_bar_swap_plus _ _ _ (Nat.le_add_left (0 + 2) n) (Nat.zero_lt_succ i) hn)
            (braid_congruence.toSetoid.refl _)
        have trans2 : braid_congruence ((σ_bar 0 (n + 1 + 1) * (.of i)) * Δ_bar (n + 1)) (σ_bar 0 (n + 1 + 1) * (Δ_bar (n + 1) * (.of (n+1 - i - 1)))) := by
          rw [mul_assoc]
          exact braid_congruence.mul
            (braid_congruence.toSetoid.refl _)
            (sorry)
            /- This sorry is more tricky, and what kept me stuck. It seems we don't have the right induction hypothesis used in the book, which indicates that something is wrong in the structure of the proof. -/
        conv in (σ_bar 0 (n + 1 + 1) * Δ_bar (n + 1) * FreeMonoid.of (n + 1 + 1 - (i + 1) - 1)) =>
          rw [mul_assoc]
          simp
        exact braid_congruence.trans trans1 trans2
