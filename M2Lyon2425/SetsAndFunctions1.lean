import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common

open Set Classical

open scoped Set
section Definitions

-- # §1: Definitions

-- **An error**
example (α : Type) (S : Set α) :S = S :=by rfl

-- `⌘`

-- **A tautology**

example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  rfl

-- **The positive integers**

def PositiveIntegers : Set ℤ := by
  intro d
  exact 0 < d
  --exact (fun m ↦ 0 < m)
  -- exact(0 < .)
  -- pas besoin de by exact
-- `⌘`

lemma one_pos : 1 ∈ PositiveIntegers := by
  have := Nat.one_pos
  rw[← Int.ofNat_lt] at this
  exact this
  -- Int.one_this


def PositiveNaturals : Set ℕ := (0 < .)


example : 1 ∈ PositiveNaturals := by
  exact Nat.one_pos



-- Why does this *fail*? How to fix it?
example : (-1) ∉ PositiveIntegers := by
  intro h
  replace h := h.out
  omega



-- **The even naturals**

def EvenNaturals : Set ℕ := by
  intro d
  exact d % 2 = 0

example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  intro h
  have h1  : (n + 2 )% 2 = n%2 := by
    rw[add_comm]
    exact Nat.add_mod_left 2 n

  replace h := h.out
  rw[← h1] at h
  exact h



-- **An abstract set**
def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α :=  setOf P

-- The same, but it is a general principle that the second version is better
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := rfl


-- `⌘`

-- **Subsets as implication**
example {α : Type} (S T : Set α) (s : α) (hST : S ⊆ T) (hs : s ∈ S) : s ∈ T := by
  apply hST
  exact hs




-- `⌘`

-- **A double inclusion**

example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  intro x
  intro h
  apply hTW (hST h)

-- **Another take on subsets and sets as types**

def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := P

def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := by
  intro h
  exact P h
  


-- Are they *equal*? This is an exercise below.

-- Why does this *fail*? How to fix it?
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : {s : S // P s}:= by
  replace hx := hx.out
  use x


-- **What is really this "injection"  `Set α ↪ Type`?**

-- Why does this *fail*? How to fix it?
example : ∀ n : PositiveIntegers, 0 ≤ n.1 := by
  intro x
  apply le_of_lt
  exact x.2
-- pour tout , n type ici n = (a integer , the proof that its positive)

-- `⌘`

/- **§ Some exercises** -/

example : 1 ∉ EvenNaturals := by
  intro h
  replace h := h.out
  trivial


example : -1 ∉ PositiveIntegers := by
  sorry

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := by
  exact fun n ↦ (n.1)%2 = 0

-- Why does this *fail*? How to fix it?
example : ⟨ 1, one_pos⟩  ∉ EvenPositiveNaturals := by
  intro h
  have h2 := h.out
  trivial


-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ :=
  fun n ↦ n % 2 = 1


example : 3 ∈ OddNaturals := by
  rfl





example (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  constructor
  · intro h
    intro h1
    replace h := h.out
    replace h1 := h1.out
    rw[h] at h1
    apply Nat.one_ne_zero
    exact h1
  · intro h
    by_contra h1
    have h2 :=  Nat.mod_two_eq_zero_or_one n
    cases h2 with
    | inl h2 =>
      exact h h2

    | inr h2 =>
      exact h1 h2






-- Why does this *fail*?
example (α : Type) (S : Set α) : subsub = subsub' := sorry


end Definitions

-- # §2. Operations

section Operations

-- **Self-intersection is the identity, proven with extensionality**

example (α : Type) (S : Set α) : S ∩ S = S := by
  ext x
  constructor
  · intro h
    exact h.left
  · intro h
    exact And.intro h h

-- `⌘`


-- **The union**

example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  ext x
  constructor
  · intro h
    cases h with
    | inl h =>
      exact H h
    | inr h =>
      exact h
  · intro h
    right
    exact h




-- **An _unfixable_ problem**

example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry

-- `⌘`


-- **Empty set**

example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  ext d
  constructor
  · rintro ⟨ hd_pos,hd_neg ⟩
    rw[mem_setOf_eq] at hd_neg hd_pos
    rw[lt_iff_not_le] at hd_neg
    apply hd_neg
    apply le_of_lt
    exact hd_pos
  · intro h
    exfalso
    exact h






-- `⌘`


-- **Complement and difference**

example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    have  := Classical.em (S x)
    cases this with
    | inl h1 =>
      right
      exact h1
    | inr h1 =>
      left
      exact h1






-- `⌘`

-- **§ Indexed unions**

example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  exact mem_iUnion
    

#check Set.iUnion





example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  ext x
  constructor
  · intro h
    cases h with
    | intro left right => 
      simp
      constructor
      · simp at right
        obtain ⟨ w , hw ⟩ := right
        use w
      · exact left
  · intro h
    simp at h
    cases h with
    | intro left right => 
      constructor
      · exact right
      · obtain ⟨ w,hw⟩ := left
        rw[mem_iUnion]
        use w
    



/- **§ Some exercises** -/

-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  ext x
  constructor
  · intro h
    right
    exact h
  · intro h
    cases h with
    | inl h => exact H h
    | inr h => exact h

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  ext x
  constructor
  · intro h
    cases h with
    | intro left right => 
      cases right with
      | inl h => 
        left
        constructor
        · exact left
        · exact h
      | inr h => 
        right
        constructor
        · exact left
        · exact h
  · intro h
    cases h with
    | inl h => 
      constructor
      · exact h.left
      · left
        exact h.right
    | inr h => 
      constructor
      · exact h.left
      . right
        exact h.right
    
-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  ext x
  constructor
  · intro h
    cases h with
    | intro left right => 
      replace left := left.out
      replace right := right.out
      simp
      apply le_antisymm
      exact right
      exact left
  · intro h
    constructor
    · simp at h
      simp 
      rw[h]
    · simp
      simp at h
      rw[h]
  

-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    by_cases  hx :x%2 = 0
    · left
      exact hx
    · rw[Nat.mod_two_ne_zero] at hx
      right
      exact hx
  



-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  ext x
  constructor
  · intro h1
    cases h1 with
    | intro left right => 
      exact right (h left)
  . intro h
    exfalso
    exact h



example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  intro x h
  cases h with
  | intro left right => 
    constructor
    · constructor
      · exact left
      · intro h
        have : T ⊆ T ∪ R := by
          intro x h
          left
          exact h
        apply this at h
        apply right
        exact h
    · intro h
      apply right
      right
      exact h



-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  constructor
  · intro h
    rw[mem_iInter] at h
    constructor
    · rw[mem_iInter]
      intro i
      have := h i
      exact this.1
    · rw[mem_iInter]
      intro i
      have := h i
      exact this.2
  · intro h
    cases h with
    | intro left right => 
      rw[mem_iInter]
      intro i
      rw[mem_iInter] at left right
      exact ⟨ left i , right i ⟩ 



end Operations
