import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common

open Set Classical

open scoped Set
section Definitions

-- # §1: Definitions

-- **A tautology**

example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by 
  rfl

-- **The positive integers**

def PositiveIntegers : Set ℤ := by 
  intro d
  exact 0 < d

def PositiveIntegers1 : Set ℤ := by 
  
  exact fun m ↦ 0 < m --so we don't need to introduce the variable at all, the function is all that matters.
  --but more than that, we could also write it as
  --exact (0 < ·)
  --This is a standard notation used by Lean to construct this kind of things, since it is the thing we need. So we can just replace the variablre with a dot, if the expression is easy enough.

--ALSO, as the proof is just providing something, one line, exact, we can just write

def PosIntegers : Set ℤ := (0 < ·) --so we don't need to PROVE stuff. This is just the definition. Here we are constructing a thing, that's why it's def at the beginning.
--we already are using mathlib here, cause we are introducing an ordering, so lean has to know ℤ has an order relation.

-- `⌘`

--anyway we introduced sets as functions now, but for cleanliness, we'd rather have functions and sets as different stuff. 
--so instead of writing a set P : Set α as P : α → Prop, it's best to write it as "SetOf P : Set α". It's a possible thing to do in lean.

lemma one_pos : 1 ∈ PositiveIntegers := by --how to prove this?
  have := Nat.one_pos 
  rwa [← Int.ofNat_lt] at this

--lemma one_pos : 1 ∈ PositiveIntegers := Int.one_pos works as well.

def PositiveNaturals : Set ℕ := (0 < ·) 

example : 1 ∈ PositiveNaturals := by 
  exact Nat.one_pos


example : (-1 : ℤ) ∉ PositiveIntegers := by
  --by_contra works, but philosophically doing this doesn't do a proof by contradiction, uses a definition tho, so for philosophical reasons, let's do
  intro h
  have h1 := h.out
  exact (Int.negSucc_not_nonneg (1)).mp (by exact h1)

-- **The even naturals**

def EvenNaturals : Set ℕ := by
  intro d 
  exact if d % 2 = 0 then True else False 

example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  intro h 
  replace h := h.out
  rw [mem_def]
  rw [← Nat.add_mod_right] at h
  exact h


-- **An abstract set**
def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α := setOf P

-- The same, but it is a general principle that the second version is better
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := by
  rfl


-- `⌘`

-- **Subsets as implication** --"the quicker you agree with the library, the happier you will be"
-- "if you want to do something swimming around what the library has, you WILL suffer, a lot"
--so it's best to define them as implications, not as a set in the set. (If it's in the subset, then it's in the bigger set)

example {α : Type} (S T : Set α) (s : α) (hST : T ⊆ S) (ht : s ∈ T) : s ∈ S := by 
  exact hST ht


-- `⌘`

-- **A double inclusion**

example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  intro _ hs
  exact hTW (hST hs)

-- **Another take on subsets and sets as types**

def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := P

def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := by
  intro a 
  exact P a

-- Are they *equal*? This is an exercise below.

-- Why does this *fail*? How to fix it?
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (_ : x ∈ subsub P) : x.1 ∈ S := by
  exact x.2


-- **What is really this "injection"  `Set α ↪ Type`?**

example : ∀ n : PositiveIntegers, 0 ≤ n.1 := by 
  intro n 
  apply le_of_lt
  exact n.2


-- `⌘`

/- **§ Some exercises** -/

example : 1 ∉ EvenNaturals := by
  intro h 
  exact h

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := by
  intro h
  exact if h.1 % 2 = 0 then True else False

-- Why does this *fail*? How to fix it?
example : ⟨1,one_pos⟩ ∉ EvenPositiveNaturals := by
  intro h 
  exact h


-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := (· % 2 = 1)

example : 3 ∈ OddNaturals := by 
  --rw [mem_def] 
  --have : 3 % 2 = 1 := by 
    --trivial
  --exact this
  rfl


lemma lem1 (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  constructor
  · intro h h1
    replace h : n % 2 = 1 := h
    replace h1 : n % 2 = 0 := h1 --se definisco con (· % 2 = 0) allora funziona
    rw [h] at h1
    apply Nat.one_ne_zero
    exact h1
  · intro h
    replace h : ¬ n % 2 = 0 := h --again, se definisco con (· % 2 = 0) funziona
    rw [Nat.mod_two_ne_zero] at h
    assumption


-- Why does this *fail*?
example (α : Type) (S : Set α) : subsub = subsub' := sorry


end Definitions

-- # §2. Operations
-- intersection, union, universal and empty set, complement, difference.

-- S ∩ T is a set, so a function from type α to Prop. Assigns a ∈ S ∧ a ∈ T (if a : α) to a

--proving two sets are equal means proving the two functions are equal, so we can use extensionality to check for a generic value the functions are equal


section Operations

-- **Self-intersection is the identity, proven with extensionality**

example (α : Type) (S : Set α) : S ∩ S = S := by
  ext s --equality of sets → prove they have the same elements
  constructor
  · intro h 
    exact h.left --("or h.right, depends on your political inclination")
  · intro h 
    constructor
    · exact h
    · exact h


-- `⌘`


-- **The union**
--same as the intersection, but assigns an or instead of an and.
--!!!!! tho, in mathematics we can unite any two sets, here if we have a set in type α and a set in type β and we try to unite them, we get an ERROR

example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  ext s 
  constructor
  · intro h 
    cases h with
    | inl h => exact H h
    | inr h => exact h
  · intro h 
    right 
    exact h


--the universal set has as a function a ↦ True. So every element of type α belongs to the set, bc we use the constant function True
--if we used the constant function False, we'd get the empty set.

-- **Universal set**
variable (α : Type)
def universal : Set α := fun _ ↦ True --(this def is implicit in Lean, i just wrote it down, written as univ)
-- **Empty set**
def empty : Set α := fun _ ↦ False --(also this def as well. Written as ∅)

example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  ext d 
  constructor
  · rintro ⟨hd_pos, hd_neg⟩ 
    rw [mem_setOf_eq] at hd_neg hd_pos
    rw [lt_iff_not_le] at hd_neg
    apply hd_neg 
    apply le_of_lt
    exact hd_pos
  · intro h 
    exfalso 
    exact h


-- `⌘`


-- **Complement and difference**
--Sᶜ `\^c` is a negation

example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  ext s 
  constructor
  · intro _ 
    trivial
  · intro _ 
    by_cases H : s ∈ S
    · right 
      exact H
    · left 
      exact H

-- `⌘`

-- **§ Indexed unions**

example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ --ok this is basically constructor+intro
  · rw [mem_iUnion] at h
    exact h
  · rw [mem_iUnion] --cheating
    exact h
  -- *Alternative proof*
  -- rw [mem_iUnion]


example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  ext s 
  --simp only [mem_inter_iff, mem_iUnion]
  constructor 
  · --rintro ⟨xs, ⟨i, xAi⟩⟩
    intro h 
    rw [mem_iUnion]
    cases h with
    | intro left right => 
      rw [mem_iUnion] at right 
      let j := Exists.choose right 
      use j
      constructor
      · exact right.choose_spec
      · exact left
  · intro h 
    rw [mem_iUnion] at h 
    let j := Exists.choose h 
    have : s ∈ A j ∩ S := h.choose_spec
    cases this with
    | intro left right => 
      constructor
      · exact right
      · rw [mem_iUnion] 
        use j

/- **§ Some exercises** -/

-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  ext s 
  constructor
  · intro h 
    right 
    exact h
  · intro h
    cases h with
    | inl h => exact H h --apply H assumption
    | inr h => exact h --assumption

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  ext s 
  constructor
  · intro h 
    have h1 := h.left
    replace h := h.right
    cases h with
    | inl h => 
      left 
      constructor
      · exact h1
      · exact h
    | inr h => 
      right 
      constructor 
      · exact h1
      · exact h
  · intro h 
    constructor
    · cases h with
    | inl h => exact h.left
    | inr h => exact h.left
    · cases h with
    | inl h => 
      left 
      exact h.right
    | inr h => 
      right
      exact h.right


-- For this, you can try `simp` at a certain point...`le_anti+symm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  ext s 
  constructor 
  · intro h 
    cases h with
    | intro left right => 
      refine mem_singleton_of_eq ?h.mp.intro.H
      by_contra hP
      push_neg at hP
      replace hP := Ne.lt_or_lt hP
      cases hP with
      | inl h => exact Lean.Omega.Int.le_lt_asymm left h
      | inr h => exact Lean.Omega.Int.le_lt_asymm right h
  · intro h
    replace h := eq_of_mem_singleton h
    constructor
    · refine mem_setOf.mpr ?h.mpr.left.a
      exact Int.le_of_eq (Eq.symm h)
    · refine mem_setOf.mpr ?h.mpr.right.a
      exact Int.le_of_eq h

-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := by
  ext s 
  constructor 
  · intro _
    trivial
  · intro _ 
    by_cases h : s ∈ EvenNaturals 
    · left 
      exact h
    · right
      apply (lem1 s).mpr
      exact h

-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  ext s 
  constructor 
  · intro h 
    cases h with
    | intro left right => 
      replace left := h left
      trivial
  · intro h 
    exfalso 
    exact h

example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  intro s h
  cases h with
  | intro left h => 
    replace h : ¬(T s ∨ R s) := h
    push_neg at h
    constructor 
    · constructor
      · exact left
      · exact h.left
    · exact h.right


-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext s 
  constructor
  · intro h 
    rw [mem_iInter] at h 
    constructor 
    · rw [mem_iInter] 
      intro i 
      specialize h i 
      exact h.left
    · rw [mem_iInter] 
      intro i 
      specialize h i 
      exact h.right
  · intro h 
    rw [mem_iInter] 
    cases h with
    | intro left right => 
      rw [mem_iInter] at left right 
      intro i 
      specialize left i 
      specialize right i 
      constructor 
      · exact left
      · exact right

end Operations
