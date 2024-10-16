import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common
import Mathlib.Order.Basic
import Mathlib.Logic.Function.Defs
import «M2Lyon2425».«SetsAndFunctions1_solutions»

-- set_option linter.unusedVariables false

namespace ENS

open Set Classical Function
section FirstTrap

-- # §1: A first trap


-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (_T : Set β) (f g : S → β) :
  f = g ↔ ∀ a : α, (ha : a ∈ S) → f ⟨a, ha⟩  = g ⟨a, ha⟩ := by
    constructor
    · intro h a ha
      rewrite [h]
      rfl
    · intro h
      ext ⟨x, hx⟩
      exact h x hx 

-- `⌘`

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- The **image**


example : 1 ∈ Nat.succ '' univ := by 
  use 0
  constructor 
  · trivial
  · omega

-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by 
  intro S 
  exact f '' S


example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  intro h1 h2 
  apply h1
  sorry

-- `⌘`


-- The **preimage**

example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by 
  constructor 
  · rw [mem_preimage]
    decide
  · intro h 
    rw [mem_preimage] at h
    trivial

-- `⌘`

example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  intro x1 hx1 x2 hx2 
  simp only
  intro h 
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one] at h
  by_cases h1l2 : x1 < x2
  · exfalso 
    have hneg := @Int.mul_lt_mul x1 x1 x2 x2 h1l2 (le_of_lt h1l2) hx1 (le_of_lt hx2)
    exact ne_of_lt hneg h 
  · by_cases h2l1 : x2 < x1
    · sorry
    · omega




/- **§ Some exercises** -/



/- **1** The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by 
  ext x 
  constructor 
  · intro h 
    simp at h ⊢
    exact h
  · intro h 
    simp at h ⊢
    exact h


-- **2** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) : N.1 ∈ Nat.succ '' (EvenNaturals) := by
  simp
  use N.1 - 1
  constructor 
  · 
    sorry
  · 
    sorry

-- **3** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) :  N.1 ∈ Nat.succ ⁻¹' (EvenNaturals) := by sorry

-- **4** Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by 
  intro h 
  
  sorry



/- **5** The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by 
  constructor 
  · intro h 
    sorry
  · sorry



/- **6** With the obvious definition of surjective, prove the following result: the
 complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by sorry

end Operations


-- # §3 : Inductive types

section InductiveTypes

inductive NiceType : Type
  | Tom : NiceType
  | Jerry : NiceType
  | f : NiceType → NiceType
  | g : ℕ → NiceType → NiceType → NiceType
open NiceType

#check NiceType
#check f (g 37 Tom Tom)

inductive ENS_Nat
| ENS_zero : ENS_Nat
| ENS_succ : ENS_Nat → ENS_Nat
open ENS_Nat

#print ENS_Nat
#check ENS_Nat

-- We want to prove that `ENS_Nat = ℕ`: they are *constructed* in the same way!
def JustOne_fun : ℕ → ENS_Nat  
  | 0 => ENS_zero
  | Nat.succ n => ENS_succ (JustOne_fun n)

--This we leave as an exercise...
def JustOne_inv : ENS_Nat → ℕ 
  | ENS_zero => 0
  | ENS_succ m => Nat.succ (JustOne_inv m)


def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n 
  induction' n with m hm 
  · rfl 
  · rw [JustOne_fun, JustOne_inv, hm]

--This we leave as an exercise...
def JustOne_Right : RightInverse JustOne_inv JustOne_fun := by
  intro n 
  cases n with
  | ENS_zero =>
    rw [JustOne_inv, JustOne_fun]
  | ENS_succ pn => 
    rw [JustOne_inv, JustOne_fun, JustOne_Right]


def JustOne : ℕ ≃ ENS_Nat where 
  toFun := JustOne_fun
  invFun := JustOne_inv
  left_inv := JustOne_Left
  right_inv := JustOne_Right


inductive ENS_Or (p q : Prop) : Prop
  | left : p → ENS_Or p q
  | right : q → ENS_Or p q

#print ENS_Or

example (n : ENS_Nat) : ENS_Or (n = ENS_zero) (∃ m, n = ENS_succ m) := by
  cases n with
  | ENS_zero =>
    apply ENS_Or.left
    rfl
  | ENS_succ m =>
    apply ENS_Or.right
    use m 

/- **§ Some exercises** -/



-- **1** : Fill in the `sorry` in `JustOne_inv` and in `JustOne_Right`.
-- *Solutions* are above

-- **2** The successor is not surjective, but you can't rely on the library this time.
example : ¬ Surjective ENS_succ := by
  intro h
  specialize h ENS_zero
  
  sorry

/- **3** Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics : Type
  | Left
  | Right


-- *leave this line as it is*
--open Politics

/- **4** Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics := by
  intro h 
  cases h with
  | Left => exact Politics.Right
  | Right => exact Politics.Left

/- **5** Prove that if someone is not on the `Right`, they are on the `Left` -/
example (a : Politics) : a ≠ Politics.Right → a = Politics.Left := by
  intro h 
  cases a with
  | Left => rfl
  | Right => exfalso; trivial

end InductiveTypes

-- # §4 : Inductive families & Inductive Predicates

section InductiveFamilies

inductive NiceProp : Prop
  | Tom : NiceProp
  | Jerry : NiceProp
  | f : NiceProp → NiceProp
  | g : ℕ → NiceProp → NiceProp → NiceProp

#check NiceProp


inductive NiceFamily : ℕ → Prop
  | Tom : NiceFamily 0
  | Jerry : NiceFamily 1
  | F : ∀n : ℕ, NiceFamily n → NiceFamily (n + 37)
  | G (n : ℕ) : ℕ → NiceFamily n → NiceFamily (n + 1) → NiceFamily (n + 3)

#check NiceFamily
#check NiceFamily 2
#check NiceFamily 21
#print NiceFamily

-- ## §4.1 : Inductive predicates

inductive IsEven : ℕ → Prop
  | zero_even : IsEven 0
  | succ_succ n : IsEven n → IsEven (n+2)


lemma IsEven_succ_succ_not (n : ℕ) : ¬ IsEven n ↔ ¬ IsEven (n + 2) := by
  constructor 
  · contrapose!
    cases n with
    | zero => 
      have p0 := IsEven.zero_even
      intro _
      exact p0
    | succ m => 
      intro h 
      cases h with 
      | succ_succ k a => 
        exact a
  · contrapose!
    exact IsEven.succ_succ n
  
lemma not_IsEven_succ : ∀ n : ℕ, IsEven n ↔ ¬ IsEven (n + 1) := by 
  intro n 
  constructor 
  · intro hn 
    cases n with
    | zero =>
      simp
      intro h 
      cases h
    | succ n =>
      intro h 
      cases h with
      | succ_succ n h =>
        exact (not_IsEven_succ n).mp h hn
  · intro hno 
    cases n with
    | zero => exact IsEven.zero_even
    | succ m => 
      cases m with
      | zero =>
        exfalso
        simp at hno 
        have f2 := IsEven.succ_succ 0 
        simp at f2
        exact hno (f2 IsEven.zero_even)
      | succ k =>
        change IsEven (k+2)
        change ¬ IsEven (k + 1 + 2) at hno
        have hno2 := (IsEven_succ_succ_not (k+1)).mpr hno 
        exact (IsEven.succ_succ k) ((not_IsEven_succ k).mpr hno2)


lemma four_is_even : IsEven 4 := by
  have p0 := IsEven.zero_even
  have f0 := IsEven.succ_succ 0
  have f2 := IsEven.succ_succ 2
  simp at f0 f2 
  exact f2 (f0 p0)

example : ¬ IsEven 5 := by
  have := (not_IsEven_succ 4).mp four_is_even
  simp at this
  exact this

/- **§ Some exercises** -/

-- **1** Recall the `repeat` tactic
example : ¬ IsEven 111 := by 
  repeat rw [←IsEven_succ_succ_not]
  have := (not_IsEven_succ 0).mp IsEven.zero_even 
  simp at this 
  exact this


-- Let's consider the *set* of even numbers satisfying `IsEven`
abbrev Evens := setOf IsEven

/- **2** Show that the two set of even numbers we defined are actually the same.
To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`. -/
lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ Evens := by
  cases n with
  | zero => 
    constructor 
    · intro _
      exact IsEven.zero_even
    · intro _ 
      change 0 % 2 = 0
      omega
  | succ m =>
    constructor 
    · intro h 
      change (m+1) % 2 = 0 at h 

      sorry
    · intro h 
      
      sorry

-- **3** Prove that every even number can be divided by `2`.
lemma exists_half (n : Evens) : ∃ d : ℕ, n = 2 * d := by sorry

noncomputable
def half : Evens → (univ : Set ℕ) := fun n ↦ ⟨(exists_half n).choose, trivial⟩

-- **4** Doubling and halving is the identity.
lemma double_half (n : Evens) : n = 2 * (half n).1 := by sorry



-- **5** Some more fun with functions.
example : InjOn half univ := by sorry


-- **6** Even more fun!
example : Surjective half := by sorry


end InductiveFamilies


end ENS
