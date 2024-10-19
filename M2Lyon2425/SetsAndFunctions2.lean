import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common
import Mathlib.Order.Basic
import Mathlib.Logic.Function.Defs
import «M2Lyon2425».«SetsAndFunctions1_solutions»

set_option linter.unusedVariables false

namespace ENS

open Set Classical Function
section FirstTrap

-- # §1: A first trap


-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (T : Set β) (f g : S → β) :
  f = g ↔ ∀ a : α, (ha : a ∈ S) → f ⟨a, ha⟩  = g ⟨ a, ha⟩  := by
constructor
· intro h
  rw[h]
  intro _ _
  rfl
· intro h
  ext x
  specialize h x x.2
  exact h
-- `⌘`

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- The **image**


example : 1 ∈ Nat.succ '' univ := ⟨ 0, ⟨ trivial, rfl⟩⟩
--use 0
--constructor
--· trivial
--· rfl

-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by
  intro S
  use f '' S


example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  intro H h_false
  apply H
  rw[eq_empty_iff_forall_not_mem] at h_false ⊢
  intro x hx
  replace h_false := h_false (f x)
  apply h_false
  use x
-- `⌘`


-- The **preimage**

example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by
  constructor
  · rw[mem_preimage]
    decide
  · intro h
    rw[mem_preimage] at h
    trivial

-- `⌘`

example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  intro m hm
  intro n hn
  simp only
  intro H
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one] at H
  by_cases hmn : m<n
  · exfalso
    have := @Int.mul_lt_mul m m n n hmn (le_of_lt hmn) hm (le_of_lt hn)
    apply ne_of_lt this H
  · by_cases hnlt : n<m
    ·exfalso
      apply hmn
      sorry
    · apply eq_of_le_of_not_lt
      apply (le_of_not_lt hnlt)
      exact hmn



/- **§ Some exercises** -/



/- **1** The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by
  ext x
  constructor
  · intro h
    have h1 := h.out
    let y := h1.choose
    let hy := Exists.choose_spec h1
    use y
    constructor
    · trivial
    · exact hy
  · intro h
    have h1 := h.out
    let a := h1.choose
    let ha := Exists.choose_spec h1
    use a
    exact ha.right


-- **2** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) : N ∈ Nat.succ '' (EvenNaturals) := by
sorry

-- **3** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) :  N ∈ Nat.succ ⁻¹' (EvenNaturals) := by sorry

-- **4** Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by
  intro h1




/- **5** The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by
constructor
· intro h
  intro x hx x2 hx2 hf
  apply h
  exact hf
· intro h
  intro a b hf
  apply h
  · trivial
  · trivial
  · exact hf


/- **6** With the obvious definition of surjective, prove the following result: the
 complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by
constructor
· intro hf
  simp
  ext x
  constructor
  · intro h
    trivial
  · intro h
    apply hf
· intro h1
  simp at h1
  intro x
  have hx : x ∈ univ := sorry
  rw [← h1] at hx
  exact hx
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
  | Nat.succ m => ENS_succ (JustOne_fun m)

--This we leave as an exercise...
def JustOne_inv : ENS_Nat → ℕ
  |ENS_zero => 0
  | ENS_succ a => Nat.succ (JustOne_inv a)


def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n
  induction' n with m hm
  · rfl
  · rw [JustOne_fun, JustOne_inv, hm]

--This we leave as an exercise...
def JustOne_Right : RightInverse JustOne_inv JustOne_fun := by
  intro n
  induction' n with m hm
  · rfl
  · rw [JustOne_inv, JustOne_fun, hm]


def JustOne : ℕ ≃ ENS_Nat where
  toFun:= JustOne_fun
  invFun:= JustOne_inv
  left_inv := JustOne_Left
  right_inv := JustOne_Right



inductive ENS_Or (p q : Prop) : Prop
  | left : p → ENS_Or p q
  |right : q → ENS_Or p q

#print ENS_Or

example (n : ENS_Nat) : ENS_Or (n = ENS_zero) (∃ m, n = ENS_succ m) := by
  cases' n with m
  · apply ENS_Or.left
    rfl
  · apply ENS_Or.right
    use m

/- **§ Some exercises** -/



-- **1** : Fill in the `sorry` in `JustOne_inv` and in `JustOne_Right`.
-- *Solutions* are above

-- **2** The successor is not surjective, but you can't rely on the library this time.
example : ¬ Surjective ENS_succ := by
  intro h
  change (∀ b, ∃ a, ENS_succ a = b) at h
  specialize h ENS_zero
  simp at h

/- **3** Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics
| Left : Politics
| Right : Politics

-- *leave this line as it is*
open Politics

/- **4** Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics
  |Right => Left
  |Left => Right

/- **5** Prove that if someone is not on the `Right`, they are on the `Left` -/
example (a : Politics) : a ≠ Right → a = Left := by
  intro h1
  by_cases h3 : a=Left
  · exact h3
  · exfalso
    apply h1
    sorry




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
  | succ_succ (n :ℕ) : IsEven n → IsEven (n+2)


example : IsEven 4 := by




example : ¬ IsEven 5 := by
  intro h
  cases' h with _ h1
  cases' h1 with _ h2
  cases h2


lemma not_isEven_succ_succ (n : ℕ) : ¬ IsEven n ↔ ¬ IsEven (n + 2) := by
  refine ⟨ fun h ↦ ?_, fun h ↦ ?_ ⟩
  · intro hf
    cases hf
    trivial
  · intro h
    have := IsEven.succ_succ n h
    trivial



lemma not_IsEven_succ : ∀ n : ℕ, IsEven n ↔ ¬ IsEven (n + 1) := by
intro n
constructor
· intro h1
  induction n with
  | zero =>
    simp
    change (IsEven 1) → False
    by_contra h2
    trivial
  | succ n ih =>
    apply ih at h1
    simp at ih
    change (IsEven (n+1+1) ) → False
    sorry
· intro h1
  sorry




/- **§ Some exercises** -/



-- **1** Recall the `repeat` tactic
example : ¬ IsEven 111 := by
intro h
cases' h with _ h1
repeat cases' h1 with _ h1
--repeat cases' h1 with IsEven h1



-- Let's consider the *set* of even numbers satisfying `IsEven`
abbrev Evens := setOf IsEven

/- **2** Show that the two set of even numbers we defined are actually the same.
To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`. -/
lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ Evens := by
constructor
· intro h1
  have h2:= h1.out
  simp
  sorry
· intro h1
  simp at h1
  rw[h1] mem_setOf_eq
  sorry


-- **3** Prove that every even number can be divided by `2`.
lemma exists_half (n : Evens) : ∃ d : ℕ, n = 2 * d := by
  sorry

noncomputable
def half : Evens → (univ : Set ℕ) := fun n ↦ ⟨(exists_half n).choose, trivial⟩

-- **4** Doubling and halving is the identity.
lemma double_half (n : Evens) : n = 2 * (half n).1 := by
  sorry



-- **5** Some more fun with functions.
example : InjOn half univ := by sorry


-- **6** Even more fun!
example : Surjective half := by sorry


end InductiveFamilies


end ENS
