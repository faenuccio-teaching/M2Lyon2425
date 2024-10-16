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
  f = g ↔ ∀ a : S, f a  = g a := by
  constructor
  · intro h
    rw [h]
    intro _
    rfl
  · intro H
    ext x
    apply H
-- `⌘`

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- The **image**


example : 1 ∈ Nat.succ '' univ := ⟨0, ⟨trivial, rfl⟩⟩
 -- use 0
 -- constructor
 -- · trivial
 -- · rfl

-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by
  intro S
  exact f '' S


example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  intro H h_false
  sorry




-- `⌘`


-- The **preimage**

example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by
  constructor
  · rw [mem_preimage]
    decide -- Lean checks every option
  · sorry




-- `⌘`

example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  intro m hm n hn
  simp
  intro H
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one] at H
  by_cases hmn: m < n
  · exfalso
    sorry


/- **§ Some exercises** -/



/- **1** The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by
  ext x
  constructor
  · intro hx
    sorry



-- **2** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) : N ∈ Nat.succ '' (EvenNaturals) := by sorry

-- **3** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) :  N ∈ Nat.succ ⁻¹' (EvenNaturals) := by sorry

-- **4** Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by sorry



/- **5** The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by sorry



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
def JustOne_fun : ℕ → ENS_Nat := sorry

--This we leave as an exercise...
def JustOne_inv : ENS_Nat → ℕ := sorry


def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by sorry

--This we leave as an exercise...
def JustOne_Right : RightInverse JustOne_inv JustOne_fun := sorry


def JustOne : ℕ ≃ ENS_Nat := sorry


inductive ENS_Or (p q : Prop) : Prop

#print ENS_Or

example (n : ENS_Nat) : ENS_Or (n = ENS_zero) (∃ m, n = ENS_succ m) := by sorry




/- **§ Some exercises** -/



-- **1** : Fill in the `sorry` in `JustOne_inv` and in `JustOne_Right`.
-- *Solutions* are above

-- **2** The successor is not surjective, but you can't rely on the library this time.
example : ¬ Surjective ENS_succ := by sorry

/- **3** Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics


-- *leave this line as it is*
open Politics

/- **4** Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics := sorry

/- **5** Prove that if someone is not on the `Right`, they are on the `Left` -/
example (a : Politics) : a ≠ Right → a = Left := by sorry

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
  | even_zero : IsEven 0
  | succ_succ (n : ℕ) : IsEven n → IsEven (n+2)


example : IsEven 4 := by sorry

example : ¬ IsEven 5 := by
  intro H
  cases' H with cdsnn h1



lemma not_isEven_succ_succ (n : ℕ) : ¬ IsEven n ↔ ¬ IsEven (n + 2) := by sorry


lemma not_IsEven_succ : ∀ n : ℕ, IsEven n ↔ ¬ IsEven (n + 1) := by sorry




/- **§ Some exercises** -/



-- **1** Recall the `repeat` tactic
example : ¬ IsEven 111 := by



-- Let's consider the *set* of even numbers satisfying `IsEven`
abbrev Evens := setOf IsEven

/- **2** Show that the two set of even numbers we defined are actually the same.
To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`. -/
lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ Evens := by sorry


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
