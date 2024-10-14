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
example (α β : Type) (f g : α  → β) : f = g ↔ ∀ a : α , f a = g a := by
  constructor
  · intro h
    intro a
    rw[h]
  · intro h
    ext x
    specialize h x
    exact h

-- # §1: A first trap
example (α β : Type) (S : Set α) (T : Set β) (f g : S → β) :
 f = g ↔ ∀ a : α , a ∈ S → f a = g a := by sorry

-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (T : Set β) (f g : S → β) :
  f = g ↔ ∀ a : α,(ha: a ∈ S) → f ⟨ a , ha⟩   = g ⟨ a, ha⟩  := by
    constructor
    · intro h
      rw[h]
      intro _ _
      rfl
    · intro h
      ext ⟨ x , hx⟩
      exact h x hx




-- `⌘`

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- The **image**


example : 1 ∈ Nat.succ '' univ := by
  rw[mem_image]
  use 0
  exact ⟨ trivial , rfl⟩

-- ⟨ 0 , ⟨ trivial , rfl ⟩ ⟩
-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by
  intro S
  exact f '' S


example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  intro h
  intro h_false
  apply h
  rw[eq_empty_iff_forall_not_mem] at h_false ⊢
  intro x hx
  replace h_false := h_false ( f x)
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
  intro m hm n hn
  simp only
  intro H
  simp only [Int.pow_succ',Int.pow_zero,Int.mul_one] at H
  by_cases hmn : m < n
  · have := @Int.mul_lt_mul m m n n hmn (le_of_lt hmn) hm (le_of_lt hn)
    exfalso
    apply ne_of_lt this H
  · by_cases hmn1 : n < m
    · have := @Int.mul_lt_mul n n m m hmn1 (le_of_lt hmn1) hn (le_of_lt hm)
      exfalso
      symm at H
      apply ne_of_lt this H
    · rw[Int.not_lt] at hmn hmn1
      symm
      exact Int.le_antisymm hmn hmn1








/- **§ Some exercises** -/



/- **1** The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by
  ext x
  constructor
  · intro h
    rw[mem_range] at h
    rw[mem_image]
    obtain ⟨ w ,hw ⟩ := h
    use w
    constructor
    · trivial
    · exact hw
  · intro h
    rw[mem_range]
    rw[mem_image] at h
    obtain ⟨ w , hw⟩ := h
    use w
    exact hw.2




-- **2** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) : N.1 ∈ Nat.succ '' (EvenNaturals) := by
  rw[mem_image]
  rcases N with ⟨ y ,Hn⟩
  have := Hn.out
  cases y with
  | zero => trivial
  | succ n =>
    use n
    constructor
    · rw[Nat.succ_mod_two_eq_one_iff] at this
      exact this
    · rw[Nat.succ_eq_add_one]



-- **3** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) :  N.1 ∈ Nat.succ ⁻¹' (EvenNaturals) := by
  rw[mem_preimage]
  rcases N with ⟨ y , Hn⟩
  have := Hn.out
  cases y with
  | zero => trivial
  | succ n =>
    rw[Nat.succ_mod_two_eq_one_iff] at this
    rw[Nat.succ_eq_add_one]
    obtain ⟨ w ,hw ⟩ := n



-- **4** Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by
  intro h
  have : ¬ (0 ∈ range Nat.succ) := by
    intro h1
    rw[mem_range] at h1
    obtain ⟨ y , hy ⟩ := h1
    rw[Nat.succ_eq_add_one y] at hy
    symm at hy
    apply Nat.zero_ne_add_one at hy
    trivial
  apply this
  rw[h]
  trivial






/- **5** The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by
  constructor
  · intro h
    rw[InjOn]
    intro x h1 y h2 H
    have := h H
    exact this
  · intro h
    rw[Injective]
    intro x y h1
    have : x ∈ univ := trivial
    have this2 : y ∈ univ := trivial
    rw[InjOn] at h
    exact h this this2 h1




/- **6** With the obvious definition of surjective, prove the following result: the
 complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by
  constructor
  · intro h
    rw[compl_empty_iff]
    ext x
    constructor
    · intro h1
      trivial
    · intro h1
      rw[Surjective] at h
      have := h x
      obtain ⟨ w ,hw ⟩ := this
      use w
  · intro h
    rw[compl_empty_iff] at h
    intro y
    have : y ∈ range f := by
      rw[h]
      trivial
    obtain ⟨ w , hw ⟩ := this
    use w



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
  | ENS_zero => 0
  | ENS_succ m => Nat.succ ( JustOne_inv m)


def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n
  induction' n with m hm
  · rfl
  · rw[JustOne_fun,JustOne_inv,hm]

--This we leave as an exercise...
def JustOne_Right : RightInverse JustOne_inv JustOne_fun := by
  intro n
  induction' n with m hm
  · rfl
  · rw[JustOne_inv,JustOne_fun,hm]



def JustOne : ℕ ≃ ENS_Nat := by
  fconstructor
  · exact JustOne_fun
  · exact JustOne_inv

  · exact JustOne_Left
  · exact JustOne_Right

-- ou where

inductive ENS_Or (p q : Prop) : Prop
  |left : p →   ENS_Or p q
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
  rw[Surjective] at h
  have := h ENS_zero
  obtain ⟨ w ,hw ⟩ := this
  trivial

/- **3** Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics
  | Right
  | Left



-- *leave this line as it is*
open Politics

/- **4** Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics := by
  exact fun h:Politics ↦ by
    cases' h
    · exact Left
    · exact Right


#check swap
#check swap Right = Right
/- **5** Prove that if someone is not on the `Right`, they are on the `Left` -/
example (a : Politics) : a ≠ Right → a = Left := by
  intro h
  cases a with
  | Right =>
    exfalso
    apply h
    rfl
  | Left =>
    trivial

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
  |zero_even : IsEven Nat.zero
  |IsEven_succ_succ n : IsEven  n →  IsEven (n + 2)

#check IsEven
#print IsEven

example : IsEven 4 := by
  apply IsEven.IsEven_succ_succ 2
  apply IsEven.IsEven_succ_succ 0
  exact IsEven.zero_even


example : ¬ IsEven 1 := by
  intro h
  cases' h

example : ¬ IsEven 5 := by
  intro h
  cases' h with _ h1
  rw[zero_add] at h1
  cases' h1 with _ h2
  cases' h2
--lean fait tt plei nde trucs tt seul

lemma not_isEven_succ_succ (n : ℕ) : ¬ IsEven n ↔ ¬ IsEven (n + 2) := by
  constructor
  · intro h
    intro h1
    cases' h1 with _ h2
    contradiction
  · intro h
    intro hmn1
    apply h
    exact (IsEven.IsEven_succ_succ n) hmn1




lemma not_IsEven_succ : ∀ n : ℕ, IsEven n ↔ ¬ IsEven (n + 1) := by
  intro n
  constructor
  · intro h
    intro h1
    rcases h with _ | ⟨ w , hw ⟩
    · cases' h1
    · rcases h1 with _ | ⟨ z , hz ⟩
      have :=  (not_IsEven_succ w ).mp hw
      exact this hz
  · intro h2
    induction' n with d hd
    · exact IsEven.zero_even
    · rw[← not_isEven_succ_succ] at h2
      replace hd := hd.mt
      push_neg at hd
      exact hd h2

/- **§ Some exercises** -/



-- **1** Recall the `repeat` tactic
example : ¬ IsEven 111 := by
  intro h
  --repeat rcases h with _ | ⟨ -, h⟩
  repeat cases' h with _ h





-- Let's consider the *set* of even numbers satisfying `IsEven`
abbrev Evens := setOf IsEven

/- **2** Show that the two set of even numbers we defined are actually the same.
To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`. -/
lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ Evens := by sorry
  constructor
  · intro h
    rw[mem_setOf_eq]
    replace h := h.out
    induction' n with m hm
    · exact IsEven.zero_even
    · rw[Nat.succ_mod_two_eq_zero_iff] at h
      rw[not_IsEven_succ]
      replace h : m ∉ EvenNaturals := by
        intro h1
        replace h1 := h1.out
        rw[h] at h1
        trivial
      have





-- **3** Prove that every even number can be divided by `2`.
lemma exists_half (n : Evens) : ∃ d : ℕ, n = 2 * d := by
  have h := n.2
  have h1 : n.1 %2 = 0 := by
    rw[← EvenEq] at h
    exact h
  have :=Nat.dvd_of_mod_eq_zero h1
  obtain ⟨ w , hw ⟩ := this
  use w



noncomputable
def half : Evens → (univ : Set ℕ) := fun n ↦ ⟨(exists_half n).choose, trivial⟩

-- **4** Doubling and halving is the identity.
lemma double_half (n : Evens) : n = 2 * (half n).1 := by
  have h1 := (exists_half n).choose
  have := (exists_half n).choose_spec

  exact this




-- **5** Some more fun with functions.
example : InjOn half univ := by
  rw[InjOn]
  intro x h y h1 H
  have h2 := double_half x
  have h3 := double_half y
  rw[H] at h2
  rw[← h2] at h3
  symm
  exact h3



-- **6** Even more fun!
example : Surjective half := by
intro b



end InductiveFamilies


end ENS
