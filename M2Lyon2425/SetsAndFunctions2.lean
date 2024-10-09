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
  f = g ↔ ∀ (a : α) (H : a ∈ S), f ⟨ a, H ⟩  = g ⟨ a, H ⟩ := by 
  constructor
  · intros e a h; rw [e]
  · intro h; ext ⟨ a', h' ⟩; apply h

-- `⌘`

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- The **image**

example : 1 ∈ Nat.succ '' univ := by
  use 0; constructor
  · trivial
  · rfl

-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by
  intro S
  exact (f '' S)

example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  intros h h'; apply h
  ext x; constructor
  · intro hin 
    have contra : f x ∈ f '' S := by exists x
    exfalso; rw [h'] at contra; trivial
  · intro hin; exfalso; trivial

-- `⌘`

-- The **preimage**

example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by
  constructor
  · rw [mem_preimage]; decide
  · intro h; rw [mem_preimage] at h; trivial

-- `⌘`

example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  unfold InjOn; intros x₁ hx₁ x₂ hx₂
  simp only; intro e; 
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one] at e
  by_cases hlt: x₁ < x₂
  · exfalso 
    have := Int.mul_lt_mul hlt (Int.le_of_lt hlt) hx₁.out (Int.le_of_lt hx₂.out)
    omega
  · by_cases he: x₁ = x₂
    · trivial
    · exfalso
      have h: x₂ < x₁ := by omega
      have := Int.mul_lt_mul h (Int.le_of_lt h) hx₂.out (Int.le_of_lt hx₁.out)
      omega

/- **§ Some exercises** -/

/- **1** The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by
  ext x; constructor <;> intro h
  · cases h with
    | intro y h => exists y
  · cases h with
    | intro y h => 
      cases h with
      | intro left right => exists y

-- **2** Why does this code *fail*? Fix it, and then prove the statement
example (N : ℕ) : N ∈ OddNaturals → N ∈ Nat.succ '' (EvenNaturals) := by
  unfold OddNaturals; unfold EvenNaturals; intro h; change (N % 2 = 1) at h
  use (N - 1); constructor
  · change ((N - 1) % 2 = 0)
    apply Nat.sub_mod_eq_zero_of_mod_eq; trivial
  · simp; apply Nat.sub_add_cancel; apply Nat.one_le_iff_ne_zero.mpr
    intro contra; rw [contra] at h; trivial

-- **3** Why does this code *fail*? Fix it, and then prove the statement
example (N : ℕ) : N ∈ OddNaturals → N ∈ Nat.succ ⁻¹' (EvenNaturals) := by
  unfold OddNaturals; unfold EvenNaturals; intro h; change (N % 2 = 1) at h
  rw [mem_preimage]; change (N.succ % 2 = 0); omega

-- **4** Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by 
  intro e
  have h: 0 ∉ range Nat.succ := by
    intro hin; cases hin with
    | intro k h => trivial
  rw [e] at h; trivial

/- **5** The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by
  constructor <;> unfold Injective <;> unfold InjOn <;> intro h
  · intros x₁ hx₁ x₂ hx₂; apply h
  · intros x₁ x₂ h'; apply h <;> trivial

/- **6** With the obvious definition of surjective, prove the following result: the
 complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by
  unfold Surjective; constructor <;> intro h
  · ext x; constructor <;> intro hx
    · apply not_mem_of_mem_compl at hx; unfold range at hx 
      exfalso; apply hx; apply h
    · exfalso; trivial
  · intros b; apply compl_empty_iff.mp at h; unfold range at h
    apply eq_univ_iff_forall.mp at h; apply h

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
  | n + 1 => ENS_succ (JustOne_fun n)

--This we leave as an exercise...
def JustOne_inv : ENS_Nat → ℕ 
  | ENS_zero => 0
  | ENS_succ n => (JustOne_inv n) + 1

def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [JustOne_fun, JustOne_inv, ih]

--This we leave as an exercise...
def JustOne_Right : RightInverse JustOne_inv JustOne_fun := by
  intro n
  induction n with
  | ENS_zero => rfl
  | ENS_succ n ih => rw [JustOne_inv, JustOne_fun, ih]

def JustOne : ℕ ≃ ENS_Nat where
  toFun := JustOne_fun
  invFun := JustOne_inv
  left_inv := JustOne_Left
  right_inv := JustOne_Right

inductive ENS_Or (p q : Prop) : Prop
  | ENS_inl : p → ENS_Or p q
  | ENS_inr : q → ENS_Or p q

#print ENS_Or

example (n : ENS_Nat) : ENS_Or (n = ENS_zero) (∃ m, n = ENS_succ m) := by
  cases n with
  | ENS_zero => exact ENS_Or.ENS_inl rfl
  | ENS_succ n => apply ENS_Or.ENS_inr; exists n

/- **§ Some exercises** -/

-- **1** : Fill in the `sorry` in `JustOne_inv` and in `JustOne_Right`.
-- *Solutions* are above

-- **2** The successor is not surjective, but you can't rely on the library this time.
example : ¬ Surjective ENS_succ := by
  unfold Surjective; intro contra
  have := contra ENS_zero
  cases this with
  | intro k h => trivial

/- **3** Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics : Prop
  | Right : Politics
  | Left : Politics

-- *leave this line as it is*
open Politics

/- **4** Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics
  | Right => Left
  | Left => Right

/- **5** Prove that if someone is not on the `Right`, they are on the `Left` -/
example (a : Politics) : a ≠ Right → a = Left := by
  cases a with
  | Right => intro contra; trivial
  | Left => intro _; rfl

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
| IsEvenZ : IsEven 0
| IsEvenSS : ∀ n, IsEven n → IsEven (n + 2)

example : IsEven 4 := by 
  repeat constructor

example : ¬ IsEven 5 := by
  intro h; cases h with | IsEvenSS _ h => cases h with | IsEvenSS _ h => contradiction

lemma not_isEven_succ_succ (n : ℕ) : ¬ IsEven n ↔ ¬ IsEven (n + 2) := by
  constructor
  · intros h hSS; apply h; cases hSS with | IsEvenSS _ hSS => trivial
  · intros hSS h; apply hSS; constructor; trivial

lemma not_IsEven_succ : ∀ n : ℕ, IsEven n ↔ ¬ IsEven (n + 1) := by
  intro n; constructor
  · intros h hS; induction h with
    | IsEvenZ => contradiction
    | IsEvenSS n h ih => cases hS with | IsEvenSS _ h => trivial
  · intros hS; induction n with
    | zero => constructor
    | succ n ih => by_contra hnS; apply ih at hnS; apply hS; constructor; trivial

/- **§ Some exercises** -/

-- **1** Recall the `repeat` tactic
example : ¬ IsEven 111 := by
  intro h
  repeat (cases h with | IsEvenSS _ h => _)
  contradiction

-- Let's consider the *set* of even numbers satisfying `IsEven`
abbrev Evens := setOf IsEven

/- **2** Show that the two set of even numbers we defined are actually the same.
To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`. -/
lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ Evens := by
  induction n with
  | zero => constructor <;> intro h
            · constructor
            · trivial
  | succ n ih => 
      constructor <;> intro h
      · rw [mem_setOf_eq, not_IsEven_succ]
        replace h := h.out
        rw [Nat.succ_mod_two_eq_zero_iff] at h
        have h' : n ∉ EvenNaturals := by
          intro h'; replace h' := h'.out; omega
        have : n ∉ Evens ↔ n ∉ EvenNaturals := by
          constructor <;> contrapose <;> simp
          · exact ih.mp
          · exact ih.mpr
        rw [←not_isEven_succ_succ]
        rw [←this] at h'; intro he; apply h'; rw [mem_setOf_eq]; trivial
      · rw [mem_setOf_eq] at ih
        rw [mem_setOf_eq, not_IsEven_succ, ←not_isEven_succ_succ, ←ih] at h
        change ((n + 1) % 2 = 0); change (n % 2 ≠ 0) at h; omega

-- **3** Prove that every even number can be divided by `2`.
lemma exists_half (n : Evens) : ∃ d : ℕ, n = 2 * d := by
  cases n with
  | mk n h => 
    apply mem_setOf_eq.mp at h
    induction h with
    | IsEvenZ => use 0
    | IsEvenSS n h ih =>
      simp; apply mem_setOf_eq.mp at h; 
      cases h with 
      | IsEvenSS n h => specialize ih h; cases ih with 
                        | intro k h => use (k + 1); simp at h; omega

noncomputable
def half : Evens → (univ : Set ℕ) := fun n ↦ ⟨(exists_half n).choose, trivial⟩

-- **4** Doubling and halving is the identity.
lemma double_half (n : Evens) : n = 2 * (half n).1 := by
  cases n with
  | mk n h =>
    apply mem_setOf_eq.mp at h
    unfold half
    let x := (exists_half ⟨ n, h ⟩).choose
    have := (exists_half ⟨ n, h ⟩).choose_spec
    trivial

-- **5** Some more fun with functions.
example : InjOn half univ := by
  intro ⟨ n, hn ⟩ _ ⟨ m, hm ⟩ _ e
  have hn': n = 2 * (half ⟨ n, hn ⟩).1 := by apply double_half ⟨ n, hn ⟩
  have hm': m = 2 * (half ⟨ m, hm ⟩).1 := by apply double_half ⟨ m, hm ⟩
  apply Subtype.mk_eq_mk.mpr; rw [hn', hm', e]

-- **6** Even more fun!
example : Surjective half := by
  intro ⟨ x, _ ⟩
  have ha: ∀ k, IsEven (2 * k) := by
    intros k; induction k with
    | zero => constructor
    | succ n ih => constructor; trivial
  use ⟨ 2 * x, ha x ⟩; unfold half
  let k := (exists_half ⟨ 2 * x, ha x ⟩).choose
  have := (exists_half ⟨ 2 * x, ha x ⟩).choose_spec
  simp at * 
  have ne: 2 ≠ 0 := by trivial
  apply (Nat.mul_right_inj ne).mp; apply Eq.symm; trivial  

end InductiveFamilies

end ENS
