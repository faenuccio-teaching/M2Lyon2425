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
  f = g ↔ ∀ a : α, (ha : a ∈ S) → f ⟨a, ha⟩ = g ⟨a, ha⟩ := by
    constructor
    · intro h
      rw [h]
      intro _ _
      rfl
    · intro h
      ext x
      apply h


-- `⌘`

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- The **image**


example : 1 ∈ Nat.succ '' univ := ⟨0, ⟨trivial, rfl⟩⟩

-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by
  intro S
  use f '' S


example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  intro H h_false
  apply H
  rw [eq_empty_iff_forall_not_mem] at h_false ⊢
  intro x hx
  sorry





-- `⌘`


-- The **preimage**

example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by
  constructor
  · rw [mem_preimage]
    decide
  · intro H
    rw [mem_preimage] at H
    trivial




-- `⌘`

example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  intro m hm n hn
  simp only
  intro H
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one] at H
  by_cases hmn : m < n
  · exfalso
    have := @Int.mul_lt_mul m m n n hmn (le_of_lt hmn) hm (le_of_lt hn)
    apply ne_of_lt this H
  · by_cases hnlt : n < m
    · exfalso
      sorry
    · apply eq_of_le_of_not_lt
      apply (le_of_not_lt hnlt)
      exact hmn






/- **§ Some exercises** -/

/- **1** The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by
  ext _
  constructor
  · intro H
    cases' H with w h
    exact ⟨w, ⟨trivial, h⟩⟩
  · intro h
    cases' h with w h
    exact ⟨w, h.2⟩

-- **2** Why does this code *fail*? Fix it, and then prove the statement
-- N is of type ↑OddNaturals and not of type ℕ
example (N : OddNaturals) : N.1 ∈ Nat.succ '' (EvenNaturals) := by
  refine ⟨N.1.pred, ⟨?_, ?_⟩⟩
  · change N.1.pred % 2 = 0
    rw [← Nat.succ_mod_two_eq_one_iff, Nat.pred_eq_sub_one, Nat.sub_one_add_one]
    exact N.2
    intro h
    have := N.2
    rw [h] at this
    change 0 % 2 = 1 at this
    rw [Nat.zero_mod] at this
    exact zero_ne_one this
  · rw [Nat.succ_pred]
    intro hn
    have := N.2
    rw [hn] at this
    change 0 % 2 = 1 at this
    rw [Nat.zero_mod] at this
    exact zero_ne_one this

-- **3** Why does this code *fail*? Fix it, and then prove the statement
-- N is of type ↑OddNaturals and not of type ℕ
example (N : OddNaturals) :  N.1 ∈ Nat.succ ⁻¹' (EvenNaturals) := by
  have := N.2
  change N.1 % 2 = 1 at this
  rwa [← Nat.succ_mod_two_eq_zero_iff] at this

-- **4** Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by
  intro H
  have := congr H (refl 0)
  rw [eq_iff_iff] at this
  have := this.2 trivial
  cases' this with w h
  contradiction

/- **5** The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ :=
  ⟨fun h _ _ _ _ hf ↦ h hf, fun h _ _ hf ↦ h trivial trivial hf⟩

/- **6** With the obvious definition of surjective, prove the following result: the
 complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by
  refine ⟨fun h ↦ ?_, fun h b ↦ ?_⟩
  · ext x
    refine ⟨fun _ ↦ ?_, fun h₂ ↦ ?_⟩
    · specialize h x
      contradiction
    · exfalso
      exact h₂
  · have := congr h (refl b)
    rw [eq_iff_iff] at this
    by_contra h₂
    exact this.1 h₂

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
  | ENS_succ a => (JustOne_inv a).succ

def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by sorry

--This we leave as an exercise...
def JustOne_Right : RightInverse JustOne_inv JustOne_fun := by
  rw [Function.RightInverse, LeftInverse]
  intro x
  induction' x with n hn
  · rfl
  · change ENS_succ (JustOne_fun (JustOne_inv n)) = n.ENS_succ
    rw [hn]

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
  cases n
  · apply ENS_Or.left
    rfl
  · apply ENS_Or.right
    sorry





/- **§ Some exercises** -/



-- **1** : Fill in the `sorry` in `JustOne_inv` and in `JustOne_Right`.
-- *Solutions* are above

-- **2** The successor is not surjective, but you can't rely on the library this time.
example : ¬ Surjective ENS_succ := by
  rw [Surjective]
  push_neg
  use ENS_zero
  intros a h
  contradiction

/- **3** Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics
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
  intro H
  cases a with
  | Right =>
      exfalso
      contradiction
  | Left => rfl

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
  | succ_succ (n : ℕ) : IsEven n → IsEven (n+2)


example : IsEven 4 := by sorry

example : ¬ IsEven 5 := by
  intro H
  cases' H with cdsnn h1
  cases' h1 with _ h2
  cases h2



lemma not_isEven_succ_succ (n : ℕ) : ¬ IsEven n ↔ ¬ IsEven (n + 2) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro hf
    cases hf
    trivial
  · intro h
    have := IsEven.succ_succ n h
    trivial

lemma not_IsEven_succ : ∀ n : ℕ, IsEven n ↔ ¬ IsEven (n + 1) := by sorry




/- **§ Some exercises** -/



-- **1** Recall the `repeat` tactic
example : ¬ IsEven 111 := by
  rw [← not_IsEven_succ 110]
  repeat constructor

-- Let's consider the *set* of even numbers satisfying `IsEven`
abbrev Evens := setOf IsEven

#print IsEven
/- **2** Show that the two set of even numbers we defined are actually the same.
To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`. -/
lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ Evens := by
  rw [mem_setOf_eq]
  induction' n with d hd
  · exact ⟨fun _ ↦ ENS.IsEven.zero_even, fun _ ↦ Nat.zero_mod 0⟩
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have d_ne_zero : d ≠ 0 := by
        intro h₂
        rw [h₂, zero_add] at h
        change 1 % 2 = 0 at h
        rw [Nat.one_mod] at h
        exact zero_ne_one h.symm
      have : d + 1 = d.pred + 2 := by
        rw [Nat.pred_eq_sub_one, add_left_inj, Nat.sub_one_add_one d_ne_zero]
      rw [this]
      apply ENS.IsEven.succ_succ
      rw [not_IsEven_succ, Nat.pred_eq_sub_one, Nat.sub_one_add_one d_ne_zero]
      intro h₂
      have := hd.2 h₂
      change d % 2 = 0 at this
      rw [← Nat.succ_mod_two_eq_one_iff] at this
      change (d+1) % 2 = 0 at h
      rw [this] at h
      exact zero_ne_one h.symm
    · rw [not_IsEven_succ] at hd
      have := (Iff.not_left hd).2 h
      change ¬(d % 2 = 0) at this
      rw [← Nat.succ_mod_two_eq_one_iff] at this
      exact (or_iff_left this).1 (d+1).mod_two_eq_zero_or_one

-- **3** Prove that every even number can be divided by `2`.
lemma exists_half (n : Evens) : ∃ d : ℕ, n = 2 * d := by
  obtain ⟨n, hn⟩ := n
  cases hn with
  | zero_even => use 0
  | succ_succ n h =>
      change n ∈ Evens at h
      rw [← EvenEq n] at h
      change n % 2 = 0 at h
      obtain ⟨r, hr⟩ := Nat.even_iff.2 h
      use r+1
      rw [Nat.mul_add, Nat.two_mul, ← hr]

noncomputable
def half : Evens → (univ : Set ℕ) := fun n ↦ ⟨(exists_half n).choose, trivial⟩

-- **4** Doubling and halving is the identity.
lemma double_half (n : Evens) : n = 2 * (half n).1 := by
  rw [half, ← Exists.choose_spec (exists_half _)]

-- **5** Some more fun with functions.
example : InjOn half univ := by
  intros x₁ hx₁ x₂ hx₂ heq
  by_contra h₂
  rw [Subtype.mk.injEq] at h₂
  push_neg at h₂
  rw [Subtype.mk.injEq] at heq
  have := congr (refl (fun x ↦ 2 * x)) heq
  rw [← double_half, ← double_half] at this
  contradiction

-- **6** Even more fun!
example : Surjective half := by
  rw [Surjective]
  intro b
  obtain ⟨b, hb⟩ := b
  induction' b with z hz
  · use ⟨0, ENS.IsEven.zero_even⟩
    by_contra h
    rw [half, Subtype.mk.injEq, ← Nat.mul_left_cancel_iff Nat.two_pos,
      ← (exists_half ⟨0, ENS.IsEven.zero_even⟩).choose_spec, Nat.mul_zero] at h
    exact h (refl 0)
  · obtain ⟨⟨a, ha⟩, ha₂⟩ := hz trivial
    use ⟨a+2, ENS.IsEven.succ_succ a ha⟩
    rw [half, Subtype.mk.injEq]
    rw [half, Subtype.mk.injEq] at ha₂
    rw [← ha₂]
    replace ha₂ := congr (refl (fun x ↦ 2*x)) ha₂
    rw [← (exists_half ⟨a, ha⟩).choose_spec] at ha₂
    have : (exists_half ⟨a+2, ENS.IsEven.succ_succ a ha⟩).choose =
      (exists_half ⟨a, ha⟩).choose +
      (exists_half ⟨2, ENS.IsEven.succ_succ 0 ENS.IsEven.zero_even⟩).choose := by
      by_contra h₂
      rw [← Nat.mul_left_cancel_iff Nat.two_pos, Nat.mul_add,
      ← (exists_half ⟨2,
      ENS.IsEven.succ_succ 0 ENS.IsEven.zero_even⟩).choose_spec,
      ← (exists_half ⟨a, ha⟩).choose_spec,
      ← (exists_half ⟨a+2, ENS.IsEven.succ_succ a ha⟩).choose_spec] at h₂
      exact h₂ (refl (a+2))
    rw [this, add_right_inj]
    by_contra h₂
    rw [← Nat.mul_left_cancel_iff Nat.two_pos,
      ← (exists_half ⟨2,
      ENS.IsEven.succ_succ 0 ENS.IsEven.zero_even⟩).choose_spec, mul_one] at h₂
    exact h₂ (refl 2)

end InductiveFamilies


end ENS
