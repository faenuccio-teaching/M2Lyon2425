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


example (α β : Type) (S : Set α) (T : Set β) (f g : S → β) : 
  f = g ↔ ∀ a : α, (ha: a ∈ S) → f ⟨a,ha⟩  = g ⟨a,ha⟩ := by  
  constructor
  · intro h 
    rw [h]
    intro _ _ 
    rfl
  · intro h 
    --ext ⟨s,hs⟩ this also introduces the proof that s is of type ↑S 
    ext s 
    specialize h s.1 s.2 --s ∈ ↑S as introduced, so it is a pair, the proof that S s.1 is True is s.2
    exact h

-- `⌘`

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- The **image**


example : 1 ∈ Nat.succ '' univ := ⟨0, ⟨trivial, rfl⟩ ⟩ --an existential statement is a pair of something and a proof that satisfies something else. 

-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by 
  intro S 
  use f '' S


example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by 
  intro h h_f
  apply h
  rw [eq_empty_iff_forall_not_mem] at h_f ⊢ 
  intro x hx  
  replace h_f := h_f (f x)
  apply h_f 
  exact mem_image_of_mem f hx


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
  intro m hm n hn 
  simp only 
  intro H 
  simp only [Int.pow_succ',Int.pow_zero,Int.mul_one] at H 
  by_cases hmn : m < n
  · exfalso
    have := @Int.mul_lt_mul m m n n hmn (le_of_lt hmn) hm (le_of_lt hn)
    apply ne_of_lt this H 
  · by_cases hnlt : n < m
    · exfalso 
      have := @Int.mul_lt_mul n n m m hnlt (le_of_lt hnlt) hn (le_of_lt hm)
      apply ne_of_gt this H
    · apply eq_of_le_of_not_lt
      apply (le_of_not_lt hnlt)
      exact hmn




/- **§ Some exercises** -/



/- **1** The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by 
  ext s 
  constructor
  · intro h 
    rw [mem_range] at h
    let Y := h.choose_spec
    let y := Exists.choose h
    use y
    constructor
    · trivial
    · exact Y
  · intro h 
    rw [mem_range]
    let Y := h.choose_spec.right
    let y := Exists.choose h
    use y


-- **2** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) : N.1 ∈ Nat.succ '' (EvenNaturals) := by
  let n := N.1
  have hn := N.2.out
  by_cases H : N.1 = 0 
  · exfalso 
    rw [H] at hn 
    trivial
  · replace H : ¬n = 0 := H
    use Nat.pred n 
    constructor 
    · have : n.pred % 2 = 0 := by
        apply Nat.succ_mod_two_eq_one_iff.mp 
        rw [← Nat.succ_eq_add_one n.pred, @Nat.succ_pred n H]
        exact hn
      exact this
    · exact Nat.succ_pred_eq_of_ne_zero H

-- **3** Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) :  N.1 ∈ Nat.succ ⁻¹' (EvenNaturals) := by 
  let n := N.1 
  have hn :=N.2.out 
  simp
  have : (n + 1) % 2 = 0 := by 
    apply Nat.succ_mod_two_eq_zero_iff.mpr 
    exact hn
  exact this

-- **4** Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by 
  intro h 
  have h1 : 0 ∈ univ := trivial 
  rw [← h] at h1
  let y := Exists.choose h1 
  have Y := h1.choose_spec
  have : 0 < y.succ := by
    apply @Nat.succ_pos' y 
  trivial



/- **5** The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by 
  constructor 
  · intro h x _ y _ 
    exact fun a ↦ h a
  · intro h x y
    have hx : x ∈ univ := trivial 
    have hy : y ∈ univ := trivial 
    exact fun a ↦ h hx hy a



/- **6** With the obvious definition of surjective, prove the following result: the
 complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by 
  constructor 
  · intro h
    simp 
    ext s 
    constructor 
    · intro _ 
      trivial
    · intro _ 
      exact h s
  · simp 
    intro h x
    have : x ∈ univ := trivial 
    rw [← h] at this 
    let y := Exists.choose this 
    have Y := this.choose_spec
    use y

end Operations

-- # §3 : Inductive types

section InductiveTypes

inductive NiceType : Type
  | Tom : NiceType
  | Jerry : NiceType
  | f : NiceType → NiceType
  | g : ℕ → (NiceType → (NiceType → NiceType))
open NiceType

#check NiceType
#check f (g 37 Tom Tom)

inductive ENS_Nat
| ENS_zero : ENS_Nat
| ENS_succ : ENS_Nat → ENS_Nat  --there is an implicit injectivity of this function
open ENS_Nat

#print ENS_Nat
#check ENS_Nat

-- We want to prove that `ENS_Nat = ℕ`: they are *constructed* in the same way!
def JustOne_fun : ℕ → ENS_Nat 
  | 0 => ENS_zero
  | Nat.succ m => ENS_succ (JustOne_fun m) --we use the function inside its definition, recursive, but makes sense, bc we tie it to succ, so we can assume we have just defined the function on m.

--This we leave as an exercise...
def JustOne_inv : ENS_Nat → ℕ
  | ENS_zero => 0
  | ENS_succ a => Nat.succ (JustOne_inv a)

def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by 
  intro n 
  induction' n with m hm 
  · rfl
  · rw [JustOne_fun, JustOne_inv, hm]

--This we leave as an exercise...
def JustOne_Right : RightInverse JustOne_inv JustOne_fun := by
    intro a 
    induction' a with b hb 
    · rfl
    · rw [JustOne_inv, JustOne_fun, hb]


def JustOne : ℕ ≃ ENS_Nat := by --why not equal? Bc they're defined as different types, with different names. at most they're isomorphic.
  fconstructor
  · exact JustOne_fun 
  · exact JustOne_inv
  · exact JustOne_Left
  · exact JustOne_Right

  --another better way to write this would be 
  
  def JustOne₁ : ℕ ≃ ENS_Nat where
    toFun := JustOne_fun
    invFun := JustOne_inv
    left_inv := JustOne_Left
    right_inv := JustOne_Right


inductive ENS_Or (p q : Prop) : Prop --no base case, this constructs, we want a term of type ENS_Or if p or q are True. If there was a base case then p or q would always be true. Induction only means "provide a proof for all cases", not the classical induction, which is a special case.
  | left : p → ENS_Or p q
  | right : q → ENS_Or p q

#print ENS_Or

example (n : ENS_Nat) : ENS_Or (n = ENS_zero) (∃ m, n = ENS_succ m) := by 
  cases' n  with m --the ' allows to add the name m to the inaccessible variable
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
  specialize h ENS_zero   
  simp only [exists_false] at h

/- **3** Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics
  | Right : Politics
  | Left : Politics


-- *leave this line as it is*
open Politics

/- **4** Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics 
  | Politics.Right => Politics.Left
  | Politics.Left => Politics.Right

/- **5** Prove that if someone is not on the `Right`, they are on the `Left` -/
example (a : Politics) : a ≠ Right → a = Left := by 
  intro _
  cases a
  · exfalso 
    trivial
  · trivial

end InductiveTypes

-- # §4 : Inductive families & Inductive Predicates

section InductiveFamilies

inductive NiceProp : Prop
  | Tom : NiceProp
  | Jerry : NiceProp
  | f : NiceProp → NiceProp
  | g : ℕ → NiceProp → NiceProp → NiceProp

#check NiceProp


inductive NiceFamily : ℕ → Prop --not a type, but a family of types. Still not a type
  | Tom : NiceFamily 0
  | Jerry : NiceFamily 1
  | F : ∀n : ℕ, NiceFamily n → NiceFamily (n + 37)
  | G (n : ℕ) : ℕ → NiceFamily n → NiceFamily (n + 1) → NiceFamily (n + 3)

#check NiceFamily
#check NiceFamily 2
#check NiceFamily 21
#print NiceFamily

-- ## §4.1 : Inductive predicates

inductive IsEven : ℕ → Prop --"the falsest proposition that is true only for the things that follow"
  | zero_even : IsEven 0
  | succ_succ (n : ℕ) : IsEven n → IsEven (n+2)


example : IsEven 4 := by 
    apply IsEven.succ_succ
    apply IsEven.succ_succ 
    exact IsEven.zero_even

example : ¬ IsEven 5 := by 
  intro H
  cases' H with _ h1 --produces only one case bc lean sees that the other produces smth of type IsEven 0 and we want IsEven 5 so it understands it's useless 
  cases' h1 with _ h2
  cases h2

lemma not_isEven_succ_succ (n : ℕ) : ¬ IsEven n ↔ ¬ IsEven (n + 2) := by 
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ --the goal is iff, it means "in the first direction use a function that sends h to something (and then we're left with proving something, and introduces h as well) and viceversa" 
  · intro hf 
    cases hf
    trivial
  · intro h 
    have := IsEven.succ_succ n h 
    trivial


lemma not_IsEven_succ : ∀ n : ℕ, IsEven n ↔ ¬ IsEven (n + 1) := by 
    intro n 
    refine ⟨fun h ↦ ?_ , fun h ↦ ?_⟩
    · intro h1 
      induction' n with m hm 
      · cases h1
      · cases' h1 with _ h2
        apply hm
        · exact h2
        · exact h
    · induction' n with m hm
      · exact IsEven.zero_even
      · by_contra h1 
        replace h1 : IsEven (m + 2) := IsEven.succ_succ m (hm h1)
        trivial
        




/- **§ Some exercises** -/



-- **1** Recall the `repeat` tactic
example : ¬ IsEven 111 := by 
    intro h 
    repeat cases' h with _ h


-- Let's consider the *set* of even numbers satisfying `IsEven`
abbrev Evens := setOf IsEven

/- **2** Show that the two set of even numbers we defined are actually the same.
To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`. -/
lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ Evens := by 
   induction' n with m hm
   · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ 
     · exact IsEven.zero_even 
     · trivial
   · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
     · replace h := h.out 
       apply (not_IsEven_succ (m + 1)).mpr 
       apply (not_isEven_succ_succ m).mp 
       rw [Nat.succ_mod_two_eq_zero_iff, ← Nat.mod_two_ne_zero] at h 
       apply (iff_false_right h).mp (id (Iff.symm hm))
     · by_contra H 
       have : m ∈ EvenNaturals := by 
         apply Nat.succ_mod_two_eq_one_iff.mp 
         rw [← @Nat.mod_two_ne_zero (m + 1)] 
         exact H
       rw [hm, mem_setOf_eq, not_IsEven_succ m] at this
       trivial


-- **3** Prove that every even number can be divided by `2`.
lemma exists_half (n : Evens) : ∃ d : ℕ, n = 2 * d := by 
  have hn : n.1 ∈ Evens := n.2 
  rw [← EvenEq] at hn
  replace hn := hn.out 
  have : n.1 = 2 * (n.1 / 2) := by 
    conv_rhs => rw [← Nat.zero_add (2 * (n.1 / 2))] 
    rw [eq_comm, ← hn] 
    exact Nat.mod_add_div n.1 2
  use n / 2

noncomputable
def half : Evens → (univ : Set ℕ) := fun n ↦ ⟨(exists_half n).choose, trivial⟩

-- **4** Doubling and halving is the identity.
lemma double_half (n : Evens) : n = 2 * (half n).1 := by 
  exact (exists_half n).choose_spec 



-- **5** Some more fun with functions.
example : InjOn half univ := by 
  rintro ⟨n, hn⟩ - ⟨m, hm⟩ - h
  simp only [Subtype.mk.injEq]
  have := double_half ⟨n, hn⟩
  rw [h] at this 
  rw [← double_half ⟨m, hm⟩] at this
  exact this


-- **6** Even more fun!
example : Surjective half := by 
  rintro ⟨b1, -⟩
  have : 2 * b1 ∈ Evens := by
    rw [← EvenEq (2 * b1)] 
    have : 2 * b1 % 2 = 0 := Nat.mul_mod_right 2 b1 
    exact this
  use ⟨2 * b1, this⟩ 
  have y := double_half ⟨2 * b1, this⟩
  have : 2 ≠ 0 := by trivial
  rw [Nat.mul_right_inj this] at y
  rw [@Subtype.ext_iff_val, ← y]


end InductiveFamilies


end ENS
