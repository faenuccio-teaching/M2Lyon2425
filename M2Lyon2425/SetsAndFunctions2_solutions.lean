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
  -- f = g ↔ ∀ a : α, a ∈ S → f a  = g a := by sorry
  f = g ↔ ∀ a : α, (ha : a ∈ S) → f ⟨a, ha⟩  = g ⟨a, ha⟩ := by
  constructor
  · intro h
    rw [h]
    -- rfl -- *fails*!
    exact fun _ _ ↦ rfl -- why? Because the whole type is not an equality type.
  · intro h
    funext x
    -- exact h --why?
    apply h -- or exact h _ _


-- `⌘`

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- The **image**
#check f

example : 1 ∈ Nat.succ '' univ := by
  -- use 0
  -- constructor
  -- · trivial
  -- · rfl
-- *An alternative proof*
  exact ⟨0, ⟨trivial, rfl⟩⟩

-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by
  intro S
  exact f '' S


example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  intro hS hfS
  apply hS
  rw [eq_empty_iff_forall_not_mem] at hfS ⊢
  intro x hx
  replace hfS := hfS (f x)
  apply hfS
  use x


-- `⌘`


-- The **preimage**

example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by
  constructor
  · rw [mem_preimage]
    trivial
  · intro h
    rw [mem_preimage] at h
    trivial


-- `⌘`

example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  intro m hm n hn
  simp only
  intro H
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one] at H
  by_cases h_mlt : m < n
  · exfalso
    -- have := mul_lt_mul -- we can add a `@` before to let it compile anyhow
    -- have := @Int.mul_lt_mul -- now we see who each `a,b,c,d` must be
    have := Int.mul_lt_mul h_mlt (le_of_lt h_mlt) hm.out (le_of_lt hn.out)
    replace this := ne_of_lt this
    exact this H
  by_cases h_nlt : n < m
  · exfalso
    exact ((ne_of_lt <| Int.mul_lt_mul h_nlt (le_of_lt h_nlt) hn.out (le_of_lt hm.out))) H.symm
  exact eq_of_le_of_not_lt (le_of_not_lt h_nlt) h_mlt




/- **§ Some exercises** -/



/- **1** The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by
  ext x
  refine ⟨fun h ↦ ?_ , fun h ↦ ?_⟩
  · rw [mem_range] at h
    let y := Exists.choose h
    use y
    constructor
    · trivial
    · exact Exists.choose_spec h
  · rw [mem_range]
    use Exists.choose h
    exact (Exists.choose_spec h).2


-- **2** Why does this code *fail*? Fix it, and then prove the statement
-- example (N : OddNaturals) : N ∈ Nat.succ '' (EvenNaturals) :=
-- It *fails* because `N` is of the wrong type. `N.1` is a `ℕ`, and the following code compiles:
example (N : OddNaturals) : N.1 ∈ Nat.succ '' (EvenNaturals) := by
  rcases N with ⟨n, hn⟩
  have hn' := hn.out
  rw [mem_image]
  match n with
  | 0 => trivial
  | m+1 =>
    rw [Nat.succ_mod_two_eq_one_iff] at hn'
    use m
    constructor
    · exact hn'
    · exact Nat.succ_eq_add_one _

-- **3** Why does this code *fail*? Fix it, and then prove the statement
-- example (N : OddNaturals) :  N ∈ Nat.succ ⁻¹' (EvenNaturals) := by
-- It *fails* because `N` is of the wrong type. `N.1` is a `ℕ`, and the following code compiles:
example (N : OddNaturals) :  N.1 ∈ Nat.succ ⁻¹' (EvenNaturals) := by
  rcases N with ⟨n, hn⟩
  rw [mem_preimage]
  have hn' := hn.out
  by_cases hnz : n = 0
  · rw [hnz] at hn'
    trivial
  · replace hnz := Nat.exists_eq_succ_of_ne_zero hnz
    obtain ⟨m, hm⟩ := hnz -- `obtain` combines the `Exists.choose` and `Exists.choose_spec`
    rw [hm] at hn'
    rw [Nat.succ_mod_two_eq_one_iff] at hn'
    show n.succ % 2 = 0 --`show` changes the goal to something definitionally equivalent
    omega
    -- *Alternative proof* if you forgot about `omega`:
    -- rw [hm]
    -- simp only [Nat.succ_eq_add_one]
    -- rwa [add_assoc, Nat.add_mod_right]

-- **4** Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by
  intro h
  rw [Set.eq_univ_iff_forall] at h
  replace h := h 0
  have := Nat.succ_ne_zero (Exists.choose h)
  exact this (Exists.choose_spec h)



/- **5** The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro a ha b hb H
    apply h H
  · intro a b H
    exact h (trivial) (trivial) H



/- **6** With the obvious definition of surjective, prove the following result: the
 complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by
  refine ⟨fun h ↦ ?_ , fun h ↦ ?_⟩
  · rw [Set.compl_empty_iff]
    ext x
    constructor
    · intro H
      trivial
    · intro H
      obtain ⟨y, hy⟩ := h x
      use y
  · intro x
    rw [Set.compl_empty_iff] at h
    rw [eq_univ_iff_forall] at h
    replace h := h x
    exact h

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
  | ENS_succ a => Nat.succ (JustOne_inv a)

def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n
  induction' n with m hm
  · rfl
  · rw [JustOne_fun, JustOne_inv, hm]
  -- *Alternative, **recursive**, proof*, without induction
  -- match n with
  -- | 0 => rfl
  -- | Nat.succ m =>
  --     rw [JustOne_fun, JustOne_inv, JustOne_Left]

--This we leave as an exercise...
def JustOne_Right : RightInverse JustOne_inv JustOne_fun
  | ENS_zero => rfl
  | ENS_succ m => by rw [JustOne_inv, JustOne_fun, JustOne_Right]


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
  cases' n with m -- this is a case-splitting on the way an `ENS_succ` can be constructed
  · apply ENS_Or.left
    rfl
  · apply ENS_Or.right
    cases' m with d
    · use ENS_zero
    · use ENS_succ d




/- **§ Some exercises** -/



-- **1** : Fill in the `sorry` in `JustOne_inv` and in `JustOne_Right`.
-- *Solutions* are above

-- **2** The successor is not surjective, but you can't rely on the library this time.
example : ¬ Surjective ENS_succ := by
  intro habs
  obtain ⟨a, ha⟩ := habs ENS_zero
  cases ha

/- **3** Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics
  | Right : Politics
  | Left : Politics


-- leave this line as it is
open Politics

/- **4** Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics
  | Right => Left
  | Left => Right

/- **5** Prove that if someone is not on the `Right`, they are on the `Left` -/
example (a : Politics) : a ≠ Right → a = Left := by
  intro ha
  cases a
  · exfalso
    trivial
  · rfl

end InductiveTypes

-- # §4 : Inductive families

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

-- # §4 : Inductive predicates

inductive IsEven : ℕ → Prop
  | zero_even : IsEven 0
  | succ_succ (n : ℕ) : IsEven n → IsEven (n+2)


example : IsEven 4 := by
  apply IsEven.succ_succ
  apply IsEven.succ_succ
  -- *Alternative proof* repeat apply IsEven.succ_succ
  exact IsEven.zero_even

example : ¬ IsEven 5 := by
  intro h
  cases h with
  | succ_succ n hn =>
    cases hn with
    | succ_succ m hm =>
      cases hm

lemma not_isEven_succ_succ (n : ℕ) : ¬ IsEven n ↔ ¬ IsEven (n + 2) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro hf
    cases hf
    trivial
  · intro hf
    have := IsEven.succ_succ n hf
    trivial

lemma not_IsEven_succ : ∀ n : ℕ, IsEven n ↔ ¬ IsEven (n + 1) := by
  intro n
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with _ | ⟨n, hn⟩ -- what are the new cases? how many? why?
    · intro hf
      cases hf
    · intro hf
      rcases hf with _ | ⟨-, H⟩
      exact (not_IsEven_succ n).mp hn H
  · induction' n with d hd
    · exact IsEven.zero_even
    · rw [← not_isEven_succ_succ] at h
      replace hd := hd.mt
      simp only [Decidable.not_not] at hd
      apply hd
      exact h




/- **§ Some exercises** -/



-- **1** Recall the `repeat` tactic
example : ¬ IsEven 111 := by
  intro h
  repeat rcases h with _ | ⟨-, h⟩


-- Let's consider the *set* of even numbers satisfying `IsEven`
abbrev Evens := setOf IsEven

/- **2** Show that the two set of even numbers we defined are actually the same.
To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`. -/
lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ Evens := by
  induction' n with m h_ind
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact IsEven.zero_even
    · trivial--rfl -- notice the difference!
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [mem_setOf_eq, not_IsEven_succ]
      replace h : (m + 1) % 2 = 0 := h.out
      replace h : m % 2 = 1 := by
        rwa [Nat.succ_mod_two_eq_zero_iff] at h
      replace h : m ∉ EvenNaturals := by
        intro hm
        replace hm := hm.out
        rw [hm] at h
        exact zero_ne_one h
      replace h_ind : ¬ IsEven m := (h_ind.mpr).mt h
      rcases m with _ | ⟨n, hn⟩
      · exfalso
        apply h
        rfl
      · intro h
        rcases h with _ | ⟨-, h⟩
        cases h
      · rwa [Nat.add_assoc, ← not_isEven_succ_succ]
    · rw [mem_setOf_eq, not_IsEven_succ] at h
      replace h : ¬ IsEven m := by
        intro h
        replace h := h.succ_succ
        trivial
      replace h_ind := h_ind.mp.mt h
      replace h_ind : ¬ m % 2 = 0 := h_ind
      rw [Nat.mod_two_ne_zero] at h_ind
      rw [← Nat.succ_mod_two_eq_zero_iff] at h_ind
      exact h_ind

-- **3** Prove that every even number can be divided by `2`.
lemma exists_half (n : Evens) : ∃ d : ℕ, n = 2 * d := by
  have hn := n.2
  replace hn : n.1 % 2 = 0 := by
    rwa [← EvenEq] at hn
  replace hn := Nat.dvd_of_mod_eq_zero hn
  exact ⟨hn.choose, hn.choose_spec⟩

noncomputable
def half : Evens → (univ : Set ℕ) := fun n ↦ ⟨(exists_half n).choose, trivial⟩

-- **4** Doubling and halving is the identity.
lemma double_half (n : Evens) : n = 2 * (half n).1 := by
  exact (exists_half n).choose_spec

-- **5** Some more fun with functions.
example : InjOn half univ := by
  rintro ⟨n, hn⟩ - ⟨m, hm⟩ - h
  simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
  have hhn := double_half ⟨n, hn⟩
  rw [h, ← double_half] at hhn
  exact hhn

-- **6** Even more fun!
example : Surjective half := by
  rintro ⟨n, -⟩
  have hn : 2 * n ∈ Evens := by
    rw [← EvenEq]
    show 2 * n % 2 = 0
    omega
  let a : Evens := ⟨2 * n , hn⟩
  use a
  have := double_half a
  rw [Nat.mul_right_inj] at this
  rw [this]
  omega


end InductiveFamilies


end ENS
