import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common
import Mathlib.Data.Set.Finite
import Mathlib.Order.Basic
import Mathlib.Logic.Function.Defs
import «M2Lyon2425».«SetsAndFunctions1_solutions»

set_option linter.unusedVariables false


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

example : 1 ∈ Nat.succ '' univ := by
  -- use 0
  -- constructor
  -- · trivial
  -- · rfl
-- *An alternative proof*
  exact ⟨0, ⟨trivial, rfl⟩⟩


-- `⌘`

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- The **image**

-- We can upgrade a function `f` to a function between sets, using the *image*:
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
    have := Int.mul_lt_mul h_mlt (le_of_lt h_mlt) hm.out (le_of_lt hn.out)
    replace this := ne_of_lt this
    exact this H
  by_cases h_nlt : n < m
  · exfalso
    exact ((ne_of_lt <| Int.mul_lt_mul h_nlt (le_of_lt h_nlt) hn.out (le_of_lt hm.out))) H.symm
  exact eq_of_le_of_not_lt (le_of_not_lt h_nlt) h_mlt




/- **§ Some exercises** -/



-- The range is not *definitionally equal* to the image of the universal set: use extensionality!
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


-- Why does this code *fail*? Fix it, and then prove the statement
-- example (N : OddNaturals) : N ∈ Nat.succ '' (EvenNaturals) ∧ N ∈ Nat.succ ⁻¹' (EvenNaturals):=
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

-- Why does this code *fail*? Fix it, and then prove the statement
-- example (N : OddNaturals) :  N ∈ Nat.succ ⁻¹' (EvenNaturals) := by
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



example : range Nat.succ ≠ univ := by
  intro h
  rw [Set.eq_univ_iff_forall] at h
  replace h := h 0
  have := Nat.succ_ne_zero (Exists.choose h)
  exact this (Exists.choose_spec h)



-- The following is a *statement* and not merely the *definition* of being injective; prove it.
example : Injective f ↔ InjOn f univ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro a ha b hb H
    apply h H
  · intro a b H
    exact h (trivial) (trivial) H



/- With the obvious definition of surjective, prove the following result: the complement `Sᶜ` is
  referred to with the abbreviation `compl` in the library -/
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

-- # §3 : Inductive types and inductive predicates

namespace InductiveTypes

inductive ENS_Nat
| ENS_zero : ENS_Nat
| ENS_succ : ENS_Nat → ENS_Nat

open ENS_Nat
#print ENS_Nat
#check ENS_Nat

def JustOne_fun : ℕ → ENS_Nat
  | 0 => ENS_zero
  | Nat.succ m => ENS_succ (JustOne_fun m)

def JustOne_inv : ENS_Nat → ℕ
  | ENS_zero => 0
  | ENS_succ a => Nat.succ (JustOne_inv a)

def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n
  match n with
  | 0 => rfl
  | Nat.succ m =>
      rw [JustOne_fun, JustOne_inv, JustOne_Left]


def JustOne_Right : RightInverse JustOne_inv JustOne_fun
  | ENS_zero => rfl
  | ENS_succ m => by rw [JustOne_inv, JustOne_fun, JustOne_Right]

def JustOne : ℕ ≃ ENS_Nat where
  toFun := JustOne_fun
  invFun := JustOne_inv
  left_inv := JustOne_Left
  right_inv := JustOne_Right



inductive Lor (p q : Prop) : Prop
| left : p → Lor p q
| right : q → Lor p q

#print Lor

example (n : ENS_Nat) : Lor (n = ENS_zero) (∃ m, n = ENS_succ m) := by
  cases' n with m -- this is a case-splitting on the way an `ENS_succ` can be constructed
  · apply Lor.left
    rfl
  · apply Lor.right
    cases' m with d
    · use ENS_zero
    · use ENS_succ d

/- **§ An exercise** -/

/-Define a type whose terms represent how one can reach the ENS: one can use a car, a bike, the
metro or any combination of those (with no repetition).-/
inductive TripToENS
  | car : TripToENS
  | bike : TripToENS
  | metro : TripToENS
  | one_change : TripToENS → TripToENS → TripToENS
  | two_changes : TripToENS → TripToENS → TripToENS → TripToENS

-- The following two lines are needed for the file to work: *leave* them as they are, please.
deriving Repr
open TripToENS

/- State that if you're not simply coming by bike nor by car, then either you come by metro or you
need at least one change.-/
example (a : TripToENS) (h1 : a ≠ bike) (h1 : a ≠ car) :
  a = metro
  ∨ (∃ b₁ b₂ , a = one_change b₁ b₂)
  ∨ (∃ c₁ c₂ c₃, a = two_changes c₁ c₂ c₃) := by
  -- cases' a with b1 b2 c1 c2 c3
  rcases a with _ | _ | _ | ⟨b1, b2⟩ | ⟨c1, c2, c3⟩
  · trivial
  · trivial
  · apply Or.inl
    rfl
  · apply Or.inr
    apply Or.inl
    use b1, b2
  · apply Or.inr
    apply Or.inr
    use c1, c2, c3

/- Define a function that expects a trip and outputs the *last* means of transportation -/
def lastTrip (a : TripToENS) : TripToENS :=
match a with
  | one_change b c => c
  | two_changes b c d => d
  | x => x

/-Evaluate your function agains three or four trips and see if it works-/
#eval (lastTrip (one_change car car))
#eval (lastTrip (one_change car bike))
#eval (lastTrip (two_changes bike car bike))
#eval (lastTrip (metro))
#eval (lastTrip (two_changes metro bike metro))

-- `⌘`

inductive NiceType : Type
  | Tom : NiceType
  | Jerry : NiceType
  | f : NiceType → NiceType
  | g : ℕ → NiceType → NiceType → NiceType

inductive NiceProp : Prop
  | Tom : NiceProp
  | Jerry : NiceProp
  | f : NiceProp → NiceProp
  | g : ℕ → NiceProp → NiceProp → NiceProp

#check NiceType
#check NiceProp

inductive NiceFamily : ℕ → Prop
  | Tom : NiceFamily 0
  | Jerry : NiceFamily 1
  | F (n : ℕ) : NiceFamily n → NiceFamily (n + 3)
  | G  : ∀n : ℕ, ℕ → NiceFamily n → NiceFamily (n + 1) → NiceFamily (n + 37)

#check NiceFamily
#check NiceFamily 2
#check NiceFamily 21



inductive IsEven : ℕ → Prop
  | zero_even : IsEven 0
  | succ_succ (n : ℕ) : IsEven n → IsEven (n+2)

example : IsEven 4 := by
  repeat apply IsEven.succ_succ
  exact IsEven.zero_even

example : ¬ IsEven 5 := by
  intro h
  cases h with
  | succ_succ n hn =>
    cases hn with
    | succ_succ m hm =>
      cases hm

example : ¬ IsEven 111 := by
  intro h
  repeat rcases h with _ | ⟨-, h⟩


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

-- To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`
abbrev Evens := setOf IsEven

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

lemma exists_half (n : Evens) : ∃ d : ℕ, n = 2 * d := by
  have hn := n.2
  replace hn : n.1 % 2 = 0 := by
    rwa [← EvenEq] at hn
  replace hn := Nat.dvd_of_mod_eq_zero hn
  exact ⟨hn.choose, hn.choose_spec⟩

noncomputable def half : Evens → (univ : Set ℕ) := fun n ↦ ⟨(exists_half n).choose, trivial⟩

-- example (n : Evens) : n = 2 * (half n) := by
lemma double_half (n : Evens) : n = 2 * (half n).1 := by
  exact (exists_half n).choose_spec

example : InjOn half univ := by
  rintro ⟨n, hn⟩ - ⟨m, hm⟩ - h
  simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
  have hhn := double_half ⟨n, hn⟩
  rw [h, ← double_half] at hhn
  exact hhn

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


/- **§ An exercise** -/

/- Define the set of `TripToENS` that entail no chages:-/
inductive NoChangesTrip' : TripToENS → Prop :=
  | only_car : NoChangesTrip' car
  | only_metro : NoChangesTrip' metro
  | only_bike : NoChangesTrip' bike

open NoChangesTrip'

def NoChangesTrip := setOf NoChangesTrip'

example : car ∈ NoChangesTrip := by
  exact only_car

example : one_change car bike ∉ NoChangesTrip := by
  intro h
  cases h


/- The cofinite topology as inductive type -/
inductive CofTop {α : Type} : Set α → Prop
| open_empty : CofTop ∅
-- | open_univ : CofTop univ
| open_cofinite (S : Set α) : Finite ↑(Sᶜ) → CofTop S
open CofTop

variable {α : Type}

lemma interCofTop (S T : Set α) : CofTop S → CofTop T → CofTop (S ∩ T) := by
  intro hs ht
  rcases hs with _ |/-  _ | -/ ⟨_, hs⟩
  · rw [empty_inter]
    exact open_empty
  -- · rwa [univ_inter]
  · rcases ht with /- _ |  -/_ | ⟨_, ht⟩
    · rw [inter_empty]
      exact open_empty
    -- · rw [inter_univ]
    --   apply open_cofinite
    --   exact hs
    · apply open_cofinite
      rw [compl_inter]
      apply Set.Finite.union
      exact hs
      exact ht

lemma iUnionCofTop (I : Type) (S : I → Set α) (hs : ∀ i, CofTop (S i)) :
  CofTop (⋃ i : I, S i) := by
  sorry


end InductiveTypes
