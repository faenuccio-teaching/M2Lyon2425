import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common
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

-- **⌘**

end FirstTrap

-- # §2: Operations

section Operations

variable (α β : Type) (f : α → β)

-- We can upgrade a function `f` to a function between sets, using the image:
example : Set α → Set β := by
  intro S
  exact f '' S

example : 1 ∈ Nat.succ '' univ := by
  use 0
  constructor
  · trivial
  · rfl
-- *An alternative proof*

-- `⌘`

-- The **image**

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



/- With the obvious definition of surjective, prove the following result: the complement is
  abreviated `compl` in the library -/
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
| zero : ENS_Nat
| succ : ENS_Nat → ENS_Nat

#print ENS_Nat
#check ENS_Nat

def JustOne_fun : ℕ → ENS_Nat
  | 0 => ENS_Nat.zero
  | Nat.succ m => ENS_Nat.succ (JustOne_fun m)

def JustOne_inv : ENS_Nat → ℕ
  | ENS_Nat.zero => 0
  | ENS_Nat.succ a => Nat.succ (JustOne_inv a)

def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n
  match n with
  | 0 => rfl
  | Nat.succ m =>
      rw [JustOne_fun, JustOne_inv, JustOne_Left]


def JustOne_Right : RightInverse JustOne_inv JustOne_fun
  | ENS_Nat.zero => rfl
  | ENS_Nat.succ m => by rw [JustOne_inv, JustOne_fun, JustOne_Right]

def JustOne : ℕ ≃ ENS_Nat where
  toFun := JustOne_fun
  invFun := JustOne_inv
  left_inv := JustOne_Left
    -- have : JustOne.invFun = JustOne_inv := by
    --   unfold JustOne.invFun
    -- intro n
    -- match n with
    -- | 0 => rfl
    -- | Nat.succ m =>
    --     have := JustOne.left_inv m
    --     rw [JustOne_fun, JustOne_inv]
    --     simp
    --     convert JustOne.left_inv m
  right_inv := JustOne_Right



inductive Lor (p q : Prop) : Prop
| left : p → Lor p q
| right : q → Lor p q

#print Lor

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


lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ IsEven n := by
  induction' n with m h_ind
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact IsEven.zero_even
    · trivial--rfl -- notice the difference!
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [not_IsEven_succ]
      replace h : (m + 1) % 2 = 0 := h
      replace h : m % 2 = 1 := by
        rwa [Nat.succ_mod_two_eq_zero_iff] at h
      replace h : m ∉ EvenNaturals := by
        intro hm
        replace hm := hm.out
        rw [hm] at h
        exact zero_ne_one h
      replace h_ind : ¬ IsEven m := sorry
      rcases m with _ | ⟨n, hn⟩
      · exfalso
        apply h
        rfl
      · intro h
        rcases h with _ | ⟨-, h⟩
        cases h
      · rwa [Nat.add_assoc, ← not_isEven_succ_succ]
    · rw [not_IsEven_succ] at h
      replace h : ¬ IsEven m := by
        intro h
        replace h := h.succ_succ
        trivial
      replace h_ind := h_ind.mp.mt h
      replace h_ind : ¬ m % 2 = 0 := h_ind
      rw [Nat.mod_two_ne_zero] at h_ind
      rw [← Nat.succ_mod_two_eq_zero_iff] at h_ind
      exact h_ind




end InductiveTypes
