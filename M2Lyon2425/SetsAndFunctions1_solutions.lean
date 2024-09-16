import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common

open Set Classical
section Examples

/- # A tautology -/
example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := sorry






/- # The positive integers -/
def PositiveIntegers : Set ℤ := by
  -- intro d
  -- -- use if 0 ≤ d then True else False --bleah!
  -- exact (0 ≤ ·) d -- not bleah
  -- exact @LE.le ℤ _ 0 -- uff
  -- exact (fun d ↦ 0 ≤ d) -- mah
  exact (0 ≤ ·) -- nicer


/- # The even naturals -/
def EvenNaturals : Set ℕ := by
  -- intro d
  -- exact if d % 2 = 0 then True else False
  exact (· % 2 = 0)


/- # An abstract set -/
def AbstracSet (α : Type) (P : α → Prop) : Set α := P


/- # Some sub-sub sets -/
def subsub (α : Type) (S : Set α) (P : α → Prop) : Set (S : Type) := by
  intro a
  exact P a

def subsub' (α : Type) (S : Set α) (P : S → Prop) : Set (S : Type) := P

example : subsub = subsub' := sorry

/- # A double inclusion -/

example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by sorry


/- # Some exercises -/

example : 1 ∉ EvenNaturals := sorry

example : 1 ∈ PositiveIntegers := sorry

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set EvenNaturals := sorry

example : 3 ∉ EvenPositiveNaturals := sorry --can you explain why Lean complains?


end Examples

inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)

inductive pp : ℕ → Type 12 where
 | z : pp 0
 | s : pp 1 → pp 2

def aa : (n : ℕ) → Prop := sorry

def vfd : Even := sorry

-- def v : aa := sorry

-- inductive Even' (n : ℕ) : Prop :=
--   | a : (n = 0) → Even' n
--   | b : 2 ≤ n → (Even' n-1) → Even' n
  -- | add_two : ∀k : ℕ, Even k → Even (k + 2)

def Even1 : ℕ → Prop
  | 0 => True
  | 1 => False
  | n + 2 => Even n

def Even2 (n : ℕ) : Prop :=
  match n with
  | 0 => True
  | 1 => False
  | n + 2 => Even n

example : Even1  = Even2 := rfl




#check (Even : Set ℕ)

section Operations

-- Self-intersection is the identity, proven with **extensionality**
example (α : Type) (S : Set α) : S ∩ S = S := by sorry















-- The difference
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by sorry
















/- # Functions-/

-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (T : Set β) (f g : S → T) :
  f = g ↔ ∀ a : α, a ∈ S → f a  = g a := by sorry
















variable (α β : Type) (f : α → β)

-- We can upgrade a function `f` to a function between sets, using the image:
example : Set α → Set β := by sorry















-- The range is not *definitionally equal* to the image of the universal set: use extensionality!
example : range f = f '' univ := by sorry
















-- Why is the following a *statement* and not merely the *definition* of being injective?
example : Injective f ↔ InjOn f univ := by sorry

end Operations
