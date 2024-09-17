import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Common

open Set Classical
section Definitions

-- # §1: Definitions


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
