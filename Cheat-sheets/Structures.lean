import Mathlib.Algebra.Group.Nat

-- # Class
-- @[ext] Tells lean to derive extensinality for structures.
-- Class is a `structure` that can be instantiated.

class Dia₁ (α : Type*) where
  dia : α → α → α

instance : Dia₁ ℕ where
  dia := Nat.add

-- # Notation

-- @[inherit_doc] Tells Lean to use the same documentation for " . " and Dia₁.dia
infixl:70 " ⋄ " => Dia₁.dia
