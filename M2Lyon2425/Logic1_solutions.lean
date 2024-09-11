/-
  ## LOGIC 1
  Credits.
  * Formalising Mathematics 2024, K. Buzzard,
  * Theorem Proving in Lean 4, J. Avigad, L. de Moura, S. Kong, S. Ullrich
  * The Mechanics of Proof, H. Macbeth
-/
import Mathlib.Tactic.Common

/-
  # The Prop type
  Propositions are mathematical statements that can be true or false, like `2 + 2 = 5` or
  `A finite group of order 11 is cyclic`. They live in the type `Prop`. It is a special
  type that contains only two elements `True` and `False`.
-/

-- Introduce some propositions
variable (P Q R S : Prop)

-- Use of the `rfl` tactic
example : P = P := by
  rfl

-- Use of the `exact` tactic
example (hP : P) : P := by
  exact hP

/-
  # Implication
  Use `\to` to write `→`
-/

-- Use of the `intro` tactic
example : P → P := by
  intro hP
  exact hP

-- Use of the `apply` tactic
example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP

example (hQ : Q) : P → Q := by
  intro _
  exact hQ

-- Let's try something a bit more complicated
-- Use `\.` to write `·`
example : (P → Q → R) → ((P → Q) → (P → R)) := by
  intro h1
  intro h2
  intro hP
  apply h1
  · exact hP
  · apply h2
    exact hP

/- TODO -/

example : P → Q → P := by
  intro hP _
  exact hP

-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
example : P → (P → Q) → Q := by
  intro hP h
  apply h
  exact hP

-- Transitivity of `→`
example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 hP
  apply h2
  apply h1
  exact hP

example : (P → Q) → ((P → Q) → P) → Q := by
  intro h1 h2
  apply h1
  apply h2
  exact h1

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro h1 h2 _
  apply h2
  intro hQ
  apply h1
  intro _
  exact hQ

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1 h2 h3
  apply h1
  intro hQ
  apply h3
  apply h2
  exact hQ

/- END TDOO-/

/-
  # `True` and `False`
  The values `True` and `False` are also defined and can be used to write
  propositions.
-/

-- Use of the `trivial` tactic
example : True := by
  trivial

-- Use of the `exfalso` tactic
example : False → P := by
  intro h
  exfalso
  exact h

/- TODO -/

example : True → True := by
  intro h
  exact h

example : False → True := by
  intro h
  exfalso
  exact h

example : False → False := by
  intro h
  exact h

example : (True → False) → False := by
  intro h
  apply h
  trivial

example : True → False → True → False → True → False := by
  intro _ h _ _ _
  exact h

example : P → (P → False) → False := by
  intro hP h
  apply h
  exact hP

example : (P → False) → P → Q := by
  intro h hP
  exfalso
  apply h
  exact hP

example : (True → False) → P := by
  intro h1
  exfalso
  apply h1
  trivial

/- END TODO -/

/-
  # Negation
  Use `\not` to write `¬`
  The definition of `¬ P` is `P → False`: they are *definitionnally equal*
-/

-- Use of the `change` tactic
example : ¬True → False := by
--  change (True → False) → False
  intro h
  apply h
  trivial

example : False → ¬True := by
  intro h _
  exact h

-- Use of the `by_contra` tactic
example : True → ¬False := by
  intro _
  by_contra h
  exact h

-- Use of the `have` tatic
example : (P → Q) → (¬Q → ¬P) := by
  intro h1
  intro h2
  intro hP
  have h3 := h1 hP
  change Q → False at h2
  exact h2 h3 -- Apply `Q → False` to the proof h3 of `Q`

-- Use of the `by_cases` tactic
example : ¬¬P → P := by
  intro h1
  by_cases hP : P
  · exact hP
  · have h2 := h1 hP
    exfalso
    exact h2

/- TODO -/

example : ¬False → True := by
  intro _
  trivial

example : P → ¬¬P := by
  change P → ¬ P → False
  change P → (P → False) → False
  intro hP h
--  apply h
--  exact hP
  exact h hP

example : False → ¬P := by
  intro h _
  exact h

example : P → ¬P → False := by
  intro hP h
--  apply h
--  exact hP
  exact h hP

example : ¬¬False → False := by
  intro h1
  apply h1
  intro h2
  exact h2

example : (¬Q → ¬P) → P → Q := by
  intro h1 hP
  --- Proves it using by_cases
  by_contra h2 -- Assume `¬ Q` holds and get a contradiction
  have h3 := h1 h2  -- Since `¬ Q` and `¬ Q → ¬ P`, we have `¬ P`
  exact h3 hP

/- END TODO -/

/-
  # Conjonction / And
  Use `\and` to write `∧`
-/

-- Use of the `constructor` tactic
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · exact hP
  · exact hQ

-- Use of the `cases` tactic
example : P ∧ Q → P := by
  intro h
  cases h with
  | intro left right => exact left

/- TODO -/

example : P ∧ Q → Q := by
  intro h
  cases h with
  | intro left right => exact right

example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  cases h2 with
  | intro left right =>
      apply h1 -- This creates two goals
      · exact left
      · exact right

-- `∧` is symmetric
example : P ∧ Q → Q ∧ P := by
  intro h
  constructor -- This creates two goals
  · cases h with
  | intro left right => exact right
  · cases h with
  | intro left right => exact left

-- `∧` is transitive
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  constructor
  · cases h1 with
  | intro left right => exact left
  · cases h2 with
  | intro left right => exact right

example : P → P ∧ True := by
  intro hP
  constructor
  · exact hP
  · trivial

example : False → P ∧ False := by
  intro h
  exfalso
  exact h

example : (P ∧ Q → R) → P → Q → R := by
  intro h hP hQ
  apply h
  constructor
  · exact hP
  · exact hQ

/- END TODO -/

/-
  # Equivalence
  Use `\iff` to write `↔`
  `P ↔ Q` can broken into two goals: `P → Q` and `Q → P` using `constructor`.
-/

example : P ↔ P := by
  constructor
  · intro hP
    exact hP
  · intro hP
    exact hP

lemma lemma1 : (P ↔ Q) → (Q ↔ P) := by
  intro h
  cases h with
  | intro mp mpr =>
    constructor
    · exact mpr
    · exact mp

-- Use of the `lemma` tactic
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · exact lemma1 P Q
  · exact lemma1 Q P

/- TODO -/

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  constructor
  · intro hP
    cases h2 with
    | intro mp mpr =>
      apply mp
      cases h1 with
      | intro mp mpr =>
        apply mp
        exact hP
  · intro hR
    cases h1 with
    | intro mp mpr =>
      apply mpr
      cases h2 with
      | intro mp mpr =>
        apply mpr
        exact hR

-- More efficiently
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  constructor
  · intro hP
    apply h2.mp
    apply h1.mp
    exact hP
  · intro hR
    apply h1.mpr
    apply h2.mpr
    exact hR

-- Even more efficiently
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  constructor
  · intro hP
    exact h2.mp (h1.mp hP)
  · intro hR
    exact h1.mpr (h2.mpr hR)

lemma lemma2 : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.right
  · exact h.left

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · exact lemma2 P Q
  · exact lemma2 Q P

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro h
    constructor
    · exact h.left.left
    · constructor
      · exact h.left.right
      · exact h.right
  · intro h
    constructor
    · constructor
      · exact h.left
      · exact h.right.left
    · exact h.right.right

example : P ↔ P ∧ True := by
  constructor
  · intro hP
    constructor
    · exact hP
    · trivial
  · intro h
    exact h.left

example : False ↔ P ∧ False := by
  constructor
  · intro h
    exfalso
    exact h
  · intro h
    exact h.right

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  constructor
  · intro h3
    constructor
    · apply h1.mp
      exact h3.left
    · apply h2.mp
      exact h3.right
  · intro h3
    constructor
    · apply h1.mpr
      exact h3.left
    · apply h2.mpr
      exact h3.right

example : ¬(P ↔ ¬P) := by
  intro h
  cases h with
  | intro mp mpr =>
    by_cases hP : P
    · have hP' := mp hP
      exact hP' hP
    · have hP' := mpr hP
      exact hP hP'

/- END TODO -/

/-
  # Disjonction / Or
  Use `\or` to write `∨`
-/

-- Use of the `left` tactic
example : P → P ∨ Q := by
  sorry

-- Use of the `right` tactic
example : Q → P ∨ Q := by
  sorry

-- symmetry of `∨`
example : P ∨ Q → Q ∨ P := by
  sorry

-- The law of excluded middle is not by default in Lean but we included some conventions
-- from Mathlib including this law (and we actually already used it.)
example : P ∨ ¬ P := by
  sorry

/- TODO -/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  sorry

-- associativity of `∨`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  sorry

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  sorry

example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  sorry

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry

/- END TODO -/
