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
  sorry

-- Use of the `exact` tactic
example (hP : P) : P := by
  sorry

/-
  # Implication
  Use `\to` to write `→`
-/

-- Use of the `intro` tactic
example : P → P := by
  intro hP
  sorry

-- Use of the `apply` tactic
example (h : P → Q) (hP : P) : Q := by
  apply h
  sorry

example (hQ : Q) : P → Q := by
  sorry

-- Let's try something a bit more complicated
-- Use `\.` to write `·`
example : (P → Q → R) → (P → Q) → P → R := by
  intro h1
  intro h2
  intro hP
  apply h1
  · sorry
  · sorry

/- TODO -/

example : P → Q → P := by
  sorry

-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
example : P → (P → Q) → Q := by
  sorry

-- Transitivity of `→`
example : (P → Q) → (Q → R) → P → R := by
  sorry

example : (P → Q) → ((P → Q) → P) → Q := by
  sorry

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  sorry

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  sorry

/- END TDOO-/

/-
  # `True` and `False`
  The values `True` and `False` are also defined and can be used to write
  propositions.
-/

-- Use of the `trivial` tactic
example : True := by
  sorry

-- Use of the `exfalso` tactic
example : False → P := by
  sorry

/- TODO -/

example : True → True := by
  sorry

example : False → True := by
  sorry

example : False → False := by
  sorry

example : (True → False) → False := by
  sorry

example : True → False → True → False → True → False := by
  sorry

example : P → (P → False) → False := by
  sorry

example : (P → False) → P → Q := by
  sorry

example : (True → False) → P := by
  sorry

/- END TODO -/

/-
  # Negation
  Use `\not` to write `¬`
  The definition of `¬ P` is `P → False`: they are *definitionnally equal*
-/

-- Use of the `change` tactic
example : ¬True → False := by
  change (True → False) → False
  sorry

example : False → ¬True := by
  sorry

-- Use of the `by_contra` tactic
example : True → ¬False := by
  sorry

-- Use of the `have` tactic
example : (P → Q) → ¬Q → ¬P := by
  intro h1 h2 hP
  have := h1 hP
  sorry

-- Use of the `by_cases` tactic
example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · sorry
  · sorry

/- TODO -/

example : ¬False → True := by
  sorry

example : P → ¬¬P := by
  change P → ¬ P → False
  change P → (P → False) → False
  sorry

example : False → ¬P := by
  sorry

example : P → ¬P → False := by
  sorry

example : ¬¬False → False := by
  sorry

example : (¬Q → ¬P) → P → Q := by
  sorry

/- END TODO -/

/-
  # Conjonction / And
  Use `\and` to write `∧`
-/

-- Use of the `constructor` tactic
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · sorry
  · sorry

-- Use of the `cases` tactic
example : P ∧ Q → P := by
  intro h
  cases h
  sorry

/- TODO -/

example : P ∧ Q → Q := by
  sorry

example : (P → Q → R) → P ∧ Q → R := by
  sorry

-- `∧` is symmetric
example : P ∧ Q → Q ∧ P := by
  sorry

-- `∧` is transitive
example : P ∧ Q → Q ∧ R → P ∧ R := by
  sorry

example : P → P ∧ True := by
  sorry

example : False → P ∧ False := by
  sorry

example : (P ∧ Q → R) → P → Q → R := by
  sorry

/- END TODO -/

/-
  # Equivalence
  Use `\iff` to write `↔`
  `P ↔ Q` can broken into two goals: `P → Q` and `Q → P` using `constructor`.
-/

example : P ↔ P := by
  constructor
  · sorry
  · sorry

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  cases h
  sorry

-- Use of the `lemma` tactic
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · sorry
  · sorry

/- TODO -/

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry

example : P ∧ Q ↔ Q ∧ P := by
  sorry

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  sorry

example : P ↔ P ∧ True := by
  sorry

example : False ↔ P ∧ False := by
  sorry

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry

example : ¬(P ↔ ¬P) := by
  sorry

/- END TODO -/

/-
  # Disjunction / Or
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
