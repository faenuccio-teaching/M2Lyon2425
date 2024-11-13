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
  intro
  exact hQ

-- Let's try something a bit more complicated
-- Use `\.` to write `·`
example : (P → Q → R) → (P → Q) → P → R := by
  intro h1
  intro h2
  intro hP
  apply h1
  · exact hP
  · apply h2 hP

/- TODO -/

example : P → Q → P := by
  intro hP
  intro
  exact hP

-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
example : P → (P → Q) → Q := by
  intro hP h
  apply h hP

-- Transitivity of `→`
example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 hP
  apply h2
  apply h1 hP

example : (P → Q) → ((P → Q) → P) → Q := by
  intro h1 h2
  apply h1
  apply h2 h1

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro h1 h2 _
  apply h2
  intro hQ
  apply h1
  intro
  exact hQ

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1 h2 h3
  apply h1
  intro hQ
  apply h3
  apply h2 hQ

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
  intro f
  exfalso
  exact f

/- TODO -/

example : True → True := by
  intro
  trivial

example : False → True := by
  intro f
  exfalso
  exact f

example : False → False := by
  intro f
  exfalso
  exact f

example : (True → False) → False := by
  intro h
  apply h trivial

example : True → False → True → False → True → False := by
  intro _ f _ _ _
  exact f

example : P → (P → False) → False := by
  intro hP h
  apply h hP

example : (P → False) → P → Q := by
  intro h hP
  exfalso
  apply h hP

example : (True → False) → P := by
  intro h
  exfalso
  apply h trivial

/- END TODO -/

/-
  # Negation
  Use `\not` to write `¬`
  The definition of `¬ P` is `P → False`: they are *definitionnally equal*
-/

-- Use of the `change` tactic
example : ¬True → False := by
  change (True → False) → False
  intro h
  apply h trivial

example : False → ¬True := by
  intro f
  exfalso
  exact f

-- Use of the `by_contra` tactic
example : True → ¬False := by
  intro _ a
  by_contra
  exact a

-- Use of the `have` tactic
example : (P → Q) → ¬Q → ¬P := by
  intro h1 h2 hP
  have h3 : Q := h1 hP
  apply h2 h3

-- Use of the `by_cases` tactic
example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exfalso
    apply h hP

/- TODO -/

example : ¬False → True := by
  intro
  trivial

example : P → ¬¬P := by
  change P → ¬ P → False
  change P → (P → False) → False
  intro hP h
  apply h hP

example : False → ¬P := by
  intro f
  exfalso
  exact f

example : P → ¬P → False := by
  intro h1 h2
  apply h2 h1

example : ¬¬False → False := by
  change ((False → False) → False) → False
  intro h
  apply h
  intro f
  exact f

example : (¬Q → ¬P) → P → Q := by
  intro h1 hP
  by_contra nQ
  have nP : ¬P := h1 nQ
  apply nP hP

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
  | intro left right => apply h1 left right

-- `∧` is symmetric
example : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro left right =>
  constructor
  · exact right
  · exact left

-- `∧` is transitive
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  cases h1 with
  | intro left _ =>
    cases h2 with
    | intro _ right =>
      constructor
      · exact left
      · exact right

example : P → P ∧ True := by
  intro hP
  constructor
  · exact hP
  · trivial

example : False → P ∧ False := by
  intro f
  exfalso
  exact f

example : (P ∧ Q → R) → P → Q → R := by
  intro h1 hP hQ
  apply h1
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

lemma equiv_sym : (P ↔ Q) → (Q ↔ P) := by
  intro h
  cases h with
  | intro mp mpr =>
    constructor
    · exact mpr
    · exact mp

-- Use of the `lemma` tactic
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · exact equiv_sym P Q
  · exact equiv_sym Q P

/- TODO -/

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  cases h1 with
  | intro mp1 mp1r =>
    cases h2 with
    | intro mp2 mp2r =>
      constructor
      · intro hP
        apply mp2
        apply mp1 hP
      · intro hR
        apply mp1r
        apply mp2r hR

example : P ∧ Q ↔ Q ∧ P := by
  sorry

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  refine ⟨ fun h1 ↦ ⟨ h1.1.1  , ⟨ h1.1.2 , h1.2⟩ ⟩, fun h2 ↦ ⟨ ⟨ h2.1 , h2.2.1⟩, h2.2.2 ⟩ ⟩

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
  intro hP
  left
  exact hP

-- Use of the `right` tactic
example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

-- symmetry of `∨`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP =>
    right
    exact hP
  | inr hQ =>
    left
    exact hQ


-- The law of excluded middle is not by default in Lean but we included some conventions
-- from Mathlib including this law (and we actually already used it.)
example : P ∨ ¬ P := by
  by_cases h : P
  · left
    exact h
  · right
    exact h

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
  tauto

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry

/- END TODO -/
