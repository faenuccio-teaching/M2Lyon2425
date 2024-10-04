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
  exact fun _ ↦ hQ

-- Let's try something a bit more complicated
-- Use `\.` to write `·`
example : (P → Q → R) → (P → Q) → P → R := by
  intro h1
  intro h2
  intro hP
  apply h1
  · exact hP
  · exact h2 hP

/- TODO -/

example : P → Q → P := by
  exact fun hP _ ↦ hP

-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
example : P → (P → Q) → Q := by
  exact fun hP h ↦ h hP

-- Transitivity of `→`
example : (P → Q) → (Q → R) → P → R := by
  exact fun h₁ h₂ hP ↦ h₂ (h₁ hP)

example : (P → Q) → ((P → Q) → P) → Q := by
  exact fun h₁ h₂ ↦ h₁ (h₂ h₁)

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  exact fun h₁ h₂ _ ↦ h₂ (fun hQ ↦ h₁ (fun _ ↦ hQ))

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  exact fun h₁ h₂ h₃ ↦ h₁ (fun hQ ↦ h₃ (h₂ hQ))

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
  exact fun h ↦ h

example : False → True := by
  intro h
  exfalso
  exact h

example : False → False := by
  exact fun h ↦ h

example : (True → False) → False := by
  intro h
  apply h
  trivial

example : True → False → True → False → True → False := by
  exact fun _ h₂ _ _ _ ↦ h₂

example : P → (P → False) → False := by
  exact fun hP h ↦ h hP

example : (P → False) → P → Q := by
  intros h hP
  exfalso
  exact h hP

example : (True → False) → P := by
  intro h
  exfalso
  apply h
  trivial

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
  apply h
  trivial

example : False → ¬True := by
  exact fun h _ ↦ h

-- Use of the `by_contra` tactic
example : True → ¬False := by
  by_contra h
  push_neg at h
  exact h.2

-- Use of the `have` tatic
example : (P → Q) → ¬Q → ¬P := by
  intro h1 h2 hP
  have := h1 hP
  exact h2 this

-- Use of the `by_cases` tactic
example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exfalso
    exact h hP

/- TODO -/

example : ¬False → True := by
  exact fun _ ↦ trivial

example : P → ¬¬P := by
  change P → ¬ P → False
  change P → (P → False) → False
  exact fun hP h ↦ h hP

example : False → ¬P := by
  intro hfalse
  exfalso
  exact hfalse

example : P → ¬P → False := by
  exact fun hP nhP ↦ nhP hP

example : ¬¬False → False := by
  intro hfalse
  push_neg at hfalse
  exact hfalse

example : (¬Q → ¬P) → P → Q := by
  intros h₁ h₂
  by_contra H
  exact (h₁ H) h₂

-- Second method

example : (¬Q → ¬P) → P → Q := by
  intro h₁ h₂
  by_cases hQ : Q
  · exact hQ
  · by_cases hP : P
    · exfalso
      exact (h₁ hQ) hP
    · exfalso
      exact hP h₂

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
  exact fun h ↦ h.2

example : (P → Q → R) → P ∧ Q → R := by
  exact fun h h₂ ↦ (h h₂.1) h₂.2

-- `∧` is symmetric
example : P ∧ Q → Q ∧ P := by
  exact fun h ↦ ⟨h.2, h.1⟩

-- `∧` is transitive
example : P ∧ Q → Q ∧ R → P ∧ R := by
  exact fun h₁ h₂ ↦ ⟨h₁.1, h₂.2⟩

example : P → P ∧ True := by
  exact fun h ↦ ⟨h, trivial⟩

example : False → P ∧ False := by
  intro hfalse
  exfalso
  exact hfalse

example : (P ∧ Q → R) → P → Q → R := by
  exact fun h hP hQ ↦ h ⟨hP, hQ⟩

/- END TODO -/

/-
  # Equivalence
  Use `\iff` to write `↔`
  `P ↔ Q` can broken into two goals: `P → Q` and `Q → P` using `constructor`.
-/

example : P ↔ P := by
  constructor
  · exact fun h ↦ h
  · exact fun h ↦ h

lemma lemma1 : (P ↔ Q) → (Q ↔ P) := by
  intro h
  cases h with
  | intro mp mpr => exact ⟨mpr, mp⟩

-- Use of the `lemma` tactic
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · exact lemma1 P Q
  · exact lemma1 Q P

/- TODO -/

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  exact fun h₁ h₂ ↦ ⟨fun hP ↦ h₂.1 (h₁.1 hP), fun hR ↦ h₁.2 (h₂.2 hR)⟩

example : P ∧ Q ↔ Q ∧ P := by
  exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  exact ⟨fun h ↦ ⟨h.1.1, ⟨h.1.2, h.2⟩⟩ , fun h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

example : P ↔ P ∧ True := by
  exact ⟨fun h ↦ ⟨h, trivial⟩, fun h ↦ h.1⟩

example : False ↔ P ∧ False := by
  refine ⟨fun h ↦ ⟨?_, h⟩, fun h ↦ h.2⟩
  exfalso
  exact h

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  exact fun h₁ h₂ ↦ ⟨fun h₃ ↦ ⟨h₁.1 h₃.1, h₂.1 h₃.2⟩, fun h₄ ↦ ⟨h₁.2 h₄.1, h₂.2 h₄.2⟩⟩

example : ¬(P ↔ ¬P) := by
  by_cases h : P
  · exact fun H ↦ (H.1 h) h
  · exact fun H ↦ h (H.2 h)

/- END TODO -/

/-
  # Disjonction / Or
  Use `\or` to write `∨`
-/

-- Use of the `left` tactic
example : P → P ∨ Q := by
  intro h
  left
  exact h

-- Use of the `right` tactic
example : Q → P ∨ Q := by
  intro h
  right
  exact h

-- symmetry of `∨`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl h =>
      right
      exact h
  | inr h =>
      left
      exact h

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
  refine fun h₁ h₂ h₃ ↦ ?_
  cases h₁ with
  | inl h => exact h₂ h
  | inr h => exact h₃ h

-- associativity of `∨`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases h with
    | inl h =>
        cases h with
        | inl h =>
            left
            exact h
        | inr h =>
            right
            left
            exact h
    | inr h =>
        right
        right
        exact h
  · cases h with
  | inl h =>
      left
      left
      exact h
  | inr h =>
      cases h with
      | inl h =>
          left
          right
          exact h
      | inr h =>
          right
          exact h

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  refine fun h₁ h₂ h₃ ↦ ?_
  cases h₃ with
  | inl h =>
      left
      exact h₁ h
  | inr h =>
      right
      exact h₂ h

example : (P → Q) → P ∨ R → Q ∨ R := by
  refine fun h₁ h₂ ↦ ?_
  cases h₂ with
  | inl h =>
      left
      exact h₁ h
  | inr h =>
      right
      exact h

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  refine fun h₁ h₂ ↦ ⟨fun h₃ ↦ ?_, fun h₄ ↦ ?_⟩
  · cases h₃ with
    | inl h =>
        left
        exact h₁.1 h
    | inr h =>
        right
        exact h₂.1 h
  · cases h₄ with
  | inl h =>
      left
      exact h₁.2 h
  | inr h =>
      right
      exact h₂.2 h

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  refine ⟨fun h₁ ↦ ⟨fun h₂ ↦ ?_, fun h₂ ↦ ?_⟩, fun h₂ ↦ (fun h₃ ↦ ?_)⟩
  · apply h₁
    left
    exact h₂
  · apply h₁
    right
    exact h₂
  · cases h₃ with
  | inl h => exact h₂.1 h
  | inr h => exact h₂.2 h

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  refine ⟨fun h₁ ↦ ?_, fun h₂ ↦ ?_⟩
  · by_contra H
    apply h₁
    constructor
    · by_contra hP
      apply H
      left
      exact hP
    · by_contra hQ
      apply H
      right
      exact hQ
  · cases h₂ with
  | inl h => exact fun H ↦ h H.1
  | inr h => exact fun H ↦ h H.2

/- END TODO -/
