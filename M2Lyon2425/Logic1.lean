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
example : (P → Q → R) → (P → Q) → P → R := by
  intro h1
  intro h2
  intro hP
  apply h1
  · exact hP
  · apply h2
    exact hP


/- TODO -/

example : P → Q → P := by
  intro h1
  intro _
  exact h1


-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
example : P → (P → Q) → Q := by
  intro h1
  intro h2
  apply h2
  exact h1

-- Transitivity of `→`
example : (P → Q) → (Q → R) → P → R := by
  intro h1
  intro h2
  intro h3
  apply h2
  apply h1
  exact h3




example : (P → Q) → ((P → Q) → P) → Q := by
  intro h1
  intro h2
  apply h1
  apply h2
  exact h1


example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro h1
  intro h2
  intro _
  apply h2
  intro h4
  apply h1
  intro _
  exact h4


example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1
  intro h2
  intro h3
  apply h1
  intro h4
  apply h3
  apply h2
  exact h4






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
  intro _
  intro h1
  intro _
  intro _
  intro _
  exact h1


example : P → (P → False) → False := by
  intro h1
  intro h2
  apply h2
  exact h1


example : (P → False) → P → Q := by
  intro h1
  intro h2
  exfalso
  apply h1
  exact h2



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
  change (True → False) → False
  intro h1
  apply h1
  trivial


example : False → ¬True := by
  intro h1
  intro _
  exact h1


-- Use of the `by_contra` tactic
example : True → ¬False := by
  intro _
  by_contra h1
  exact h1




-- Use of the `have` tactic
example : (P → Q) → ¬Q → ¬P := by
  intro h1 h2 hP
  have  q: Q := h1 hP
  have := h2 q
  exact this



-- Use of the `by_cases` tactic
example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · have h1 := h hP
    exfalso
    exact h1




/- TODO -/

example : ¬False → True := by
  intro _
  trivial



example : P → ¬¬P := by
  change P → ¬ P → False
  change P → (P → False) → False
  intro h1
  intro h2
  apply h2
  exact h1


example : False → ¬P := by
  intro h
  exfalso
  exact h


example : P → ¬P → False := by
  intro h1
  intro h2
  apply h2
  exact h1



example : ¬¬False → False := by
  intro h
  apply h
  intro h1
  exact h1





example : (¬Q → ¬P) → P → Q := by
  intro h1
  intro h2
  by_contra h3
  have h4 := h1 h3
  have h5 := h4 h2
  exact h5



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
  intro h
  intro q
  cases q with
  | intro left right =>
  apply h
  exact left
  exact right




-- `∧` is symmetric
example : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · cases h with
    | intro left right =>
      exact right
  · cases h with
    | intro left right =>
      exact left



-- `∧` is transitive
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h
  intro h2
  constructor
  · cases h with
    | intro left right =>
       exact left
  · cases h2 with
    | intro left right =>
      exact right




example : P → P ∧ True := by
  intro h
  constructor
  · exact h
  · trivial


example : False → P ∧ False := by
  intro h
  constructor
  · exfalso
    exact h
  · exact h


example : (P ∧ Q → R) → P → Q → R := by
  intro h1 h2 h3
  apply h1
  constructor
  · exact h2
  · exact h3


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
  intro h
  intro h1
  constructor
  · intro h2
    cases h with
    | intro mp mpr =>
      cases h1 with
      | intro mp1 mpr2 =>
        apply mp1
        apply mp
        exact h2
  · intro h3
    cases h with
    | intro mp mpr =>
      cases h1 with
      | intro mp1 mpr2 =>
        apply mpr
        apply mpr2
        exact h3

--on peux faire avec des apply avec moins de constructor
-- meme plus vite avec des exact direct



example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h1
    constructor
    · cases h1 with
      | intro left right =>
        exact right
    · cases h1 with
      | intro left right =>
        exact left


  · intro h2
    constructor
    · cases h2 with
      | intro left right =>
        exact right
    · cases h2 with
      | intro left right =>
        exact left





example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro h1
    constructor
    · cases h1 with
      | intro left right =>
        cases left with
      | intro left1 right1 =>
          exact left1
    · constructor
      · cases h1 with
      | intro left right =>
          cases left with
          | intro left right1 =>
            exact right1
      · cases h1 with
        | intro left right =>
          exact right
  · intro h2
    constructor
    · constructor
      · cases h2 with
      | intro left right =>
        exact left
      · cases h2 with
      | intro left right =>
        cases right with
        | intro left right =>
          exact left
    · cases h2 with
    | intro left right =>
      cases right with
      | intro left right =>
        exact right



example : P ↔ P ∧ True := by
  constructor
  · intro h
    constructor
    · exact h
    · trivial
  · intro h
    cases h with
    | intro left right =>
      exact left





example : False ↔ P ∧ False := by
  constructor
  · intro h
    exfalso
    exact h
  · intro h
    cases h with
    | intro left right =>
      exact right


example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  constructor
  · intro h3
    constructor
    · cases h1 with
    | intro mp mpr =>
      cases h3 with
      | intro left right =>

        exact mp left
    · cases h2 with
    | intro mp mpr =>
      cases h3 with
      | intro left right =>
        exact mp right
  · intro h3
    constructor
    · cases h1 with
    | intro mp mpr =>
      cases h3 with
      | intro left right =>
        exact mpr left
    · cases h2 with
    | intro mp mpr =>
      cases h3 with
      | intro left right =>
        exact mpr right


example : ¬(P ↔ ¬P) := by
  intro h
  cases h with
  | intro mp mpr =>
    apply mp
    apply mpr
    intro h1
    apply mp
    exact h1
    exact h1
    apply mpr
    intro h2
    have h3 := mp h2
    exact h3 h2
    --apply mp a la place des 2 dernieres lignes
    --exact h2
    --exact h2

example : ¬ (P ↔ ¬ P) := by
  intro h
  cases h with
  | intro mp mpr =>
    apply mp
    apply mpr
    intro h1
    apply mp at h1
    apply h1
    apply mpr
    exact h1
    apply mpr
    intro h2
    apply mp at h2
    apply h2
    apply mpr
    exact h2

-- 1ere methode plus rapide




/- END TODO -/

/-
  # Disjunction / Or
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
lemma exclu :  P ∨ ¬ P := by
  by_cases hP : P
  . left
    exact hP
  . right
    exact hP








/- TODO -/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1
  intro h2
  intro h3
  cases h1 with
  | inl h =>
    apply h2
    exact h
  | inr h =>
    exact h3 h


-- associativity of `∨`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro h
    cases h with
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
  · intro h
    cases h with
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
  intro h1 h2 h3
  cases h3 with
  | inl h =>
    left
    apply h1
    exact h
  | inr h =>
    right
    apply h2
    exact h


example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h
  intro h1
  cases h1 with
  | inl h1 =>
    left
    apply h
    exact h1

  | inr h1 =>
    right
    exact h1

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  constructor
  . intro h3
    cases h3 with
    | inl h =>
      left
      apply h1.1
      exact h
    | inr h =>
      right
      apply h2.1
      exact h
  · intro h3
    cases h3 with
    | inl h =>
      left
      apply h1.2
      exact h
    | inr h =>
      right
      apply h2.2
      exact h


-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h1
    constructor
    · intro h2
      apply h1
      left
      exact h2
    · intro h2
      apply h1
      right
      exact h2
  · intro h1
    intro h2
    cases h2 with
    | inl h =>
      apply h1.left
      exact h
    | inr h =>
      apply h1.right
      exact h


example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h1
    have p : P ∨ ¬ P := by tauto
    --have q : Q ∨ ¬ Q := exclu Q
    cases p with
    | inl h =>
      right
      intro h2
      apply h1
      constructor
      · exact h
      · exact h2
    | inr h =>
      left
      exact h
  · intro h
    intro h1
    cases h with
    | inl h =>
      apply h
      exact h1.left
    | inr h =>
      apply h
      exact h1.right

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  push_neg
  tauto








/- END TODO -/
