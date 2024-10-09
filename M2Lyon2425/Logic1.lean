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
example : P = P := by rfl

-- Use of the `exact` tactic
example (hP : P) : P := by assumption

/-
  # Implication
  Use `\to` to write `→`
-/

-- Use of the `intro` tactic
example : P → P := by
  intro hP
  assumption

-- Use of the `apply` tactic
example (h : P → Q) (hP : P) : Q := by
  apply h
  refine hP

example (hQ : Q) : P → Q := by
  intro _; assumption

-- Let's try something a bit more complicated
-- Use `\.` to write `·`
example : (P → Q → R) → (P → Q) → P → R := by
  intro h1
  intro h2
  intro hP
  apply h1
  · refine hP
  · apply h2; assumption

example : P → Q → P := by intros hP _; assumption

-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
example : P → (P → Q) → Q := by intros hP h; apply h; assumption

-- Transitivity of `→`
example : (P → Q) → (Q → R) → P → R := by intros h h' hP; apply h'; apply h; assumption

example : (P → Q) → ((P → Q) → P) → Q := by intros h h'; apply h; apply h'; assumption

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intros h h₀ h₁
  apply h₀; intro _
  apply h; intro _
  apply h₁; intro hR
  apply h₀; intro; assumption

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intros h₀ h₁ h₂; apply h₀; intro hQ; apply h₂; apply h₁; exact hQ

/-
  # `True` and `False`
  The values `True` and `False` are also defined and can be used to write
  propositions.
-/

-- Use of the `trivial` tactic
example : True := by trivial

-- Use of the `exfalso` tactic
example : False → P := by intro; exfalso; assumption

example : True → True := by trivial

example : False → True := by trivial

example : False → False := by trivial

example : (True → False) → False := by trivial

example : True → False → True → False → True → False := by trivial

example : P → (P → False) → False := by
  intros hP f; apply f; assumption

example : (P → False) → P → Q := by
  intros f hP; exfalso; apply f; assumption

example : (True → False) → P := by
  intros f; exfalso; apply f; trivial

/- END TODO -/

/-
  # Negation
  Use `\not` to write `¬`
  The definition of `¬ P` is `P → False`: they are *definitionnally equal*
-/

-- Use of the `change` tactic
example : ¬True → False := by
  change (True → False) → False
  trivial

example : False → ¬True := by
  change False → True → False
  intros; assumption

-- Use of the `by_contra` tactic
example : True → ¬False := by
  intros _; by_contra; assumption

-- Use of the `have` tactic
example : (P → Q) → ¬Q → ¬P := by
  intro h1 h2 hP
  have hQ := h1 hP
  apply h2
  assumption

-- Use of the `by_cases` tactic
example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · assumption
  · exfalso; apply h; assumption

example : ¬False → True := by
  change (False → False) → True
  intro _; trivial

example : P → ¬¬P := by
  change P → ¬ P → False
  change P → (P → False) → False
  intros hP f; apply f; assumption

example : False → ¬P := by
  intros F _; assumption

example : P → ¬P → False := by
  intros hP f; apply f; assumption

example : ¬¬False → False := by
  intros F; apply F; change (False → False); intro; assumption

example : (¬Q → ¬P) → P → Q := by
  intros f hP; by_contra hnQ
  have hnP := f hnQ
  exfalso; apply hnP; assumption

/- END TODO -/

/-
  # Conjonction / And
  Use `\and` to write `∧`
-/

-- Use of the `constructor` tactic
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · assumption
  · assumption

-- Use of the `cases` tactic
example : P ∧ Q → P := by
  intro h
  cases h
  assumption

/- TODO -/

example : P ∧ Q → Q := by
  intros h; cases h; assumption

example : (P → Q → R) → P ∧ Q → R := by
  intros f h; cases h; apply f
  · assumption
  · assumption

-- `∧` is symmetric
example : P ∧ Q → Q ∧ P := by
  intros h; cases h
  constructor
  · assumption
  · assumption

-- `∧` is transitive
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intros f g; cases f; cases g
  constructor
  · assumption
  · assumption

example : P → P ∧ True := by
  intros hP; constructor
  · assumption
  · trivial

example : False → P ∧ False := by
  intros F; constructor
  · exfalso; assumption
  · assumption

example : (P ∧ Q → R) → P → Q → R := by
  intros h hP hQ; apply h
  constructor
  · assumption
  · assumption

/- END TODO -/

/-
  # Equivalence
  Use `\iff` to write `↔`
  `P ↔ Q` can broken into two goals: `P → Q` and `Q → P` using `constructor`.
-/

example : P ↔ P := by
  constructor
  · intros hP; assumption
  · intros hP; assumption

lemma iff_sym : (P ↔ Q) → (Q ↔ P) := by
  intro h
  cases h
  constructor
  · assumption
  · assumption

-- Use of the `lemma` tactic
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · apply iff_sym
  · apply iff_sym

/- TODO -/

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intros f g
  · constructor
    · intros hP; cases f with
      | intro hPQ hQP => cases g with
                         | intro hQR hRQ => apply hQR; apply hPQ; assumption
    · intros hR; cases f with
      | intro hPQ hQP => cases g with
                         | intro hQR hRQ => apply hQP; apply hRQ; assumption

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h; cases h; constructor
    · assumption
    · assumption
  · intro h; cases h; constructor
    · assumption
    · assumption

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro h; cases h with
    | intro hPQ hR => cases hPQ; constructor
                      · assumption
                      · constructor
                        · assumption
                        · assumption
  · intro h; cases h with
    | intro hP hQR => cases hQR; constructor
                      · constructor
                        · assumption
                        · assumption
                      · assumption  

example : P ↔ P ∧ True := by
  constructor
  · intro hP; constructor
    · assumption
    · trivial
  · intro h; cases h; assumption

example : False ↔ P ∧ False := by
  constructor
  · intro contra; exfalso; assumption
  · intro h; cases h; assumption

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intros hPQ hRS; cases hPQ with
  | intro hPQ hQP => cases hRS with
                     | intro hRS hSR => constructor
                                        · intro hPR; constructor
                                          · apply hPQ; cases hPR; assumption
                                          · apply hRS; cases hPR; assumption
                                        · intro hQS; constructor
                                          · apply hQP; cases hQS; assumption
                                          · apply hSR; cases hQS; assumption

example : ¬(P ↔ ¬P) := by
  change (P ↔ ¬P) → False; intro contra
  cases contra with
  | intro f g => apply f; apply g; intro hP; apply f; assumption; assumption; apply g
                 intro hP; apply f; assumption; assumption

/- END TODO -/

/-
  # Disjunction / Or
  Use `\or` to write `∨`
-/

-- Use of the `left` tactic
example : P → P ∨ Q := by
  intro hP; left; assumption

-- Use of the `right` tactic
example : Q → P ∨ Q := by
  intro hQ; right; assumption

-- symmetry of `∨`
example : P ∨ Q → Q ∨ P := by
  intro hPQ; cases hPQ
  · right; assumption
  · left; assumption

-- The law of excluded middle is not by default in Lean but we included some conventions
-- from Mathlib including this law (and we actually already used it.)
example : P ∨ ¬ P := by
  by_cases h : P 
  · left; assumption
  · right; assumption

/- TODO -/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intros hPQ hPR hQR; cases hPQ with
  | inl hP => apply hPR; assumption
  | inr hQ => apply hQR; assumption

-- associativity of `∨`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro h; cases h with
    | inl h => cases h with
               | inl hP => left; assumption
               | inr hQ => right; left; assumption
    | inr hR => right; right; assumption
  · intro h; cases h with
    | inl hP => left; left; assumption
    | inr h => cases h with
               | inl hQ => left; right; assumption      
               | inr hR => right; assumption

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intros f g h; cases h with
  | inl hP => left; apply f; assumption
  | inr hQ => right; apply g; assumption

example : (P → Q) → P ∨ R → Q ∨ R := by
  intros f h; cases h with
  | inl hP => left; apply f; assumption
  | inr hR => right; assumption

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intros hPR hQS; constructor
  · intro hPQ; cases hPQ with
    | inl hP => left; cases hPR with
                      | intro f _ => apply f; assumption
    | inr hQ => right; cases hQS with
                       | intro f _ => apply f; assumption
  · intro hRS; cases hRS with
    | inl hR => left; cases hPR with
                      | intro _ f => apply f; assumption
    | inr hS => right; cases hQS with
                       | intro _ f => apply f ; assumption

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro f; constructor
    · intro hP; apply f; left; assumption
    · intro hQ; apply f; right; assumption
  · intros hnPQ hPQ; cases hPQ with
    | inl hP => cases hnPQ with
                | intro hnP _ => apply hnP; assumption
    | inr hQ => cases hnPQ with
                | intro _ hnQ => apply hnQ; assumption

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro f; by_cases h : (¬P ∨ ¬Q)
    · assumption
    · exfalso; apply f; constructor
      · by_cases hP : P
        · assumption
        · exfalso; apply h; left; assumption
      · by_cases hQ : Q
        · assumption
        · exfalso; apply h; right; assumption
  · intros f h; cases f with
    | inl hnP => cases h; apply hnP; assumption
    | inr hnQ => cases h; apply hnQ; assumption

/- END TODO -/
