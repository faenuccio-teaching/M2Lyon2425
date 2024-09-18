/-
  ## LOGIC 2
  Credits.
  * Theorem Proving in Lean 4, J. Avigad, L. de Moura, S. Kong, S. Ullrich
  * The Mechanics of Proof, H. Macbeth
  * Lean source code (part by L. de Moura, M. Carneiro)
-/
import Mathlib.Tactic.Common

/-
  # Functions (preview)
  Use `\to` to write `→`
-/

variable (α : Type*) (P Q : α → Prop) -- Use `\alpha` to write `α`

-- Use of the `rw` tactic
example (x y : α) (hx : P x) (h : y = x) : P y := by
  sorry

example (x : α) (hP : P x) (h : P = Q) : Q x := by
  sorry

/-
  # Quantifiers
  Use `\forall` and `\exists` to write `∀` and `∃`.
-/

variable (R : Prop)

example (h : ∀ x : α, P x) (y : α) : P y := by
  sorry

example : (∀ x : α, P x ∧ Q x) → ∀ x : α, P x := by
  sorry

-- Use of the `specialize` tactic and `Or.resolve_right/Or.resolve_left`
example : (∀ x, P x ∨ R) ↔ (∀ x, P x) ∨ R := by
  sorry

-- Use of the `use` tactic
example (x : α) (h : P x) : ∃ y, P y := by
  sorry

-- Use of `Exists.choose / Exists.choose_spec`
example (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  sorry

-- Use of the `cases` tactic
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  sorry

/- TODO -/

example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  sorry

example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  sorry

example : (∀ x, Q x) ∨ (∀ x, Q x) → ∀ x, Q x ∨ P x := by
  sorry

example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  sorry

example (h : ¬ ∃ x, ¬ P x) : ∀ x, P x := by
  sorry

example : (∃ x : α, R) → R := by
  sorry

example (x : α) : R → (∃ x : α, R) := by
  sorry

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

example : (∀ x, P x) ↔ ¬ (∃ x, ¬ P x) := by
  sorry

example : (∃ x, P x) ↔ ¬ (∀ x, ¬ P x) := by
  sorry

example : (∀ x, P x → R) ↔ (∃ x, P x) → R := by
  sorry

example : (∃ x, P x → R) ↔ (∀ x, P x) → R := by
  sorry

example : (∃ x, R → P x) ↔ (R → ∃ x, P x) := by
  sorry

/- END TODO -/

/-
  # The Theorem of Diaconescu.
  The axiom of excluded middle follows from the axiom of choice
  (and also Function extensionality and propositional extensionality).
-/

-- Axiom of choice
-- axiom Classical.choice {α : Sort u} : Nonempty α → α

example (P : Prop) : P ∨ ¬ P := by -- This result is called `em` in Lean
  let T : Prop → Prop := fun A ↦ (A = True ∨ P)
  let F : Prop → Prop := fun A ↦ (A = False ∨ P)
  have nonempty_T : ∃ x, T x := by
    use True
    left
    rfl
  have nonempty_F : ∃ x, F x := by
    use False
    left
    rfl
  let U := nonempty_T.choose -- Here, we use the axiom of choice
  let V := nonempty_F.choose -- Here, we use the axiom of choice
  have TU : T U := nonempty_T.choose_spec
  have FV : F V := nonempty_F.choose_spec
  have U_ne_V_or_P : (U ≠ V) ∨ P := by
    cases TU with
    | inl h1 =>
      cases FV with
      | inl h2 =>
        left
        rw [h1, h2]
        trivial
      | inr h2 =>
        right
        exact h2
    | inr h1 =>
      cases FV with
      | inl h2 =>
        sorry
      | inr h2 =>
        sorry
  have P_implies_U_eq_V : P → (U = V) := by
    intro hP
    have T_eq_F : T = F := by
      ext x --  Here, we are using function extensionality
      constructor
      · intro hT
        cases hT with
        | inl _ =>
            right
            exact hP
        | inr _ =>
            right
            exact hP
      · intro hF
        cases hF with
        | inl _ =>
            right
            exact hP
        | inr h =>
            right
            exact hP
    have magic :
      ∀ proof_nonempty_T proof_nonempty_F,
          @Exists.choose Prop T proof_nonempty_T = @Exists.choose Prop F proof_nonempty_F := by
      -- Here, we use the fact that the axiom of choice is a function
      rw [T_eq_F]
      intro _ _
      rfl
    exact magic nonempty_T nonempty_F
  cases U_ne_V_or_P with
  | inl h =>
    have := mt P_implies_U_eq_V h
    sorry
  | inr h =>
    sorry
