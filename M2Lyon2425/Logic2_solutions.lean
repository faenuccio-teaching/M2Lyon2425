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
  rw [h]
  exact hx

example (x : α) (hP : P x) (h : P = Q) : Q x := by
  rw [← h] -- Use `\l` to write `←`
  exact hP

/-
  # Quantifiers
  Use `\forall` and `\exists` to write `∀` and `∃`.
-/

variable (R : Prop)

example (h : ∀ x : α, P x) (y : α) : P y := by
  exact h y

example : (∀ x : α, P x ∧ Q x) → ∀ x : α, P x := by
  intro h
  intro x
  exact (h x).left

-- Use of the `specialize` tactic and `Or.resolve_right/Or.resolve_left`
example : (∀ x, P x ∨ R) ↔ (∀ x, P x) ∨ R := by
  constructor
  · intro h
    by_cases hR : R
    · right
      exact hR
    · left
      intro x
      specialize h x
      exact Or.resolve_right h hR
  · intro h
    intro x
    by_cases hR : R
    · right
      exact hR
    · left
      exact Or.resolve_right h hR x

-- Use of the `use` tactic
example (x : α) (h : P x) : ∃ y, P y := by
  use x

-- Use of `Exists.choose / Exists.choose_spec`
example (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
--  have y := Exists.choose h
--  let y := h.choose -- Axiom of choice -- `let` also carries some data
--  have : P y ∧ Q y := by
--    exact h.choose_spec
--  use y
  use h.choose
  exact h.choose_spec.left

-- Use of the `cases` tactic
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  cases h with
  | intro x h =>
    use x
    constructor
    · exact h.right
    · exact h.left

/- TODO -/

example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).left
    · intro x
      exact (h x).right
  · intro h x
    constructor
    · exact h.left x
    · exact h.right x

example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  intro h1 h2 x
  apply h1 x
  exact h2 x

example : (∀ x, Q x) ∨ (∀ x, P x) → ∀ x, Q x ∨ P x := by
  intro h x
  cases h with
  | inl h =>
    left
    exact h x
  | inr h =>
    right
    exact h x

example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  apply h1 x
  exact h2 x

example (h : ¬ ∃ x, ¬ P x) : ∀ x, P x := by
  intro x
  by_contra h2
  have h3 : ∃ x, ¬ P x := by
    use x
  exact h h3

example : (∃ x : α, R) → R := by
  intro h
  exact h.choose_spec

example (x : α) : R → (∃ x : α, R) := by
  intro hR
  use x

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

example : (∀ x, P x) ↔ ¬ (∃ x, ¬ P x) := by
  sorry

example : (∃ x, P x) ↔ ¬ (∀ x, ¬ P x) := by
  sorry

example : (∀ x, P x → R) ↔ (∃ x, P x) → R := by
  sorry

example (a : α) : (∃ x, P x → R) ↔ ((∀ x, P x) → R) := by -- (*)
  constructor
  · intro h1 h2
    cases h1 with
    | intro x h =>
      exact h (h2 x)
  · contrapose! -- change `P → Q` to `¬ Q → ¬ P`; `!` also does `push_neg`
    intro h
    constructor
    · intro x
      exact (h x).left
    · specialize h a
      exact h.right

example (a : α) : (∃ x, R → P x) ↔ (R → ∃ x, P x) := by -- (*)
  constructor
  · intro h hR
    cases h with
    | intro x h =>
      use x
      exact h hR
  · contrapose!
    intro h
    constructor
    · specialize h a
      exact h.left
    · intro x
      specialize h x
      exact h.right

/- END TODO -/

/-
  # The Theorem of Diaconescu.
  The axiom of excluded middle follows from the axiom of choice
  (and also Function extensionality and propositional extensionality).
-/

-- Axiom of choice
-- axiom Classical.choice {α : Sort u} : Nonempty α → α

theorem Diaconescu (P : Prop) : P ∨ ¬ P := by -- This result is called `em` in Lean
  let T : Prop → Prop := fun A : Prop ↦ (A = True) ∨ P -- Use `\mapsto` to write `↦`
  let F : Prop → Prop := fun A : Prop ↦ (A = False) ∨ P
  -- Is there an A such that T A = F A? Yes iff P holds
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
        right
        exact h1
      | inr h2 =>
        right
        exact h1
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
        | inr _ =>
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
    right
    exact this
  | inr h =>
    left
    exact h
