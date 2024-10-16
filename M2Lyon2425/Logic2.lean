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
  rw [← h]
  exact hP

/-
  # Quantifiers
  Use `\forall` and `\exists` to write `∀` and `∃`.
-/

variable (R : Prop)

example (h : ∀ x : α, P x) (y : α) : P y := by
  exact h y

example : (∀ x : α, P x ∧ Q x) → ∀ x : α, P x := by
  intro h1
  intro x
  exact (h1 x).left

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
  . intro h
    intro x
    by_cases hR : R
    · right
      exact hR
    · left
      exact h.resolve_right hR x

-- Use of the `use` tactic
example (x : α) (h : P x) : ∃ y, P y := by
  use x

-- Use of `Exists.choose / Exists.choose_spec`
example (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  let y := h.choose  -- requires the axiom of choice. Also, use `let` instead of `have` here
  have : P y ∧ Q y := by
    exact h.choose_spec
  use y
  exact this.left

-- Use of the `cases` tactic
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  cases h with
  | intro w h =>
    use w
    constructor
    · exact h.right
    · exact h.left

/- TODO -/

example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h1
    constructor
    · intro x
      exact (h1 x).left
    · intro x
      exact (h1 x).right
  · intro h1 x
    constructor
    · exact h1.left x
    · exact h1.right x

example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  intro h1 h2 x
  exact (h1 x) (h2 x)

example : (∀ x, Q x) ∨ (∀ x, P x) → ∀ x, Q x ∨ P x := by
  intro h1 x
  cases h1 with
  | inl h =>
    left
    exact h x
  | inr h =>
    right
    exact h x

example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  exact (h1 x) (h2 x)

example (h : ¬ ∃ x, ¬ P x) : ∀ x, P x := by
  push_neg at h
  exact h

example : (∃ _x : α, R) → R := by
  intro h1
  exact h1.choose_spec

example (x : α) : R → (∃ _x : α, R) := by
  intro h
  use x

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · intro h
    cases h with
    | intro w hor =>
      cases hor with
      | inl h =>
        left
        use w
      | inr h =>
        right
        use w
  · intro hor
    cases hor with
    | inl h =>
      let x := h.choose
      use x
      left
      exact h.choose_spec
    | inr h =>
      let x := h.choose
      use x
      right
      exact h.choose_spec

-- Galère avec Loris

example : (∀ x, P x) ↔ ¬ (∃ x, ¬ P x) := by
  constructor
  · intro h1 
    change (∃ x, (P x → False)) → False
    intro h2
    cases h2 with
    | intro w h => 
      exact h (h1 w)
  · intro h1 e
    change (∃ x, (P x → False)) → False at h1
    by_cases h : P e
    · exact h
    · exfalso
      apply h1
      use e

example : (∃ x, P x) ↔ ¬ (∀ x, ¬ P x) := by
  constructor 
  · intro h1 h2
    let y := h1.choose
    have Py := h1.choose_spec
    specialize h2 y
    let f := h2 Py 
    exact f
  · intro h1 
    change (∀ x, (P x) → False) → False at h1
    by_cases hP : ∃ x, P x
    · exact hP
    · exfalso
      apply h1
      intro y Py
      apply hP
      use y


-- Trois preuves de la même chose

example : (∀ x, P x → R) ↔ (∃ x, P x) → R := by
  constructor
  · intro h1 h2
    cases h2 with
    | intro w h =>
      exact h1 w h
  · intro h1 h2 h3
    by_cases h : ∃ x, P x
    · exact h1 h
    · exfalso
      push_neg at h
      have h4 := h h2
      change P h2 → False at h4
      exact h4 h3

example : (∀ x, P x → R) ↔ (∃ x, P x) → R := by
  constructor
  · intro h1 h2
    cases h2 with
    | intro w h =>
      exact h1 w h
  · intro h1 h2 h3
    apply h1
    use h2

example : (∀ x, P x → R) ↔ (∃ x, P x) → R := by
  constructor
  · intro h1 h2
    cases h2 with
    | intro w h =>
      exact h1 w h
  · intro h1 h2 h3
    exact h1 ⟨h2, h3 ⟩

example (a : α) : (∃ x, P x → R) ↔ (∀ x, P x) → R := by
  constructor
  · intro h1 h2
    cases h1 with
    | intro w h => exact h (h2 w)
  · contrapose!
    intro h1
    constructor
    · intro x
      exact (h1 x).left
    · exact (h1 a).right

example (a : α) : (∃ x, R → P x) ↔ (R → ∃ x, P x) := by
  constructor
  · intro h1 hR
    cases h1 with
    | intro w h =>
      use w
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
  (and also follows from Function extensionality and propositional extensionality).
-/

-- Axiom of choice
-- axiom Classical.choice {α : Sort u} : Nonempty α → α

theorem Diaconescu (P : Prop) : P ∨ ¬ P := by -- This result is called `em` in Lean
  let T : Prop → Prop := fun A ↦ ((A = True) ∨ P)
  let F : Prop → Prop := fun A ↦ ((A = False) ∨ P)
  -- is there an A s.t. T A = F A
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
    right
    exact this
  | inr h =>
    left
    exact h


#print axioms Diaconescu
