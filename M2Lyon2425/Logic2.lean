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

example (h : ∀ x : α, P x) (y : α) : P y := h y

example : (∀ x : α, P x ∧ Q x) → ∀ x : α, P x := fun H x ↦ (H x).1

-- Use of the `specialize` tactic and `Or.resolve_right/Or.resolve_left`
example : (∀ x, P x ∨ R) ↔ (∀ x, P x) ∨ R := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases hR : R
    · right
      exact hR
    · left
      intro x
      specialize h x
      exact h.resolve_right hR
  · intro x
    cases h with
    | inl h =>
        left
        specialize h x
        exact h
    | inr h =>
        right
        exact h

-- Use of the `use` tactic
example (x : α) (h : P x) : ∃ y, P y := by
  use x

-- Use of `Exists.choose / Exists.choose_spec`
example (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  use h.choose
  exact h.choose_spec.1

-- Use of the `cases` tactic
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  cases h with
  | intro w h =>
      use w
      exact ⟨h.2, h.1⟩

/- TODO -/

example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) :=
  ⟨fun h ↦ ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩, fun h x ↦ ⟨h.1 x, h.2 x⟩⟩

example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
  fun h h₂ x ↦ h x (h₂ x)

example : (∀ x, Q x) ∨ (∀ x, Q x) → ∀ x, Q x ∨ P x := by
  refine fun h x ↦ ?_
  left
  cases h with
  | inl h => exact h x
  | inr h => exact h x

example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x :=
  fun x ↦ h1 x (h2 x)

example (h : ¬ ∃ x, ¬ P x) : ∀ x, P x := by
  push_neg at h
  exact h

example : (∃ _ : α, R) → R := (·.choose_spec)

example (x : α) : R → (∃ _ : α, R) := (⟨x, ·⟩)

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases h with
    | intro w h =>
        cases h with
        | inl _ =>
            left
            use w
        | inr _ =>
            right
            use w
  · cases h with
    | inl h =>
        use h.choose
        left
        exact h.choose_spec
    | inr h =>
        use h.choose
        right
        exact h.choose_spec

example : (∀ x, P x) ↔ ¬ (∃ x, ¬ P x) := by
  refine ⟨fun h h₂ ↦ h₂.choose_spec (h h₂.choose), fun h x ↦ ?_⟩
  push_neg at h
  exact h x

example : (∃ x, P x) ↔ ¬ (∀ x, ¬ P x) := by
  refine ⟨fun h h₂ ↦ h₂ h.choose h.choose_spec, fun h ↦ ?_⟩
  push_neg at h
  exact h

example : (∀ x, P x → R) ↔ (∃ x, P x) → R :=
  ⟨fun h h₂ ↦ h h₂.choose h₂.choose_spec, fun h x hx ↦ h ⟨x, hx⟩⟩

example (a : α) : (∃ x, P x → R) ↔ (∀ x, P x) → R := by
  refine ⟨fun h h₂ ↦ h.choose_spec (h₂ h.choose), ?_⟩
  contrapose!
  intro hx
  exact ⟨fun x ↦ (hx x).1, (hx a).2⟩

example (a : α) : (∃ x, R → P x) ↔ (R → ∃ x, P x) := by
  refine ⟨fun h r ↦ ⟨h.choose, h.choose_spec r⟩, ?_⟩
  contrapose!
  exact fun hx ↦ ⟨(hx a).1, fun x ↦ (hx x).2⟩

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
