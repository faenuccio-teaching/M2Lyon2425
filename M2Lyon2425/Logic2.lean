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
  rw [h]; assumption

example (x : α) (hP : P x) (h : P = Q) : Q x := by
  rw [←h]; assumption

/-
  # Quantifiers
  Use `\forall` and `\exists` to write `∀` and `∃`.
-/

variable (R : Prop)

example (h : ∀ x : α, P x) (y : α) : P y := by
  apply h

example : (∀ x : α, P x ∧ Q x) → ∀ x : α, P x := by
  intros h x
  specialize h x
  exact h.left

-- Use of the `specialize` tactic and `Or.resolve_right/Or.resolve_left`
example : (∀ x, P x ∨ R) ↔ (∀ x, P x) ∨ R := by
  constructor
  · intro h; by_cases hR : R 
    · right; assumption
    · left; intro x; specialize h x; cases h with
      | inl hP => assumption
      | inr hR' => exfalso; apply hR; assumption
  · intros h x; cases h with
    | inl hP => specialize hP x; left; assumption
    | inr hR => right; assumption

-- Use of the `use` tactic
example (x : α) (h : P x) : ∃ y, P y := by
  use x

-- Use of `Exists.choose / Exists.choose_spec`
example (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  let x := Exists.choose h
  have hPQ : P x ∧ Q x := Exists.choose_spec h
  use x; exact hPQ.left

-- Use of the `cases` tactic
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  cases h with
  | intro x hPQ => use x; constructor
                   · exact hPQ.right
                   · exact hPQ.left

/- TODO -/

example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h; 
    constructor <;> intro x <;> 
    specialize (h x)
    · exact h.left
    · exact h.right
  · intros h x; constructor
    · exact (h.left x)
    · exact (h.right x)

example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  intros f h x
  apply f; exact (h x)

example : (∀ x, Q x) ∨ (∀ x, P x) → ∀ x, Q x ∨ P x := by
  intros h x; cases h with
  | inl hQ => left; exact (hQ x)
  | inr hP => right; exact (hP x)

example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intros x; exact (h1 x (h2 x))

example (h : ¬ ∃ x, ¬ P x) : ∀ x, P x := by
  intros x; by_cases (P x)
  · assumption
  · exfalso; apply h; use x

example : (∃ _ : α, R) → R := by
  intro h
  have hR : R := Exists.choose_spec h
  assumption

example (x : α) : R → (∃ _ : α, R) := by
  intro hR; use x

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · intro h; cases h with
    | intro x h => cases h with
                   | inl hP => left; use x
                   | inr hQ => right; use x
  · intro h; cases h with
    | inl hP => cases hP with
                | intro x hP => use x; left; assumption
    | inr hQ => cases hQ with
                | intro x hQ => use x; right; assumption

example : (∀ x, P x) ↔ ¬ (∃ x, ¬ P x) := by
  constructor
  · intros f h; cases h with
    | intro x hP => apply hP; exact (f x)
  · intros h x; push_neg at h; exact (h x)

example : (∃ x, P x) ↔ ¬ (∀ x, ¬ P x) := by
  constructor
  · intros hEx h; cases hEx with
    | intro x hP => exact (h x hP)
  · intro h; push_neg at h; assumption

example : (∀ x, P x → R) ↔ (∃ x, P x) → R := by
  constructor
  · intros h hEx; cases hEx with
    | intro x hP => exact (h x hP)
  · intros h x hP; apply h; use x

example (a : α) : (∃ x, P x → R) ↔ (∀ x, P x) → R := by
  constructor
  · intros h hP; cases h with
    | intro x f => exact (f (hP x))
  · contrapose!; intros h; constructor
    · intros x; exact (h x).left
    · exact (h a).right

example (a : α) : (∃ x, R → P x) ↔ (R → ∃ x, P x) := by
  constructor
  · intros h hR; cases h with
    | intro x f => exists x; exact (f hR)
  · intros h; by_contra h'; push_neg at h'; have hR := (h' a).left
    cases (h hR) with
    | intro x hP => exact ((h' x).right hP)

/- END TODO -/

/-
  # The Theorem of Diaconescu.
  The axiom of excluded middle follows from the axiom of choice
  (and also Function extensionality and propositional extensionality).
-/

-- Axiom of choice
-- axiom Classical.choice {α : Sort u} : Nonempty α → α

theorem Diaconescu (P : Prop) : P ∨ ¬ P := by -- This result is called `em` in Lean
  let T : Prop → Prop := λ A ↦ (A = True ∨ P)
  let F : Prop → Prop := λ A ↦ (A = False ∨ P)
  have nonempty_T : ∃ x, T x := by use True; left; rfl
  have nonempty_F : ∃ x, F x := by use False; left; rfl
  let U := nonempty_T.choose -- Here, we use the axiom of choice
  let V := nonempty_F.choose -- Here, we use the axiom of choice
  have TU : T U := nonempty_T.choose_spec
  have FV : F V := nonempty_F.choose_spec
  have U_ne_V_or_P : (U ≠ V) ∨ P := by
    cases TU with
    | inl h1 =>
      cases FV with
      | inl h2 => left; rw [h1, h2]; trivial
      | inr h2 => right; exact h2
    | inr h1 => right; assumption
  have P_implies_U_eq_V : P → (U = V) := by
    intro hP
    have T_eq_F : T = F := by ext x; constructor <;> intro <;> right <;> exact hP
    have magic :
      ∀ proof_nonempty_T proof_nonempty_F,
          @Exists.choose Prop T proof_nonempty_T = @Exists.choose Prop F proof_nonempty_F := by
      -- Here, we use the fact that the axiom of choice is a function
      rw [T_eq_F]; intros; rfl
    exact magic nonempty_T nonempty_F
  cases U_ne_V_or_P with
  | inl h =>
    have := mt P_implies_U_eq_V h; right; assumption
  | inr h => left; assumption
