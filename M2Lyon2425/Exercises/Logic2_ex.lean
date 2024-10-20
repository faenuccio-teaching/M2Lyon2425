import Mathlib.Tactic.Common

variable (α : Type*) (P Q : α → Prop) -- Use `\alpha` to write `α`

variable (R : Prop)

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
  have h3 := h1 x
  apply h3
  exact h2 x

example : (∀ x, Q x) ∨ (∀ x, Q x) → ∀ x, Q x ∨ P x := by
  intro h x
  left
  cases h with
  | inl h => exact h x
  | inr h => exact h x

example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  apply h1 x
  exact h2 x

example (h : ¬ ∃ x, ¬ P x) : ∀ x, P x := by
  push_neg at h --cheating, but works
  exact h
  --intro x
  --by_contra
  --have := h x --nope, doesn't make sense, not a valid proof
  --exact this

example : (∃ _ : α, R) → R := by
  intro h
  exact h.choose_spec

example (x : α) : R → (∃ _ : α, R) := by
  intro H
  use x

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · intro h
    let y := Exists.choose h
    have h1 := h.choose_spec
    cases h1 with
    | inl h2 => 
      left
      use y
    | inr h2 => 
      right
      use y
  · intro h 
    cases h with
    | inl h => 
      let y := Exists.choose h
      have h1 := h.choose_spec
      use y
      left
      exact h1
    | inr h => 
      let y := Exists.choose h
      have h1 := h.choose_spec
      use y
      right
      exact h1

example : (∀ x, P x) ↔ ¬ (∃ x, ¬ P x) := by
  push_neg --very much cheating
  constructor
  · intro h
    exact h
  · intro H
    exact H

example : (∃ x, P x) ↔ ¬ (∀ x, ¬ P x) := by
  constructor
  · intro h1 h2
    let y := Exists.choose h1
    have hP := h1.choose_spec
    have h := h2 y
    apply h
    exact hP
  · intro h1
    change (∀ (x : α), ¬ P x) → False at h1
    by_contra h 
    apply h1
    intro x
    by_cases hP : P x
    · have y : ∃ x, P x := by
        use x
      exfalso
      exact h y
    · exact hP

example : (∀ x, P x → R) ↔ (∃ x, P x) → R := by
  constructor
  · intro h1 h2
    let y := Exists.choose h2
    have Y := h2.choose_spec
    specialize h1 y
    apply h1
    exact Y
  · intro h1 x h2
    apply h1
    use x

example  (a : α) : (∃ x, P x → R) ↔ (∀ x, P x) → R := by --recheck it
  constructor
  · intro h1 h2
    cases h1 with
    | intro x h => 
      exact h (h2 x)
  · contrapose! --"!" also does 'push_neg'
    intro h 
    constructor
    · intro x
      exact (h x).left
    · specialize h a
      exact h.right

example  (a : α) : (∃ x, R → P x) ↔ (R → ∃ x, P x) := by --recheck it
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
-- axiom Classical.choice {α : Sort u} : Nonempty α → α --As we've seen, in lean this is used as "something exists → I can choose an element", this is what the axiom of choice is in lean.

example (P : Prop) : P ∨ ¬ P := by -- This result is called `em` in Lean
  let T : Prop → Prop := fun A ↦ (A = True ∨ P) --`\mapsto` to ↦
  let F : Prop → Prop := fun A ↦ (A = False ∨ P)
  --Is there an A such that T A = F A?
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
      --cases FV with
      --inl h2 =>
      --right
      --exact h1
      --inr h2 =>
      right
      exact h1
  have P_implies_U_eq_V : P → (U = V) := by
    intro hP
    have T_eq_F : T = F := by
      ext x --  Here, we are using function extensionality --also transforms the equality in the goal into a ↔ bc they're functions on Prop type, and for Props equality is defined as a ↔. For other types, it's not
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
        --"Every proof that T is non empty is a proof that F is non empty"
        --Notation means "Use the func Exists.choose, for which we provide the type Prop, a fun T, and we provide the proof that T is non empty (so it exists smt)"
      rw [T_eq_F]
      intro _ _
      rfl --the axiom of choice in Lean is implemented as the existence of ONE specific function, that has for domain all possible types, and produces one instance for each of them. FOR A SPECIFIC TYPE it produces always the same result. So if we want to choose a Prop, we always end up with the same result.
    exact magic nonempty_T nonempty_F
    --? ok so if P then T and F are the same function alright, but the U and V that we chose are also the same? What if we chose 2 different istances of the same thing?
    --ASK
  cases U_ne_V_or_P with
  | inl h =>
    have := mt P_implies_U_eq_V h
    right
    exact this
  | inr h =>
    left
    exact h
