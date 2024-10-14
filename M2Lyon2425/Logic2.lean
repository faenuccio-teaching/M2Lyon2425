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
-- star
-- Use of the `rw` tactic
example (x y : α) (hx : P x) (h : y = x) : P y := by
  rw[h]
  exact hx

example (x : α) (hP : P x) (h : P = Q) : Q x := by
  --rw[← h]
  rw[h] at hP
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
  have h1 := h x
  exact h1.left



-- Use of the `specialize` tactic and `Or.resolve_right/Or.resolve_left`
example : (∀ x, P x ∨ R) ↔ (∀ x, P x) ∨ R := by
  constructor
  · intro h
    by_cases hR : R
    · right
      exact hR
    · left
      intro x
      specialize h x --diff avec apply ?
      have := Or.resolve_right h hR
      exact this
  · intro h
    intro x
    by_cases hR : R
    · right
      exact hR
    · left
      have := Or.resolve_right h hR x
      exact this




-- Use of the `use` tactic
example (x : α) (h : P x) : ∃ y, P y := by
  use x


-- Use of `Exists.choose / Exists.choose_spec`
example (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  --obtain ⟨ w ,hw ⟩ := h
  --let  y := Exists.choose h --use axiom of choice pas have sinon on perd l'info
  --have h1 : P y ∧ Q y:= Exists.choose_spec h
  --use y
  obtain ⟨ w ,h1⟩ := h
  use w
  exact h1.left

  --use h.choose h.choose_spec left va plus vite



-- Use of the `cases` tactic
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  cases h with
  | intro x h =>
    use x
    constructor
    · exact h.right
    · exact h.left

-- quand on construit faut utiliser .choose pour pas oublier la data
/- TODO -/

example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h
    constructor
    · intro x
      have h1 := h x
      exact h1.left
    · intro y
      exact (h y ).right
  · intro h
    cases h with
    | intro left right =>
      intro x
      have h1 := left x
      have h2 := right x
      constructor
      · exact h1
      · exact h2



example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
   intro h
   intro h1
   intro y
   have :=  h1 y
   have h2 := h y
   exact h2 this



example : (∀ x, Q x) ∨ (∀ x, P x) → ∀ x, Q x ∨ P x := by
  intro h
  cases h with
  | inl h =>
    intro x
    have := h x
    left
    exact this
  | inr h =>
    intro x
    have := h x
    right
    exact this

example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  have := h1 x
  have h3 := h2 x
  apply this
  exact h3

example (h : ¬ ∃ x, ¬ P x) : ∀ x, P x := by
  intro x
  by_contra h1
  apply h
  use x

example : (∃ _ : α, R) → R := by
  intro h
  exact h.choose_spec


example (x : α) : R → (∃ _ : α, R) := by
  intro h
  use x



example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · intro h
    let y := h.choose

    have h2 : P y ∨ Q y := Exists.choose_spec h
    cases h2 with
    | inl h =>
      left
      use y

    | inr h =>
      right
      use y
  · intro h
    cases h with
    | inl h =>
      obtain ⟨ w , hw ⟩  := h
      use w
      left
      exact hw
    | inr h =>
      obtain⟨ w ,hw ⟩ := h
      use w
      right

      exact hw


example : (∀ x, P x) ↔ ¬ (∃ x, ¬ P x) := by
  constructor
  · intro h
    by_contra h1
    obtain ⟨ w , hw⟩ := h1
    apply hw
    specialize h w
    exact h
  · intro h
    intro x
    by_contra h1
    apply h
    use x



example : (∃ x, P x) ↔ ¬ (∀ x, ¬ P x) := by
  constructor
  · intro h
    by_contra h1
    obtain ⟨ w,hw⟩ := h
    specialize h1 w
    exact h1 hw
  · intro h
    by_contra h1
    apply h
    intro x
    intro h2
    apply h1
    use x




example : (∀ x, P x → R) ↔ (∃ x, P x) → R := by
  constructor
  . intro h
    intro h1
    obtain ⟨ w ,hw ⟩ := h1
    specialize h w
    exact h hw
  · intro h
    intro x
    intro h1
    apply h
    use x



example (a : α): (∃ x, P x → R) ↔ (∀ x, P x) → R := by -- c cho
  constructor
  · intro h1 h2
    cases h1 with
    | intro w h =>
      have h3 := h2 w
      apply h
      exact h3
  · contrapose! -- ! do push neg
    intro h
    constructor
    · intro x
      have :=h x
      exact this.left
    · specialize h a
      exact h.right






example (a : α): (∃ x, R → P x) ↔ (R → ∃ x, P x) := by
  constructor
  · intro h
    intro h1
    cases h with
    | intro w h =>
      use w
      apply h
      exact h1
  · contrapose!
    intro h

    constructor
    · specialize h a
      exact h.left
    · intro y
      have h2 := h y
      exact h2.right

/- END TODO -/

/-
  # The Theorem of Diaconescu.
  The axiom of excluded middle follows from the axiom of choice
  (and also Function extensionality and propositional extensionality).
-/

-- Axiom of choice
-- axiom Classical.choice {α : Sort u} : Nonempty α → α

theorem diaconescu (P : Prop) : P ∨ ¬ P := by -- This result is called `em` in Lean
  let T : Prop → Prop := fun A ↦ (A = True) ∨ P -- '\mapsto
  let F : Prop → Prop := fun A ↦ (A = False) ∨ P
  -- is there a such as T A = F A equiv a P holds
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
        exact h2
  have P_implies_U_eq_V : P → (U = V) := by
    intro hP
    have T_eq_F : T = F := by
      ext x --  Here, we are using function extensionality and prop exten
      constructor
      · intro _
        right
        exact hP
        --cases hT with
        --| inl _ =>
        --    right
        --    exact hP
        --| inr _ =>
        --    right
         --   exact hP
      · intro _
        right
        exact hP
        --cases hF with
        --| inl _ =>
        --    right
        --    exact hP
        --| inr _ =>
        --    right
        --    exact hP

    have magic :
      ∀ proof_nonempty_T proof_nonempty_F,
          @Exists.choose Prop T proof_nonempty_T = @Exists.choose Prop F proof_nonempty_F := by
      -- Here, we use the fact that the axiom of choice is a function arobase permet de donner les arguments
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

#print axioms diaconescu
