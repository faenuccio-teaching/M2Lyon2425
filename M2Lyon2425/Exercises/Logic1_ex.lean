import Mathlib.Tactic.Common
-- Introduce some propositions
variable (P Q R S : Prop) --we are introducing some variables and giving them their type: the Prop type

-- Use of the `rfl` tactic

/- TODO -/

example : P → Q → P := by
  intro hP
  intro hQ
  exact hP

-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
example : P → (P → Q) → Q := by
  intro hP
  intro h1
  apply h1
  exact hP

-- Transitivity of `→`
example : (P → Q) → (Q → R) → P → R := by
  intro h1
  intro h2
  intro hP
  apply h2
  apply h1
  exact hP

example : (P → Q) → ((P → Q) → P) → Q := by
  intro h1
  intro h2
  apply h1
  apply h2
  exact h1

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro h1
  intro h2
  intro h3
  apply h2
  intro hQ
  apply h1
  intro hP --from here we could skip the rest, at this point the goal is prove Q is true, and we already have it. The proof could have ended here
  --h3 so it's useless, bc we can stop here. This shows what hypothesis can be deleted in a statement, neat in mathematics.
  apply h3
  intro hR
  exact hP

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1
  intro h2
  intro h3 --we can write intro h1 h2 h3 too, like, merge them. Lean understands
  apply h1
  intro hQ
  apply h3
  apply h2 --we can't merge these apply tho.
  exact hQ

/- END TDOO-/

/- TODO -/

example : True → True := by
  trivial 

example : False → True := by
  trivial

example : False → False := by
  trivial

example : (True → False) → False := by
  trivial

example : True → False → True → False → True → False := by
  trivial

example : P → (P → False) → False := by
  intro hP
  intro h2
  apply h2
  exact hP

example : (P → False) → P → Q := by
  intro h1
  intro h2
  exfalso
  apply h1
  exact h2
  sorry

example : (True → False) → P := by
  intro h1
  exfalso
  apply h1
  trivial

/- END TODO -/

/- TODO -/

example : ¬False → True := by
  intro h1
  by_contra h2
  apply h2
  trivial

example : P → ¬¬P := by
  change P → ¬ P → False
  change P → (P → False) → False
  intro h1 h2
  apply h2
  exact h1

example : False → ¬P := by
  intro h1
  exfalso
  exact h1

example : P → ¬P → False := by
  intro h1 h2
  change P → False at h2
  apply h2
  exact h1

example : ¬¬False → False := by
  intro h1
  apply h1
  intro h2
  exfalso
  exact h2

example : (¬Q → ¬P) → P → Q := by
  intro h1
  intro hP
  by_contra h2
  have h3 := h1 h2
  apply h3
  exact hP

/- END TODO -/

/- TODO -/

example : P ∧ Q → Q := by
  intro H
  cases H with
  | intro left right => exact right

example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  cases h2 with
  | intro left right => --we need to write | explicitly
  apply h1 --?
  exact left
  exact right

-- `∧` is symmetric
lemma lemma2 : P ∧ Q → Q ∧ P := by
  intro h1
  constructor
  · cases h1 with
  | intro left right => exact right
  · cases h1 with
  | intro left right => exact left

-- `∧` is transitive
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  constructor
  · cases h1 with
  | intro left right => exact left
  · cases h2 with
  | intro left right => exact right

example : P → P ∧ True := by
  intro h1
  constructor
  · exact h1
  · trivial

example : False → P ∧ False := by
  intro h1
  exfalso
  exact h1

example : (P ∧ Q → R) → P → Q → R := by
  intro h1 h2 h3
  apply h1
  constructor
  · exact h2
  · exact h3
/- END TODO -/

/- TODO -/

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  constructor
  --here we can avoid using cases. Because we can just "apply h2.mp" or "apply h2.mpr" and lean understands without having to divide first
  · cases h1 with
  | intro mp mpr => 
    intro h3 
    cases h2 with
    | intro mp1 mpr1 => 
      apply mp1
      apply mp
      exact h3
  · cases h2 with
  | intro mp mpr => 
    intro hR
    cases h1 with
    | intro mp1 mpr1 => 
      apply mpr1
      apply mpr
      exact hR

--example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  --intro h1 h2
  --constructor
  --· intro hP
  --  exact (smth like) h1.mpr (h2.mpr hR) (see h1.mpr as a function, applied to the functon h2.mpr applied to hR)

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · exact lemma2 P Q
  · exact lemma2 Q P

lemma lemma3 : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  --refine ⟨fun h1 ↦ ⟨ h1.1.1,⟨ h1.1.2, h1.2⟩⟩ , fun h2 ↦ ⟨⟨ h2.1, h2.2.1⟩,h2.2.2⟩ ⟩  
  --"refine" is like "exact" but you can see the context. h1.1.1 means take h1 ((P∧ Q) ∧ R), its first term, and then the first term (so P).
  --"fun" introduces a function from h(smt) to another stuff. The angle brackets is used to write tuples, ⟨a,b⟩ is the tuple a∧b (yeah it's a tuple)
  constructor
  · intro h1
    constructor
    · cases h1 with
    | intro left  => 
      cases left with
      | intro left => 
      exact left
    · cases h1 with
    | intro left right => 
      cases left with
      | intro left1 right1 => 
      constructor
      · exact right1
      · exact right
  · intro h1
    cases h1 with
    | intro left right => 
      constructor
      · constructor
        · exact left
        · cases right with
        | intro left => exact left
      · cases right with
      | intro _ right => exact right

example : P ↔ P ∧ True := by
  constructor
  · intro h1
    constructor
    · exact h1
    · trivial
  · intro h1
    cases h1 with
    | intro left right => exact left

example : False ↔ P ∧ False := by
  constructor
  · intro h1
    exfalso
    exact h1
  · intro h1
    cases h1 with
    | intro left right => exact right

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  constructor
  · intro h3
    constructor
    · cases h3 with
    | intro left => 
      cases h1 with
      | intro mp mpr => 
        apply mp
        exact left
    · cases h2 with
    | intro mp mpr => 
      cases h3 with
      | intro left right => 
        apply mp
        exact right
  · intro h3
    constructor
    · cases h3 with
    | intro left => 
      cases h1 with
      | intro mp mpr => 
        apply mpr
        exact left
    · cases h2 with
    | intro mp mpr => 
      cases h3 with
      | intro left right => 
        apply mpr
        exact right

example : ¬(P ↔ ¬P) := by
  intro h1
  cases h1 with
  | intro mp mpr => 
    by_cases hP : P --"this tactic doesn't work if we don't have classical logic", bc terzo escluso
    · have h2 := mp hP
      apply h2
      exact hP
    · have h2 := mpr hP
      apply hP
      exact h2
  

/- END TODO -/

/- TODO -/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1 h2 h3
  cases h1 with
  | inl h => 
    apply h2
    exact h
  | inr h => 
    apply h1
    exact h

-- associativity of `∨`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro h1
    cases h1 with
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
  · intro h1
    cases h1 with
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
  intro h1 h2
  cases h2 with
  | inl h => 
    left
    apply h1
    exact h
  | inr h => 
    right
    exact h

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  constructor
  · intro h3
    cases h3 with
    | inl h => 
      left
      apply h1.mp
      exact h
    | inr h => 
      right
      apply h2.mp
      exact h
  · intro h3
    cases h3 with
    | inl h => 
      left
      apply h1.mpr
      exact h
    | inr h => 
      right
      exact h2.mpr h --function h2.mpr applied to h

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h1
    constructor
    · intro hP
      have h2 : P ∨ Q := by --!!!!!!! have is much more than what we had seen last time. Here have is used to prove P ∨ Q, as if it were another separate example
        left
        exact hP
      exact h1 h2
    · intro hQ 
      apply h1 
      right 
      exact hQ
  · intro h h1 
    cases h1 with
    | inl h1 => apply h.left; exact h1 
    | inr h1 => apply h.right; exact h1

/- END TODO -/
