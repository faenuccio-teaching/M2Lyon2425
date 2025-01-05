/- Résultats inutilisés. Je voulais l'utiliser à l'origine pour
la preuve de l'induction noetherienne. -/
import Mathlib

/- On (re)définit une fonction `minSet {A : Set ℕ} : A.Nonempty → ℕ`
et on prouve que cette fonction coincide bien avec le minimum de `A`.
En passant, on définit la fonction auxilliaire
`minSetAux {a : ℕ} {A : Set ℕ} (n : ℕ) : (a ∈ A ∧ n ≤ a) → ℕ`
qui facilite les preuves voulues. -/

/-- Étant donné `A : Set ℕ`, `a ∈ A`, `n ∉ A`, on a
l'implication `n ≤ a → n+1 ≤ a`. -/
lemma lAux₃ (A : Set ℕ) (a : ℕ) (ha : a ∈ A) (n : ℕ) (hn : n ∉ A) :
  n ≤ a → n+1 ≤ a := by
    intro h
    have : n = a ∨ n+1 ≤ a := by omega
    cases this with
    | inl h₂ =>
      exfalso
      rw [h₂] at hn
      exact hn ha
    | inr h₂ =>
      exact h₂


/-- Calcule le plus petit entier de `A : Set ℕ` supérieur à `n : ℕ`,
étant donnée l'existence d'un élément `a : ℕ` dans A et supérieur à n -/
private noncomputable def minSetAux {a : ℕ} {A : Set ℕ} (n : ℕ) :
  a ∈ A ∧ n ≤ a → ℕ := by
  intro ha
  by_cases h₁ : n ∈ A
  · exact n
  · have ⟨haA, han⟩ := ha
    have : a ∈ A ∧ n+1 ≤ a := by
      constructor
      · exact haA
      · have : n = a ∨ n+1 ≤ a := by omega
        cases this with
        | inl h₂ =>
          exfalso
          rw [h₂] at h₁
          exact h₁ haA
        | inr h => exact h
    exact minSetAux (n+1) this
termination_by a - n

lemma minSetAux_in_A {a : ℕ} (A : Set ℕ) (n : ℕ) (ha : a ∈ A ∧ n ≤ a) :
  minSetAux n ha ∈ A := by
    rw [minSetAux]
    split
    · case isTrue h => exact h
    · case isFalse h =>
        simp
        have : a ∈ A ∧ n+1 ≤ a := ⟨ha.left, by
          have : n = a ∨ n+1 ≤ a := by omega
          cases this with
          | inl hl => exfalso; rw [hl] at h; exact h ha.left
          | inr hr => exact hr
        ⟩
        split
        · exact minSetAux_in_A A (n+1) this

lemma minSetAuxIncr {a : ℕ} (A : Set ℕ) (n : ℕ) (ha : a ∈ A ∧ n ≤ a) :
  n ≤ minSetAux n ha ∧ minSetAux n ha ≤ a := by
    constructor
    · unfold minSetAux
      simp
      by_cases hn : n ∈ A
      · simp only [hn, reduceDIte, le_refl]
      · simp only [hn, reduceDIte]
        have ha_succ : n + 1 ≤ a := by
          have : n = a ∨ n+1 ≤ a := by omega
          cases this with
          | inl h₂ =>
            exfalso
            rw [←h₂] at ha
            exact hn ha.left
          | inr h => exact h
        have := (minSetAuxIncr A (n + 1) ⟨ha.left, ha_succ⟩).left
        split
        omega
    · unfold minSetAux
      by_cases hn : n ∈ A
      · simp only [hn, reduceDIte]
        exact ha.right
      · simp only [hn, reduceDIte]
        have ha_succ : n + 1 ≤ a := by
          have : n = a ∨ n+1 ≤ a := by omega
          cases this with
          | inl h₂ =>
            exfalso
            rw [←h₂] at ha
            exact hn ha.left
          | inr h => exact h
        have := (minSetAuxIncr A (n+1) ⟨ha.left, ha_succ⟩).right
        split
        exact this
termination_by a - n

lemma minSetAuxStable (A : Set ℕ) (n a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hn : n ≤ a ∧ n ≤ b) :
  minSetAux n ⟨ha, hn.left⟩ = minSetAux n ⟨hb, hn.right⟩ := by
    rw [minSetAux, minSetAux]
    simp only
    split
    · rfl
    · case isFalse h =>
      exact minSetAuxStable
        A
        (n+1)
        a
        b
        ha
        hb
        ⟨lAux₃ A a ha n h hn.left, lAux₃ A b hb n h hn.right⟩
termination_by a - n
decreasing_by
  simp only [InvImage]
  case _ h₁  =>
  have : n < a := by
    have := lAux₃ A a ha n h₁ hn.left
    omega
  have : a - (n + 1) < a - n := by omega
  exact this

lemma minSetAuxIncr₂ {a : ℕ} (A : Set ℕ) (ha : a ∈ A) (n m : ℕ) (hn : n ≤ a) (hm : m ≤ a) :
  n ≤ m → minSetAux n ⟨ha, hn⟩ ≤ minSetAux m ⟨ha, hm⟩ := by
    intro hnm
    unfold minSetAux
    simp
    split
    · case isTrue h₁ =>
      split
      · case isTrue h₂ =>
        exact hnm
      · case isFalse h₂ =>
        have h₃ := (minSetAuxIncr A (m+1) ⟨ha, lAux₃ A a ha m h₂ hm⟩).left
        have h₄ : m ≤ m + 1 := by omega
        exact Nat.le_trans (Nat.le_trans hnm h₄) h₃
    · case isFalse h₁ =>
      split
      · case isTrue h₂ =>
        have := minSetAuxStable
          A
          (n+1)
          a
          m
          ha
          h₂
          ⟨lAux₃ A a ha n h₁ hn, lAux₃ A m h₂ n h₁ hnm⟩
        rw [this]
        exact (minSetAuxIncr A (n+1) ⟨h₂, lAux₃ A m h₂ n h₁ hnm⟩).right
      · case isFalse h₂ =>
        exact minSetAuxIncr₂ -- j'ai coupé la ligne, c'est plus agréable à lire
          A
          ha
          (n+1)
          (m+1)
          (lAux₃ A a ha n h₁ hn)
          (lAux₃ A a ha m h₂ hm)
          (by omega)
termination_by (a - n)
decreasing_by
  simp only [InvImage]
  case _ h₁ h₂  =>
  have : n < a := by
    have := lAux₃ A a ha n h₁ hn
    omega
  have : a - (n + 1) < a - n := by omega
  exact this

noncomputable def minSet {A : Set ℕ} (hA : A.Nonempty) : ℕ := by
  exact minSetAux 0 ⟨hA.choose_spec, by omega⟩

lemma minSet_in_A {A : Set ℕ} (hA : A.Nonempty) : minSet hA ∈ A := by
  exact minSetAux_in_A A 0 ⟨hA.choose_spec, by omega⟩

lemma minSetAux_is_min {a : ℕ} {A : Set ℕ} (n : ℕ) (ha : a ∈ A ∧ n ≤ a) :
  n < minSetAux n ha →  ¬ n ∈ A := by
    intro h₁ h₂
    rw [minSetAux] at h₁
    simp only [h₂, reduceDIte, lt_self_iff_false] at h₁

lemma minSet_is_min {A : Set ℕ} (hA : A.Nonempty) :
  ∀ n, n ∈ A → minSet hA ≤ n := by
    have ha : hA.choose ∈ A ∧ 0 ≤ hA.choose := ⟨hA.choose_spec, by omega⟩
    let a := hA.choose
    intro n h₁
    rw [minSet]
    by_contra hm
    simp at hm
    by_cases h : n ≤ a
    · have ineq₁ := minSetAuxIncr₂ A hA.choose_spec 0 n (by omega) h (by omega)
      have ineq₂ : n < minSetAux n ⟨hA.choose_spec, h⟩ := by omega
      exact minSetAux_is_min n ⟨hA.choose_spec, h⟩ ineq₂ h₁
    · have ineq₁ : a < minSetAux 0 ha := by omega
      have ineq₂ := (minSetAuxIncr A 0 ha).right
      omega
