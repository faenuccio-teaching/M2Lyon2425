import Mathlib

variable {α : Type*} (f : α → α → Prop)

@[simp]
def iteration (n : ℕ) : α → α → Prop :=
  match n with
  | 0 => (· = ·)
  | m+1 => fun x y ↦ (∃ w, (iteration m) x w ∧ f w y)

lemma equiv_defs :
  ∀ n, ∀ x y,
  iteration f n x y →
  ∃ (w : ℕ → α), -- `w` est définie sur ℕ, mais on ne s'intéresse qu'à ses `n` premières valeurs
    (w 0 = x ∧ w n = y) ∧ -- on veut forcer des conditions sur les valeurs en 0 et en `n`
    (∀ i,
      n < i+1 ∨ -- et la condition ne s'applique que si `i < n`, donc pas si `n < i+1`
      f (w i) (w (i+1))) := by

    intro n
    induction n with
    | zero => sorry -- le problème n'est pas ici, cette partie est "facile", d'où le `sorry`
    | succ m hm =>
      intro x y hite
      simp at hite
      let w_der := hite.choose
      have ⟨hw_der_prev, hw_der_suiv⟩ := hite.choose_spec
      have := hm x w_der hw_der_prev
      let w := this.choose
      have hw := this.choose_spec
      -- on construit ici une fonction `w'` qui étend `w`
      let w' := fun i ↦ (if i = m+1 then y else w i)
      use w'
      simp
      constructor
      · -- on sait que `w' 0 = w 0` car 0 n'est pas un successeur (cf def. de `w'`)
        -- mais comment le montrer ?
        constructor
        · have h0 : 0 ≠ m+1 := by omega
          simp only [h0, w', reduceIte]
          exact hw.left.left
        · sorry
      · sorry -- le même problème apparait, à résoudre similairement

def w : ℕ → ℕ := sorry
def w₁ := fun i ↦ if i = 10 then 0 else w i
#check w₁

def NatHom (h : ℕ → ℕ) : Prop := ∀ x y, h x * h y = h (x*y)

lemma existsNatHom : ∃ h : ℕ → ℕ, NatHom h := by
  use (·)
  intro x y
  rfl

lemma exemple (h : ℕ → ℕ) :
  ∃ (g : ℕ → ℕ), ∀ i, ((i≠ 10 ∧ g i = h i) ∨ (i = 10 ∧ g i = 0)) := by
    let g := fun i ↦ if i = 10 then 0 else h i
    use g
    intro i
    by_cases hi : i = 10
    · right
      constructor
      · exact hi
      · simp only [hi, reduceIte, g]
    · left
      constructor
      · exact hi
      · simp only [hi, reduceIte, g]
