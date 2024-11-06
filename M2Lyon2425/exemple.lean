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
      let w' := fun i ↦ (match i with
        | m+1 => y
        | _ => w i
        )
      use w'
      simp
      constructor
      · -- on sait que `w' 0 = w 0` car 0 n'est pas un successeur (cf def. de `w'`)
        -- mais comment le montrer ?
        calc
          w' 0 = w 0 := sorry
          _ = x := hw.left.left
      · sorry -- le même problème apparait, à résoudre similairement
