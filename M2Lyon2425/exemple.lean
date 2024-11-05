import Mathlib

variable {α : Type*} (f : α → α → Prop)

@[simp]
def iteration (f : α → α → Prop) (n : ℕ) : α → α → Prop :=
  match n with
  | 0 => (· = ·)
  | m+1 => fun x y ↦ (∃ w, (iteration f m) x w ∧ f w y)


lemma equiv_defs :
  ∀ n, ∀ x y,
  iteration f n x y →
  ∃ (w : ℕ → α), (w 0 = x ∧ w n = y) ∧ (∀ i, n < i+1 ∨ f (w i) (w (i+1))) := by
    intro n
    induction n with
    | zero => sorry -- le problème n'est pas ici, cette partie est "facile"
    | succ m hm =>
      intro x y hiter
      simp at hiter
      let w_der := hiter.choose
      have ⟨hw_der_prev, hw_der_suiv⟩ := hiter.choose_spec
      have := hm x w_der hw_der_prev
      let w := this.choose
      have hw := this.choose_spec
      let w' := fun i ↦ (match i with
        | m+1 => y
        | _ => w i
        )
      use w'

      sorry
