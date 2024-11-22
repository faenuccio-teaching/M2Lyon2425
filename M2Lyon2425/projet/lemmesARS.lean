import «M2Lyon2425».projet.ARSinstKleene

variable {α : Type*}

namespace ARS

lemma le_iff_imp {f g : ARS α} : f ≤ g ↔ ∀ x y, f x y → g x y := by
  constructor
  · intro hyp x y hfxy
    rw [← add_eq_right_iff_le] at hyp
    rw [← hyp]
    left
    exact hfxy
  · intro hyp
    ext x y
    constructor
    · intro ou
      cases ou with
      | inl fxy =>
        exact hyp x y fxy
      | inr gxy =>
        exact gxy
    · intro hgxy
      right
      exact hgxy

/-

Partie correcte, mais inutilisée

@[reducible]
def indexed_op (ι β : Type*) := ι → ARS β

@[reducible]
def big_sum {ι : Type*} (t : indexed_op ι α) : ARS α :=
  fun x y ↦ ∃ i, t i x y

def big_sum_respects_le {ι : Type*} {g : ARS α} (t : indexed_op ι α) :
  (∀ i, t i ≤ g) → big_sum t ≤ g := by
    intro htflef
    rw [le_iff_imp]
    intro x y hbigsum
    exact le_iff_imp.mp (htflef hbigsum.choose) x y hbigsum.choose_spec

def big_sum_comm_from_comm {ι : Type*} {f : ARS α} (t : indexed_op ι α) :
  (∀ i, t i * f = f * t i) → big_sum t * f = f * big_sum t := by
    intro hypcomm
    ext x y
    constructor
    · intro hyp
      let z1 := hyp.choose
      let ⟨hz1bs, hz1f⟩ := hyp.choose_spec
      let i := hz1bs.choose
      have hi := hz1bs.choose_spec
      have hypcommi := (hypcomm i)
      have h₀ : ((t i * f) x y ↔ (f * t i) x y) :=  by rw [hypcommi]
      have h₁ : (t i * f) x y := by use z1
      have h₃ := h₀.mp h₁
      let z2 := h₃.choose
      have ⟨hz2f, hz2bs⟩ := h₃.choose_spec
      use z2
      constructor
      · exact hz2f
      · use i
    · intro hyp
      let z1 := hyp.choose
      let ⟨hz1f, hz1bs⟩ := hyp.choose_spec
      let i := hz1bs.choose
      have hi := hz1bs.choose_spec
      have hypcommi := (hypcomm i)
      have h₀ : ((t i * f) x y ↔ (f * t i) x y) :=  by rw [hypcommi]
      have h₁ : (f * t i) x y := by use z1
      have h₃ := h₀.mpr h₁
      let z2 := h₃.choose
      have ⟨hz2bs, hz2f⟩ := h₃.choose_spec
      use z2
      constructor
      · use i
      · exact hz2f

/-- Le fait que `∃ i, ∃ w, ⋯` est la même chose que `∃ w, ∃ i, ⋯`
On pourrait aller plus loin et faire une distributivité d'une
big sum sur une autre, mais c'est plus que le nécessaire.
-/
def big_sum_distrib_left {ι : Type*} {f: ARS α} {t : indexed_op ι α} :
  f * big_sum t = big_sum (fun i ↦ f * t i)
    := by
      ext x y
      constructor
      · intro hyp
        let w := hyp.choose
        have ⟨hwf, hwbs⟩ := hyp.choose_spec
        let i := hwbs.choose
        have hi := hwbs.choose_spec
        use i
        simp only
        use w
      · intro hyp
        let i := hyp.choose
        have hi := hyp.choose_spec
        simp only at hi
        let w := hi.choose
        have ⟨hwf, hwbs⟩ := hi.choose_spec
        use w
        constructor
        · exact hwf
        · use i

/-- Le choix d'avoir des fonctions dans ℕ plutôt que Fin (n+1) est arbitraire.-/
def existsChaine (f :ARS α) (n : ℕ) (x y : α) :=
  ∃ w : ℕ → α, (w 0 = x ∧ w n = y) ∧ (∀ i, n < i+1 ∨ f (w i) (w (i+1)))

/-- Une description alternative de f^n
On remarque que l'ordre de quantification est important,
si on commence par `∀ x y, ∀ n, ⋯`, il n'est pas possible
de faire une induction sur `n` en gardant `x` et `y` généraux.-/
lemma npow' {f : ARS α} :
  ∀ n : ℕ, ∀ x y : α,
  (f^n) x y →
  existsChaine f n x y := by
    intro n
    induction n with
    | zero =>
      intro x y hypf0
      use (fun _ ↦ x)
      simp only [pow_zero] at hypf0
      constructor
      · constructor <;> rw [hypf0]
      · intro i
        left
        omega
    | succ m hm =>
      intro x y' hypfn
      rw [pow_succ] at hypfn
      let wn := hypfn.choose
      have ⟨hfmwn, hfwn⟩ := hypfn.choose_spec
      let w := (hm x wn hfmwn).choose
      have ⟨⟨hw0, hwm⟩, hwf⟩ := (hm x wn hfmwn).choose_spec
      let w' :=  fun (i: ℕ) ↦ if i = m+1 then y' else w i
      use w'
      constructor
      · constructor
        · simp only [w', reduceIte]
          exact hw0
        · simp only [w', reduceIte]
      · intro i' -- on va faire une *trichotomie* sur i'>m, i'=m, i'< m
        by_cases hi₁ : m+1 < i'+1
        · left; exact hi₁
        · right
          simp only [add_lt_add_iff_right, not_lt] at hi₁
          by_cases hi₂ : i' = m
          · have hi₃ : m ≠ m+1 := by omega
            simp only [w', hi₂, hi₃, reduceIte, w, hwm, hfwn]
          · have hi₃ : i' ≠ m +1 := by omega
            have hi₄ : i'+1 ≠ m+1 := by omega
            simp only [w', hi₃, hi₄, reduceIte]
            cases hwf i' with
            | inl hi => exfalso; omega
            | inr hw' => exact hw'

-/

end ARS
