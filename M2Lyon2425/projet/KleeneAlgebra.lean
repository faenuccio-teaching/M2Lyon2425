import Mathlib.Algebra.Order.Kleene


/- Dans cette section, on établit quelques propriétés de élémentaires
des algèbres de Kleene. Beaucoup sont déjà prouvées
dans Mathlib/Algebra/Order/Kleene. Les preuves sont longues car j'ai tenté
d'être complet et d'expliciter les lemmes et résultats intermédiaires utilisés.

Le résultat le plus important est `KleeneChurchRosser`, le dernier de ce fichier. -/

open Computability

variable {K : Type*} [KleeneAlgebra K]

lemma add_respects_le {a₁ b₁ a₂ b₂ : K}
  (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) : a₁ + a₂ ≤ b₁ + b₂ := by
    rw [← add_eq_right_iff_le] at h₁ h₂ ⊢
    rw [
      add_assoc,
      add_comm a₂,
      ← add_assoc,
      ← add_assoc,
      h₁,
      add_assoc,
      add_comm b₂,
      h₂
    ]

lemma mul_respects_le {a₁ b₁ a₂ b₂ : K}
  (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) : a₁ * a₂ ≤ b₁ * b₂ := by
    rw [← add_eq_right_iff_le] at h₁ h₂
    have calcul : (a₁ + b₁) * (a₂ + b₂) = b₁ * b₂ := by rw [h₁, h₂]
    rw [
      left_distrib,
      right_distrib,
      right_distrib,
      ← add_assoc,
      add_eq_right_iff_le,
      add_assoc
    ] at calcul
    exact (add_le_iff.mp calcul).1

lemma topown_mono (n : ℕ) {f g : K} : f ≤ g → f^n ≤ g^n := by
  intro lefg
  induction n with
  | zero => simp only [pow_zero, le_refl]
  | succ m hm =>
    rw [pow_succ, pow_succ]
    exact mul_respects_le hm lefg

lemma unfold_left (a : K) : 1 + a∗ * a ≤ a∗ := by
    nth_rw 2 [← add_idem a∗]
    exact add_respects_le
      (KleeneAlgebra.one_le_kstar a)
      (KleeneAlgebra.kstar_mul_le_kstar a)

lemma unfold_right (a : K) : 1 + a * a∗ ≤ a∗ := by
    nth_rw 2 [← add_idem a∗]
    exact add_respects_le
      (KleeneAlgebra.one_le_kstar a)
      (KleeneAlgebra.mul_kstar_le_kstar a)

lemma induction_left {a b c : K} : b + a * c ≤ c → a∗ * b ≤ c := by
  intro hyp
  rw [add_le_iff] at hyp
  exact kstar_mul_le hyp.left hyp.right

lemma induction_right {a b c : K} : b + c * a ≤ c → b * a∗ ≤ c := by
  intro hyp
  rw [add_le_iff] at hyp
  exact mul_kstar_le hyp.left hyp.right

lemma le_add_left' {a b : K} : a ≤ a + b := by
  rw [← add_eq_right_iff_le, ← add_assoc, add_idem]

lemma le_add_right' {a b : K} : b ≤ a + b := by
  rw [← add_eq_right_iff_le, add_comm, add_assoc, add_idem]

lemma add_kstar {a b : K} : (a + b)∗ = a∗ * (b * a∗)∗ := by
  refine le_antisymm ?_ ?_
  · rw [← mul_one (a+b)∗]
    refine induction_left ?_
    · refine add_le_iff.mpr ?_
      · constructor
        · rw [← mul_one 1]
          exact mul_respects_le one_le_kstar one_le_kstar
        · rw [right_distrib]
          refine add_le_iff.mpr ?_
          · constructor
            · rw [← mul_assoc]
              exact mul_respects_le (mul_kstar_le_kstar) (by simp only [le_refl])
            · rw [← mul_assoc]
              nth_rw 1 [← one_mul b]
              rw [mul_assoc, mul_assoc, ← mul_assoc b]
              exact mul_respects_le one_le_kstar mul_kstar_le_kstar
  · refine induction_right ?_
    · refine add_le_iff.mpr ?_
      · constructor
        · refine kstar_mono ?_
          rw [
            ← add_eq_right_iff_le,
            ← add_assoc,
            add_idem
          ]
        · calc
            (a + b)∗ * (b * a∗)
              ≤ (a + b)∗ * ((a + b) * a∗ ):= ?_
            _ ≤ (a + b)∗ * (a + b) * a∗ := by rw [mul_assoc]
            _ ≤ (a + b)∗ * (a + b)∗  * a∗ :=  ?_
            _ ≤ (a + b)∗ * (a + b)∗  * (a + b)∗ := ?_
            _ = (a+b)∗ := by repeat rw [kstar_mul_kstar]
          · exact mul_respects_le
              (le_refl (a + b)∗)
              (mul_respects_le
                (le_add_right')
                (le_refl a∗))
          · exact mul_respects_le
              (mul_respects_le
                (le_refl (a + b)∗ )
                le_kstar)
              (le_refl a∗)
          · exact mul_respects_le
              (le_refl ((a + b)∗ * (a + b)∗))
              (kstar_mono le_add_left')

lemma mul_kstar_le_kstar_revmul_kstar {a b : K} :
  b * a∗ ≤ a∗ * b∗ → (a + b)∗ ≤ a∗ * b∗ := by
    intro hyp
    have h₀ : a ≤ a∗ := le_kstar
    have h₁ : a∗ * b∗ ≤ a∗ * b∗ := le_refl (a∗ * b∗)
    have h₂ : a * (a∗ * b∗) ≤ a∗ * (a∗ * b∗) := mul_respects_le (h₀) (h₁)
    rw [← mul_assoc, ← mul_assoc, kstar_mul_kstar, mul_assoc] at h₂
    have h₃ : b∗ ≤ b∗ := le_refl b∗
    have h₄ : b * a∗ * b∗ ≤ a∗ * b∗ * b∗ := mul_respects_le hyp h₃
    rw [mul_assoc, mul_assoc, kstar_mul_kstar] at h₄
    have h₅ := add_respects_le h₂ h₄
    rw [← right_distrib, add_idem] at h₅
    have h₆ : 1 ≤ a∗ := one_le_kstar
    have h₇ : 1 ≤ b∗ := one_le_kstar
    have h₈ := mul_respects_le h₆ h₇
    rw [one_mul] at h₈
    have h₉ := add_respects_le h₈ h₅
    rw [add_idem] at h₉
    have h₁₀ := induction_left h₉
    rw [mul_one] at h₁₀
    exact h₁₀

lemma kstar_mul_kstar_le_kstar_revmul_kstar {a b : K} :
  b∗ * a∗ ≤ a∗ * b∗ → (a + b)∗ ≤ a∗ * b∗ := by
    intro hyp
    refine mul_kstar_le_kstar_revmul_kstar ?_
    · have h₀ : b ≤ b∗ := le_kstar
      rw [← add_eq_right_iff_le] at h₀
      nth_rw 1 [← h₀] at hyp
      rw [right_distrib, add_le_iff] at hyp
      exact hyp.left

theorem KleeneChurchRosser {a b : K} :
  b∗ * a∗ ≤ a∗ * b∗ ↔ (a + b)∗ ≤ a∗ * b∗ := by
    constructor
    · intro hyp
      exact kstar_mul_kstar_le_kstar_revmul_kstar hyp
    · intro hyp
      nth_rw 1 [← mul_one a]
      refine le_trans ?_ hyp
      rw [add_comm, add_kstar]
      refine mul_respects_le
        (le_refl b∗)
        (kstar_mono
          (mul_respects_le
            (le_refl a)
            (one_le_kstar)))
