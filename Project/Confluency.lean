import Mathlib.Tactic.Common

import «Project».AbstractRewritingSystem
import «Project».Definition

/-!
# Confluency of the untyped λ-calculus

This file shows that the β-reduction defined in the file `Definition` is a confluent
abstract rewriting system.
The proof of this file follows the standard proof that uses parallel β-reduction. It follows
the steps of [Mim22, §3.4].

## References

* [S. Mimram. PROGRAM=PROOF. 2022][Mim22] 
In this file, the proofs follow the book very closely. -/


/-!
## Parallel β-reduction 

Parallel β-reduction is denoted ⇉ and define with the following rules:
  - if x is a variable, then x ⇉ x
  - if M ⇉ M' and N ⇉ N', then (λx. M) N ⇉ M'[N'/x]
  - if M ⇉ M' and N ⇉ N', then M N ⇉ M' N'
  - if M ⇉ M', then λx. M ⇉ λx. M'.
-/
inductive Pβreduction : Λ → Λ → Prop :=
  | βx : ∀ x, Pβreduction (Lambda.Var x) (Lambda.Var x)
  | βs : ∀ M M' N N', Pβreduction M M' → Pβreduction N N' 
           → Pβreduction (Lambda.App (Lambda.Lam M) N) (M'[N'⧸0])
  | βa : ∀ M M' N N', Pβreduction M M' → Pβreduction N N'
           → Pβreduction (Lambda.App M N) (Lambda.App M' N')
  | βl : ∀ M M', Pβreduction M M' → Pβreduction (Lambda.Lam M) (Lambda.Lam M')

infixl:75 " ⇉ " => Pβreduction
infixl:75 " ⇉⋆ " => Pβreduction⋆

/-- Parallel β-reduction is reflexive. -/
lemma is_refl_parallel : ∀ M, M ⇉ M := by
  intro M; induction' M with x M ih M N ihM ihN
  · constructor
  · constructor; trivial
  · constructor <;> trivial

/-! ### ⇉⋆ coincides with →β⋆ -/

/-- β-reduction is included in parallel β-reduction -/
lemma beta_reduction_is_parallel_beta_reduction : βreduction ⊂ Pβreduction := by
  intro M N h; induction h with
  | β M N => constructor <;> apply is_refl_parallel
  | context₀ M N _ ih => constructor; trivial
  | context₁ M N P _ ih => constructor; apply is_refl_parallel; trivial
  | context₂ M N P _ ih => constructor; trivial; apply is_refl_parallel

/-- On the other hand, one step of parallel β-reduction is included in →β⋆ -/
lemma parallel_beta_reduction_is_trans_refl_beta_reduction : Pβreduction ⊂ βreduction⋆ := by
  intros M N h; induction h with
  | βx x => right; rfl
  | βs M M' N N' _ _ ihM ihN => 
    have h₀ : (Lambda.App (Lambda.Lam M) N) →β⋆ (Lambda.App (Lambda.Lam M') N') := by
      have h₀ : (Lambda.Lam M) →β⋆ (Lambda.Lam M') := by 
        apply context₀_trans_refl; trivial
      have h₁ : (Lambda.App (Lambda.Lam M) N) →β⋆ (Lambda.App (Lambda.Lam M') N) := by
        apply context₂_trans_refl; trivial
      have h₂ : (Lambda.App (Lambda.Lam M') N) →β⋆ (Lambda.App (Lambda.Lam M') N') := by
        apply context₁_trans_refl; trivial
      exact h₁ ∙⋆ h₂
    have h₁ : (Lambda.App (Lambda.Lam M') N') →β⋆ M'[N'⧸0] := by
      left; left; constructor
    exact h₀ ∙⋆ h₁
  | βa M M' N N' _ _ ihM ihN =>
    have h₀ : (Lambda.App M N) →β⋆ (Lambda.App M N') := by
      apply context₁_trans_refl; trivial
    have h₁ : (Lambda.App M N') →β⋆ (Lambda.App M' N') := by
      apply context₂_trans_refl; trivial
    exact h₀ ∙⋆ h₁
  | βl M M' _ ih => apply context₀_trans_refl; trivial

/-- Hence, the transitive closure of the two relations is equal. -/
lemma transitive_closure_parallel_coincides : (Pβreduction⋆ = βreduction⋆) := by
  have h₀ : Pβreduction⋆ ⊂ βreduction⋆ := by 
    rw [←(@refl_trans_closure_is_idempotent Λ βreduction)]
    apply is_subrelation_refl_trans_closure
    exact parallel_beta_reduction_is_trans_refl_beta_reduction
  have h₁ : βreduction⋆ ⊂ Pβreduction⋆ := by
    apply is_subrelation_refl_trans_closure
    exact beta_reduction_is_parallel_beta_reduction
  ext x y; constructor <;> intro h
  · apply h₀; trivial
  · apply h₁; trivial

/-! ### ⇉⋆ has the diamond property -/

/-- First, we show that lifting is compatible with the parallel β-reduction. --/
lemma parallel_reduction_compatible_lift :
  ∀ (i j : ℕ) (M N : Λ), M ⇉ N → lift i j M ⇉ lift i j N := by
  intro i j M N h; revert j i; induction h with
  | βx x => intro i j; apply is_refl_parallel
  | βs M M' P P' _ _ ihM ihP =>
    intro i j
    change Lambda.App (Lambda.Lam (lift i (j + 1) M)) (lift i j P) ⇉ lift i j (M'[P'⧸0])
    have : Lambda.App (Lambda.Lam (lift i (j + 1) M)) (lift i j P) 
             ⇉ (lift i (j + 1) M')[lift i j P'⧸0] := by
      constructor; apply ihM; apply ihP
    rw [lift_substitute j i 0] at this; trivial
  | βa P P' M M' _ _ ihP ihM =>
    intro i j; unfold lift
    constructor; apply ihP; apply ihM
  | βl M M' _ ih =>
    intro i j; unfold lift
    constructor; apply ih

/-- Parallel β-reduction is compatible with substitution. --/
lemma parallel_reduction_compatible_subst_aux :
  ∀ (n : ℕ) (M M' N N' : Λ), 
    M ⇉ M' → N ⇉ N' → M[N⧸n] ⇉ M'[N'⧸n] := by
  intro n M M' N N' hM hN; revert n; induction hM with
  | βx x => intro n; unfold substitute; split
            · apply is_refl_parallel
            · split; apply parallel_reduction_compatible_lift; trivial; apply is_refl_parallel
  | βs M M' P P' _ _ ihM ihP =>
    intro n; change Lambda.App (Lambda.Lam (M[N⧸n + 1])) (P[N⧸n]) ⇉ M'[P'⧸0][N'⧸n]
    have h : Lambda.App (Lambda.Lam (M[N⧸n + 1])) (P[N⧸n]) ⇉ M'[N'⧸n + 1][P'[N'⧸n]⧸0] := by
      constructor; apply ihM; apply ihP
    have : P'[N'⧸n] = P'[N'⧸n - 0] := by rw [Nat.sub_zero]
    rw [this, ←substitution_lemma] at h; trivial; omega
  | βa P P' M M' _ _ ihP ihM => intro n; constructor
                                · apply ihP 
                                · apply ihM
  | βl M M' _ ih => intro n; constructor; apply ih

lemma parallel_reduction_compatible_subst :
  ∀ (M M' N N' : Λ), M ⇉ M' → N ⇉ N' → M[N⧸0] ⇉ M'[N'⧸0] :=
  parallel_reduction_compatible_subst_aux 0

/-- Parallel β-reduction has the diamond property. --/
instance : HasDiamond Pβreduction where
  has_diamond := by
    intro M N N' hMN; revert N'; induction hMN with
    | βx x => 
        intro N' hMN'
        use N'; constructor
        · trivial
        · apply is_refl_parallel
    | βs M M' P P' _ _ ihM ihP => 
        intro N' hMN'
        cases hMN' with
        | βs _ M'' _ P'' hM'' hP'' =>
            specialize ihM M'' hM''; specialize ihP P'' hP''
            cases ihM with
            | intro Q h => cases ihP with
              | intro Q' h' => exists Q[Q'⧸0]; constructor
                               · apply parallel_reduction_compatible_subst 
                                 exact h.left; exact h'.left
                               · apply parallel_reduction_compatible_subst
                                 exact h.right; exact h'.right
        | βa Q Q' R R' hQ hP =>
            cases hQ with
            | βl M' M''  hM'' => 
                specialize ihM M'' hM''; specialize ihP R' hP
                cases ihM with
                | intro S h => cases ihP with
                | intro S' h' => exists S[S'⧸0]; constructor
                                 · apply parallel_reduction_compatible_subst
                                   exact h.left; exact h'.left
                                 · constructor; exact h.right; exact h'.right
    | βa P P' M M' hP _ ihP ihM =>
        intro N' hMN'
        cases hMN' with
        | βs P P'' _ M'' hP'' hM'' =>
            cases hP with
            | βl _ P' hP' =>
                specialize ihM M'' hM''; specialize ihP (Lambda.Lam P'')
                have : Lambda.Lam P ⇉ Lambda.Lam P'' := by constructor; trivial
                specialize ihP this; cases ihM with
                | intro R hR => cases ihP with
                  | intro R' hR' => cases hR' with
                    | intro hP' hP'' => cases hP' with
                      | βl _ S hS => cases hP'' with
                        | βl _ S' hS' => exists S[R⧸0]; constructor
                                         · constructor; trivial; exact hR.left
                                         · apply parallel_reduction_compatible_subst; trivial
                                           exact hR.right
        | βa _ P'' _ M'' hP'' hM'' =>
            specialize ihM M'' hM''; specialize ihP P'' hP''
            cases ihM with
            | intro Q hQ => cases ihP with
              | intro Q' hQ' => exists (Lambda.App Q' Q); constructor
                                · constructor; exact hQ'.left; exact hQ.left
                                · constructor; exact hQ'.right; exact hQ.right
    | βl M M' _ ih =>
        intro N' hMN'
        cases hMN' with
        | βl _ M'' hM'' => 
            specialize ih M'' hM''; cases ih with
            | intro P hP => exists (Lambda.Lam P); constructor
                            · constructor; exact hP.left
                            · constructor; exact hP.right

/-! ## Confluency Results -/

/- As every relation that has the diamond property is confluent, we can define a term
   that says that parallel β-reduction has an instance of confluence. -/
def is_confluent_par_beta_reduction := (inferInstance : IsConfluent Pβreduction)

/-- As ⇉⋆ = →β⋆, it directly implies the confluency of →β⋆. -/
instance : IsConfluent βreduction where
  has_diamond := by
    have := is_confluent_par_beta_reduction.has_diamond
    rw [transitive_closure_parallel_coincides] at this
    assumption

def is_confluent_beta_reduction := (inferInstance : IsConfluent βreduction)
def is_church_rosser_beta_reduction := (inferInstance : IsChurchRosser βreduction)

/-! ## Non-triviality Results -/

/-- If 2 λ-terms are β-equivalent and in normal form, then they are equal (by confluency): -/
lemma beta_equivalent_in_normal_form_are_equal :
  ∀ {M N : Λ}, in_normal_form βreduction M → in_normal_form βreduction N → 
    M ≡β N → M = N := by
  intro M N hnormM hnormN hequiv
  have := is_church_rosser_beta_reduction
  have := this.is_church_rosser M N hequiv
  cases this with
  | intro P h =>
    have e₁ : M = P := by
      cases h.left with
      | inl h => exfalso; apply hnormM; cases h with
        | carrier _ _ => use P
        | concat _ M' _ hM' => use M'
      | inr e => trivial
    have e₂ : N = P := by
      cases h.right with
      | inl h => exfalso; apply hnormN; cases h with
        | carrier _ _ => use P
        | concat _ N' _ hN' => use N'
      | inr e => trivial
    rw [e₁, e₂]

/-- That is, β-equivalence is not trivial:
         λxy.x    and    λxy.y
    are 2 λ-terms in normal form that are not β-equivalent. -/
theorem beta_equivalence_is_not_trivial :
  ∃ (M N : Λ), ¬(M ≡β N) := by
  let M := (Lambda.Lam (Lambda.Lam (Lambda.Var 0)))
  let N := (Lambda.Lam (Lambda.Lam (Lambda.Var 1)))
  exists M; exists N
  have h₀ : in_normal_form βreduction M := by
    intro h; cases h with
    | intro P h => unfold_let M at h; contradiction
  have h₁ : in_normal_form βreduction N := by
    intro h; cases h with
    | intro P h => unfold_let N at h; contradiction
  intro h
  have := beta_equivalent_in_normal_form_are_equal h₀ h₁ h
  unfold_let M at this; unfold_let N at this; injection this with e; injection e with e
  injection e with e; contradiction
