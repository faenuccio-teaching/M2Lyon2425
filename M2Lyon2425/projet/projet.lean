-- pas besoin d'`import Mathlib`, qui est déjà importé par les dépendances
import M2Lyon2425.projet.lemmesARSKleene

variable {α : Type*}

open Computability -- pour avoir la notation ∗

/- Sections 2.2 et 2.3 du pdf
On peut désormais facilement et de façon unifiée définir différentes propriétés
et propositions dont les preuves sont aisées. -/

def isWeaklyCommuting (f₁ f₂ : ARS α) : Prop := f₁⇐ * f₂ ≤ f₂∗ * f₁⇐∗

def isCommuting (f₁ f₂ : ARS α) : Prop := f₁⇐ * f₂ ≤ f₂ * f₁⇐

def isDiamond (f : ARS α) : Prop := isCommuting f f

def isChurchRosser (f : ARS α) : Prop := f≡ ≤ f∗ * f⇐∗

def isConfluent (f : ARS α) : Prop := isDiamond f∗

def isWeaklyConfluent (f : ARS α) : Prop := f⇐ * f ≤ f∗ * f⇐∗

/- Le théorème 2.2.5 du pdf, mais via la preuve issu de la partie 2.5 -/
theorem ChurchRosser (f : ARS α) : isConfluent f ↔ isChurchRosser f := by
  rw [isConfluent, isDiamond, isCommuting, isChurchRosser]
  simp only [inv_trans_eq_trans_inv]
  exact KleeneChurchRosser -- ce théorème est le clou du spectacle de KleeneAlgebra.lean

/- La preuve "naïve" du même théorème (incomplète) -/
theorem ChurchRosser' (f : ARS α) :  isConfluent f ↔ isChurchRosser f := by
  rw [isConfluent, isDiamond, isCommuting, isChurchRosser]
  simp only [inv_trans_eq_trans_inv]
  constructor
  · intro hyp
    rw [ARS.le_iff_imp]
    intro x y hEquiv
    sorry -- ici, la preuve est pénible, car il faut faire une induction
  · intro hyp
    rw [ARS.le_iff_imp]
    intro x y hBranching
    rw [ARS.le_iff_imp] at hyp
    have coeur : (f⇐∗ * f∗) ≤ f≡ := by
      refine lubEquiv_contains_mul ?_ ?_
      · simp only [lubEquiv_contains_self, lubEquiv_contains_inverse, lubEquiv_contains_kstar]
      · simp only [lubEquiv_contains_self, lubEquiv_contains_kstar]
    rw [ARS.le_iff_imp] at coeur
    exact hyp x y (coeur x y hBranching)

def isNormalForm (f : ARS α) (a : α) : Prop := ∀ b, ¬(f a b)
