-- pas besoin d'`import Mathlib`, qui est déjà importé par les dépendances
import M2Lyon2425.projet.lemmesARSKleene

variable {α : Type*}

open Computability -- pour avoir la notation ∗

/- Sections 2.2 et 2.3 du pdf
On peut désormais facilement et de façon unifiée définir différentes propriétés
et propositions dont les preuves sont aisées. -/

def isWeaklyCommuting (f₁ f₂ : ARS α) : Prop := f₁⇐ * f₂ ≤ f₂∗ * f₁⇐∗

@[reducible]
def isCommuting (f₁ f₂ : ARS α) : Prop := f₁⇐ * f₂ ≤ f₂ * f₁⇐

@[reducible]
def isDiamond (f : ARS α) : Prop := isCommuting f f

def isChurchRosser (f : ARS α) : Prop := f≡ ≤ f∗ * f⇐∗

@[reducible]
def isConfluent (f : ARS α) : Prop := isDiamond f∗

@[reducible]
def isConfluent' (f : ARS α) : Prop :=
  ∀ a b b', (f∗ a b ∧ f∗ a b' → ∃ c, f∗ b c ∧ f∗ b' c)

/- Équivalence des deux définitions au-dessus -/
lemma confluentEquiv {f : ARS α} : isConfluent f ↔ isConfluent' f := by
  constructor
  · intro hyp a b b' habb'
    rw [isConfluent, isDiamond, isCommuting, ARS.le_iff_imp] at hyp
    have := hyp b b'
    have h₂ : (f∗⇐ * f∗) b b' := by
      use a
    exact this h₂
  · intro hyp
    rw [isConfluent, isDiamond, isCommuting, ARS.le_iff_imp]
    intro x y hfxy
    let w := hfxy.choose
    have hw := hfxy.choose_spec
    exact hyp w x y hw

def isWeaklyConfluent (f : ARS α) : Prop := f⇐ * f ≤ f∗ * f⇐∗

/- Le théorème 2.2.5 du pdf, mais via la preuve issu de la partie 2.5 -/
theorem ChurchRosser {f : ARS α} : isConfluent f ↔ isChurchRosser f := by
  rw [isConfluent, isDiamond, isCommuting, isChurchRosser]
  simp only [inv_trans_eq_trans_inv]
  exact KleeneChurchRosser -- ce théorème est le clou du spectacle de KleeneAlgebra.lean

/- La preuve "naïve" du même théorème (incomplète) -/
theorem ChurchRosser' {f : ARS α} :  isConfluent f ↔ isChurchRosser f := by
  rw [isConfluent, isDiamond, isCommuting, isChurchRosser]
  simp only [inv_trans_eq_trans_inv]
  constructor
  · intro hyp
    rw [ARS.le_iff_imp]
    intro x y hEquiv
    sorry -- ici, la preuve serait pénible, car il faut faire une induction
  · intro hyp
    rw [ARS.le_iff_imp]
    intro x y hBranching
    rw [ARS.le_iff_imp] at hyp
    have coeur : (f⇐∗ * f∗) ≤ f≡ := by
      refine lubEquiv_contains_mul ?_ ?_
      · simp only [
          lubEquiv_contains_self,
          lubEquiv_contains_inverse,
          lubEquiv_contains_kstar
          ]
      · simp only [lubEquiv_contains_self, lubEquiv_contains_kstar]
    rw [ARS.le_iff_imp] at coeur
    exact hyp x y (coeur x y hBranching)

/- Cette définition implique notamment que `f∗` n'admet **aucune** forme normale,
puisque `f∗ a a` est vrai pour tout `a : α`. -/
def isNormalForm (f : ARS α) (a : α) : Prop := ∀ b, ¬(f a b)

@[reducible]
def NFARS (f : ARS α) := Subtype (isNormalForm f)

/- Au sens faible du terme -/
def isNormalizing (f : ARS α) (a : α) : Prop := ∃ b : NFARS f, f∗ a b

def isNormalizingRel (f : ARS α) : Prop := ∀ a, isNormalizing f a

def isInfiniteReductionSequence (f : ARS α) (A : ℕ → α) : Prop := ∀ i, f (A i) (A (i+1))

def isTerminating (f : ARS α) (a : α) : Prop :=
  ¬ (∃ A : ℕ → α, isInfiniteReductionSequence f A ∧ a = A 0)

def isTerminatingRel (f : ARS α) : Prop := ∀ a, isTerminating f a

def isTerminatingRel' (f : ARS α) : Prop := ¬ ∃ A, isInfiniteReductionSequence f A

/- Équivalence des deux définitions au-dessus -/
lemma terminatingRelEquiv {f :ARS α} :
  isTerminatingRel f ↔ isTerminatingRel' f := by
    constructor
    · contrapose
      intro hyp
      rw [isTerminatingRel'] at hyp
      push_neg at hyp
      let A := hyp.choose
      have hA := hyp.choose_spec
      intro h₂
      have h₃ : ∃ B, isInfiniteReductionSequence f B ∧ (A 0) = B 0 := by
        use A
      exact h₂ (A 0) h₃
    · intro hyp
      rw [isTerminatingRel'] at hyp
      push_neg at hyp
      intro a
      rw [isTerminating]
      push_neg
      intro A hfA
      exfalso
      exact (hyp A) hfA

def isConvergent (f : ARS α) : Prop := isConfluent f ∧ isTerminatingRel f

def hasNormalFormProp (f : ARS α) : Prop := ∀ a : α, ∀ b : NFARS f, (f≡) a b → f∗ a b

def hasUniqueNormalFormProp (f : ARS α) : Prop := ∀ a b : NFARS f, (f≡) a b → a = b

def isSemiConvergent (f : ARS α) : Prop := hasUniqueNormalFormProp f ∧ isNormalizingRel f

lemma uniqueExists_NF_of_SemiConvergence (f : ARS α) :
  isSemiConvergent f →
  ∀ a, ∃ b : NFARS f, (f∗ a b.val ∧ ∀ b' : NFARS f, f∗ a b'.val → b = b') := by
    intro hfSC a
    let b := (hfSC.right a).choose
    have hb := (hfSC.right a).choose_spec
    use b
    constructor
    · exact hb
    · intro c hfac
      have hbc : (f≡) b c := by
        let nb := hb.choose
        let hnb := hb.choose_spec
        let nc := hfac.choose
        let hnc := hfac.choose_spec
        use nb+nc
        rw [pow_add]
        use a
        constructor
        · have ineq : f⇐ ≤ f⇔ := by simp only [add_eq_sup, le_sup_right]
          have implication : f⇐ ^ nb ≤ f⇔ ^ nb := topown_mono nb ineq
          have : (f⇐ ^ nb) b.val a := by
            rw [inv_pow_eq_pow_inv, inverse]
            exact hnb
          exact ARS.le_iff_imp.mp implication b.val a this
        · have ineq : f ≤ f⇔ := by simp only [add_eq_sup, le_sup_left]
          have implication : f ^ nc ≤ f⇔ ^ nc := topown_mono nc ineq
          have : (f ^ nc) a c.val := hnc
          exact ARS.le_iff_imp.mp implication a c.val this
      exact hfSC.left b c hbc

def isNFCompatibleFun (f : ARS α) (φ : α → NFARS f) : Prop := ∀ a, f∗ a (φ a)

lemma eq_of_trans_and_NF {f : ARS α} (b : NFARS f) : ∀ w, f∗ b.val w → b.val = w := by
  intro w hyp
  let n := hyp.choose
  have ndef : n = hyp.choose := by trivial
  have hn := hyp.choose_spec
  by_cases h0 : n = 0
  · rw [← ndef, h0, pow_zero] at hn
    exact hn
  · exfalso
    have hpredn := (Nat.exists_eq_succ_of_ne_zero h0).choose_spec
    rw [← ndef, hpredn, ← Nat.add_one, add_comm, pow_add, pow_one] at hn
    exact b.prop hn.choose hn.choose_spec.left

/- Le théorème 2.3.8-i -/
example (f : ARS α) :
  hasNormalFormProp f → hasUniqueNormalFormProp f  :=  by
    intro hfNFProp a b hab
    have hfNFconcl := hfNFProp a b hab
    exact Subtype.ext_val (eq_of_trans_and_NF a b.val hfNFconcl)

/- Le théorème 2.3.8-ii-/
example (f : ARS α) :
  isConfluent f → hasNormalFormProp f := by
    intro hfConf a b hfab
    have := ChurchRosser.mp hfConf
    rw [isChurchRosser, ARS.le_iff_imp] at this
    have := this a b.val hfab
    let w := this.choose
    have hwdef : w = this.choose := by trivial
    have ⟨hwa, hwb⟩ := this.choose_spec
    rw [← hwdef] at hwa hwb
    rw [← inv_trans_eq_trans_inv, inverse] at hwb
    have := (eq_of_trans_and_NF b w hwb)
    rw [← this] at hwa
    exact hwa
