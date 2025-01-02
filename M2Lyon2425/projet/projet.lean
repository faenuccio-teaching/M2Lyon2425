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
    sorry -- ici, la preuve serait pénible, il faudrait faire une induction
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
def NF_of (f : ARS α) := Subtype (isNormalForm f)

/-- Caractérisation, pour `f : ARS α`, des fonctions associant
à tout élément de type `α` une forme normale pour `f`. -/
def isNFCompatibleFun (f : ARS α) (φ : α → NF_of f) : Prop := ∀ a, f∗ a (φ a).val

/-- Sous-type des fonctions donnant *une* forme normale de chaque
élément de type `α`, pour un `f : ARS α`. -/
def NF_fun (f : ARS α) := Subtype (isNFCompatibleFun f)

/-- Normalisation d'un `a : α`, au sens faible du terme, pour un `f : ARS α` -/
def isNormalizing (f : ARS α) (a : α) : Prop := ∃ b : NF_of f, f∗ a b

/-- Normalisation d'un `f : ARS α`-/
def isNormalizingRel (f : ARS α) : Prop := ∀ a, isNormalizing f a

/-- Caractérisation des suites *infinies* de réduction (une étape à la fois) -/
def isInfiniteReductionSequence (f : ARS α) (A : ℕ → α) : Prop := ∀ i, f (A i) (A (i+1))

def InfiniteReductionSequence (f : ARS α) := Subtype (isInfiniteReductionSequence f)

class FiniteReductionSequence (f : ARS α) :=
  carrier : ℕ → α
  longueur : ℕ
  isReductionSequence : ∀ i, f (carrier i) (carrier (i+1)) ∨ longueur ≤ i

def inhab_FiniteReductionSequence [Inhabited α] (f : ARS α) :
  Inhabited (FiniteReductionSequence f) where
   default := {
    carrier := fun _ ↦ Inhabited.default
    longueur := 0
    isReductionSequence := by omega
  }

/- Au sens fort du terme -/
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

structure RedStep (f : ARS α) :=
  a : α
  b : α
  red : f a b

noncomputable def infRedSeq_of_nonemptyNF (f : ARS α) (hE : ¬ Nonempty (NF_of f)) (prems : α) (i : ℕ) :
  RedStep f := by
      have h₁ : ∀ b : α, ∃ c, f b c := by
        intro b
        simp only [nonempty_subtype, not_exists] at hE
        have := hE b
        rw [isNormalForm] at this
        push_neg at this
        exact this
      let a := match i with
      | 0 => prems
      | m+1 => (infRedSeq_of_nonemptyNF f hE prems m).b
      exact {
          a := a
          b := (h₁ a).choose
          red := (h₁ a).choose_spec
      }

noncomputable def RedSeq (f : ARS α) (hE : ¬ Nonempty (NF_of f)) (prems : α) :
  InfiniteReductionSequence f := by
    let T := infRedSeq_of_nonemptyNF f hE prems
    let S := fun i ↦ (T i).a
    have hdefS : ∀ i, S i = (T i).a := by
      intro i
      trivial
    have hdefS' : ∀ i, (T (i+1)).a = (T i).b := by
      intro i
      rfl
    refine ⟨S, ?_⟩
    intro i
    let this := (T i)
    have hSi : S i = this.a := by
      rw [hdefS,]
    have hSip1 : S (i+1) = this.b := by
      rw [hdefS, hdefS']
    rw [hSi, hSip1]
    exact this.red

lemma ARS_termination_of_exists_NF (f : ARS α) [Inhabited α] :
  isTerminatingRel f → Nonempty (NF_of f) := by
    contrapose
    intro h
    rw [terminatingRelEquiv, isTerminatingRel']
    push_neg at h ⊢
    have a : α := Inhabited.default
    use (RedSeq f h a).val
    exact (RedSeq f h a).prop

def isProfondeur (f : ARS α) (π : α → ℕ) : Prop :=
  ∀ a, ∃ k, π a = Nat.succ k → ∃ b, π b = k ∧ f a b

def profondeurARS (f : ARS α) := Subtype (isProfondeur f)

instance inhabited_profondeurARS_of_termination {f : ARS α} (hfT : isTerminatingRel f) :
  Nonempty (profondeurARS f) := by
      let π : α → ℕ := fun a ↦ by
        have hTfa := hfT a
        push_neg at hTfa

        sorry
      sorry



/-- Le but de cette fonction est de fournir une fonction `φ : NF_fun f`,
étant données `f : ARS α` et la preuve de sa terminaison. -/
/- Comment faire une preuve correcte (idées) :
+ avoir une fonction `profondeur {f : ARS α} [isTerminatingRel f] : α → ℕ`, telle que
  `profondeur a = k + 1 → ∃ b, f a b ∧ profondeur b = k)` ;
+ `NF_fun_of_termination hfT` est bien définie, car les argument de type α successifs
  décroissent en profondeur.
 -/
noncomputable def NF_fun_of_termination {f : ARS α} (hfT : isTerminatingRel f) :
  NF_fun f := by
    refine ⟨?_, ?_⟩
    · intro a
      by_cases h : isNormalForm f a
      · exact ⟨a,h⟩
      · rw [isNormalForm] at h
        push_neg at h
        let b := h.choose
        exact (NF_fun_of_termination hfT).val b
    · intro a
      simp only
      by_cases h : isNormalForm f a
      · sorry
      · sorry
termination_by sorry

def isConvergent (f : ARS α) : Prop := isConfluent f ∧ isTerminatingRel f

def hasNormalFormProp (f : ARS α) : Prop := ∀ a : α, ∀ b : NF_of f, (f≡) a b → f∗ a b

def hasUniqueNormalFormProp (f : ARS α) : Prop := ∀ a b : NF_of f, (f≡) a b → a = b

def isSemiConvergent (f : ARS α) : Prop := hasUniqueNormalFormProp f ∧ isNormalizingRel f

lemma uniqueExists_NF_of_SemiConvergence (f : ARS α) :
  isSemiConvergent f →
  ∀ a, ∃ b : NF_of f, (f∗ a b.val ∧ ∀ b' : NF_of f, f∗ a b'.val → b = b') := by
    intro hfSC a
    let b := (hfSC.right a).choose
    have hb := (hfSC.right a).choose_spec
    use b
    constructor
    · exact hb
    · intro c hfac
      have hbc : (f≡) b.val c.val := by
        have := lubEquiv_contains_BandF hb hfac
        have defb : b = (hfSC.right a).choose := by trivial
        rw [← defb] at this
        exact this
      exact hfSC.left b c hbc

noncomputable instance inhabited_NF_fun_of_SemiConvergence
  {f : ARS α} (hfSC : isSemiConvergent f) :
  Inhabited (NF_fun f) where
    default := by
      have t := uniqueExists_NF_of_SemiConvergence f hfSC
      let φ x := (t x).choose
      have hφ x := (t x).choose_spec.left
      change ∀ x, f∗ x (φ x).val at hφ
      exact ⟨φ, hφ⟩

instance subsingleton_NF_fun_of_SemiConvergence
  {f : ARS α} (hfSC : isSemiConvergent f) :
  Subsingleton (NF_fun f) where
    allEq := by
      intro φ ψ
      rw [Subtype.ext_iff_val]
      ext x
      rw [← Subtype.ext_iff_val]
      have := (uniqueExists_NF_of_SemiConvergence f hfSC x)
      have hw := this.choose_spec
      have hw₁ := hw.right (φ.val x) (φ.prop x)
      have hw₂ := hw.right (ψ.val x) (ψ.prop x)
      rw [hw₁] at hw₂
      exact hw₂

noncomputable instance unique_NF_fun_of_SemiConvergence
  {f : ARS α} (hfSC : isSemiConvergent f) :
  Unique (NF_fun f) where
    default := (inhabited_NF_fun_of_SemiConvergence hfSC).default
    uniq a:= (subsingleton_NF_fun_of_SemiConvergence hfSC).allEq
        a (inhabited_NF_fun_of_SemiConvergence hfSC).default

lemma eq_of_trans_and_NF {f : ARS α} (b : NF_of f) : ∀ w, f∗ b.val w → b.val = w := by
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

def hasNoetherianInduction (f : ARS α) :=
  ∀ P : α → Prop, (∀ a, (∀ b, f a b → P b) → P a) → ∀ x, P x

def relous (P : α → Prop) := Subtype (¬ P ·)

theorem NoetherianInduction_from_termination {f : ARS α} (hfT : isTerminatingRel f) :
  hasNoetherianInduction f := by
    intro P
    contrapose
    push_neg
    intro hnPx
    let x := hnPx.choose
    have xdef : x = hnPx.choose := by trivial
    have hx := hnPx.choose_spec
    rw [← xdef] at hx
    have := hfT x
    by_cases hNFx : isNormalForm f x
    · have : ∀ b, f x b → P b := by
        intro y hAbsu
        exfalso
        exact hNFx y hAbsu
      use x
    · let ⟨φ, hφ⟩ := NF_fun_of_termination hfT
      let ⟨φx , hφx⟩ := φ x
      use φx
      constructor
      · intro b hfφxb
        exfalso
        exact hφx b hfφxb
      · intro hPφx

        sorry
    -- by_cases hIndu : ∀ y, ¬ P y → ∃ z, f y z ∧ ¬ P z
    -- · have : ∃ S : Nat → relous P, ∀ i, ¬ P (S i).val ∧ f (S i).val (S (i+1)).val := by
    --     let rec S := fun i : Nat ↦ if i = 0
    --       then
    --         (⟨x, hx⟩ : relous P)
    --       else by
    --         let z := (hIndu (S i.pred).val (S i.pred).prop).choose
    --         have zdef : z = (hIndu (S i.pred).val (S i.pred).prop).choose := by trivial
    --         have hz := (hIndu (S i.pred).val (S i.pred).prop).choose_spec.right
    --         rw [← zdef] at hz
    --         exact ⟨z, hz⟩
    --     termination_by sorry
    --     use S
    --     intro i
    --     constructor
    --     · by_cases hi : i = 0
    --       · sorry
    --       · sorry
    --     · sorry
    --   sorry
    -- · push_neg at hIndu
    --   sorry
    --
    --
    -- intro P h x
    -- by_cases hNFx : isNormalForm f x
    -- · have : ∀ b, f x b → P b := by
    --     intro y hAbsu
    --     exfalso
    --     exact hNFx y hAbsu
    --   exact h x this
    -- ·
    --   sorry

/- Le théorème 2.3.8-i -/
example (f : ARS α) :
  hasNormalFormProp f → hasUniqueNormalFormProp f :=  by
    intro hfNFProp a b hab
    have hfNFconcl := hfNFProp a b hab
    exact Subtype.ext_val (eq_of_trans_and_NF a b.val hfNFconcl)

/- Le théorème 2.3.8-ii -/
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

/- Le théorème 2.3.8-iii -/
noncomputable example (f : ARS α) :
  isSemiConvergent f → isConfluent f := by
    intro hfSC
    rw [confluentEquiv]
    intro a b b' ⟨hfab, hfab'⟩
    have ⟨φ, hφ⟩ := (inhabited_NF_fun_of_SemiConvergence hfSC).default
    use φ a
    have hfaφa := hφ a
    constructor
    · have hfaφb : f∗ a (φ b).val := kstar_is_trans f hfab (hφ b)
      have h : (f≡) (φ a) (φ b) := lubEquiv_contains_BandF hfaφa hfaφb
      have := (hfSC.left (φ a) (φ b) h)
      rw [this]
      exact hφ b
    · have hfaφb' : f∗ a (φ b').val := kstar_is_trans f hfab' (hφ b')
      have h : (f≡) (φ a) (φ b') := lubEquiv_contains_BandF hfaφa hfaφb'
      have := (hfSC.left (φ a) (φ b') h)
      rw [this]
      exact hφ b'

noncomputable instance inhabited_NF_fun_of_confluence_and_normalization
  {f : ARS α} (_ : isConfluent f) (hfNR : isNormalizingRel f) :
  Inhabited (NF_fun f) where
    default := by
      let φ x := (hfNR x).choose
      have hφ x := (hfNR x).choose_spec
      change ∀ x, f∗ x (φ x) at hφ
      exact ⟨φ, hφ⟩

instance subsingleton_NF_fun_of_confluence_and_normalization
  {f : ARS α} (hfC : isConfluent f) (hfNR : isNormalizingRel f) :
  Subsingleton (NF_fun f) where
    allEq := by
      rw [confluentEquiv] at hfC
      intro ⟨φ, hφ⟩ ⟨ψ, hψ⟩
      rw [Subtype.ext_iff_val]
      ext x
      simp
      rw [← Subtype.ext_iff_val, ]
      have h₁ := hφ x
      have h₂ := hψ x
      have h := hfC x (φ x).val (ψ x).val ⟨h₁, h₂⟩
      have ⟨hwφ, hwψ⟩ := h.choose_spec
      let nφ := hwφ.choose
      let nψ := hwψ.choose
      have nφdef : nφ = hwφ.choose := by trivial
      have nψdef : nψ = hwψ.choose := by trivial
      have hnφ := hwφ.choose_spec
      have hnψ := hwψ.choose_spec
      by_cases hn : ((nφ = 0) ∧ (nψ = 0))
      · have ⟨hnφ0, hnψ0⟩ := hn
        rw [←nφdef, hnφ0, pow_zero] at hnφ
        rw [←nψdef, hnψ0, pow_zero] at hnψ
        rw [←hnψ] at hnφ
        exact Subtype.ext_iff_val.mpr hnφ
      · exfalso
        push_neg at hn
        by_cases hnφ0 : nφ = 0
        · have hnψ0 := hn hnφ0
          have hpredn := (Nat.exists_eq_succ_of_ne_zero hnψ0).choose_spec
          rw [← nψdef, hpredn, ← Nat.add_one, add_comm, pow_add, pow_one] at hnψ
          exact (ψ x).prop hnψ.choose hnψ.choose_spec.left
        · have hpredn := (Nat.exists_eq_succ_of_ne_zero hnφ0).choose_spec
          rw [← nφdef, hpredn, ← Nat.add_one, add_comm, pow_add, pow_one] at hnφ
          exact (φ x).prop hnφ.choose hnφ.choose_spec.left

noncomputable example
  {f : ARS α} (hfC : isConfluent f) (hfNR : isNormalizingRel f) :
  ∀ φ : NF_fun f, ∀ a b : α, (f≡) a b ↔ (φ.val a = φ.val b) := by
    intro ⟨φ, hφ⟩ a b
    simp
    constructor
    · intro hequivfab
      have coeur := ARS.le_iff_imp.mp (ChurchRosser.mp hfC) a b hequivfab
      let w := coeur.choose
      have wdef : w = coeur.choose := by trivial
      have ⟨hwa, hwb⟩ := coeur.choose_spec
      rw [← wdef] at hwa hwb
      rw [← inv_trans_eq_trans_inv, inverse] at hwb
      have hwφw := hφ w
      by_cases h : ∃ ψ : NF_fun f, ψ.val w ≠ φ w
      · exfalso
        let ⟨ψ, hψ⟩ := h.choose
        have ψdef : ψ = h.choose.val := by sorry
        have hneqφwψw := h.choose_spec
        rw [← ψdef] at hneqφwψw
        have hneqφψ : (⟨φ, hφ⟩ : (NF_fun f)) ≠ ⟨ψ, hψ⟩ := by
          intro heq
          simp only [Subtype.mk.injEq] at heq
          rw [heq] at hneqφwψw
          simp only [ne_eq, not_true_eq_false] at hneqφwψw
        exact
          hneqφψ
          ((subsingleton_NF_fun_of_confluence_and_normalization hfC hfNR).allEq
            ⟨φ, hφ⟩ ⟨ψ, hψ⟩)
      · push_neg at h

        sorry
    · sorry
