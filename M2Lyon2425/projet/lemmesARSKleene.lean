import M2Lyon2425.projet.KleeneAlgebra
import M2Lyon2425.projet.lemmesARS

variable {α : Type*}

open Computability

/-
On montre quelques lemmes basiques spécifique aux ARS :
- la clôture symmétrique est symétrique,
- la cloture transitive est transitive,
- …
-/

/- `∗` n'est pas la clôture transitive,
mais bien la clôture transitive *et* réflexive.-/
lemma kstar_is_refl (f : ARS α) : Reflexive f∗ := by
  intro x
  use 0
  trivial

lemma kstar_is_trans (f : ARS α) : Transitive f∗ := by
  intro x y z hxy hyz
  have pnxy := hxy.choose_spec
  have pnyz := hyz.choose_spec
  use hxy.choose + hyz.choose
  rw [pow_add]
  use y

/-- La plus petite relation transitive issue d'une relation donnée-/
@[reducible]
def trans_closure (f : ARS α) : ARS α := fun x y ↦ ∃ n, (f^n) x y ∧ 0 < n
notation:1024 elm "⁺" => trans_closure elm

lemma le_plus (f : ARS α) : f ≤ f⁺ := by
  rw [ARS.le_iff_imp]
  intro _ _ fxy
  use 1
  rw [pow_one]
  exact ⟨fxy, by omega⟩

lemma plus_mono {f g : ARS α} : f ≤ g → f⁺ ≤ g⁺  := by
  intro lefg
  rw [ARS.le_iff_imp]
  intro x y fpxy
  let n := fpxy.choose
  have ⟨hfnxy, hn⟩ := fpxy.choose_spec
  use n
  exact ⟨ARS.le_iff_imp.mp (topown_mono n lefg) x y hfnxy, hn⟩

lemma plus_is_transitive (f : ARS α) : Transitive f⁺ := by
  intro x y z hxy hyz
  have pnxy := hxy.choose_spec
  have pnyz := hyz.choose_spec
  use hxy.choose + hyz.choose
  constructor
  · rw [pow_add]
    use y
    exact ⟨pnxy.left, pnyz.left⟩
  · omega -- on utilise ici, de façon cachée, `pnxy.right` et `pnyz.right`

lemma plus_add_one (f : ARS α) : f∗ = 1 + f⁺ := by
  ext x y
  constructor
  · intro hyp
    have hn := hyp.choose_spec
    have := eq_zero_or_pos hyp.choose
    cases this with
    | inl zero =>
      rw [zero, pow_zero] at hn
      left
      exact hn
    | inr pos =>
      right
      use hyp.choose
  · intro hyp
    cases hyp with
    | inl eg =>
      use 0
      rw [pow_zero]
      exact eg
    | inr pos =>
      use pos.choose
      exact pos.choose_spec.left

/-- La relation inverse issue d'une relation donnée -/
@[reducible]
def inverse (f : ARS α) : ARS α := fun x y ↦ f y x
notation:1024 elm "⇐" => inverse elm

@[simp] lemma inverse_involution (f : ARS α) : f⇐⇐ = f := by
  ext x y
  simp only

@[simp] lemma inverse_one : (1 : ARS α)⇐ = 1 := by
  ext x y
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    rw [h]
    rfl

@[simp] lemma inverse_over_add (f g : ARS α) : (f + g)⇐ = f⇐ + g⇐ := by
  ext x y
  rfl

/-- La plus petite relation contenant une relation et son inverse -/
@[reducible]
def symm_closure (f : ARS α) : ARS α := f + f⇐
notation:1024 elm "⇔" => symm_closure elm

lemma symm_is_idem (f : ARS α) : f⇔⇔ = f⇔ := by
  change (f + f⇐) + (f + f⇐)⇐ = f + f⇐
  simp only [inverse_over_add, inverse_involution]
  rw [add_assoc]
  nth_rw 2 [← add_assoc]
  rw [add_idem]
  nth_rw 2 [add_comm]
  nth_rw 1 [← add_assoc]
  rw [add_idem] -- une fois pour f, une fois pour f⇔

lemma symm_closure_is_symm (f : ARS α) : Symmetric f⇔ := by
  intro x y hxy
  cases hxy with
  | inl direct =>
    right
    exact direct
  | inr indirect =>
    left
    exact indirect

lemma inv_pow_eq_pow_inv (f : ARS α) (n : ℕ): f⇐^n = (f^n)⇐ := by
  match n with
  | 0 =>
    simp only [pow_zero, inverse_one]
  | m + 1 =>
    rw [pow_succ, pow_succ, ← ARS.npow_mul_eq_mul_npow]
    ext x y
    constructor
    · intro hyp
      let w := hyp.choose
      have ⟨hw, hwm⟩ := hyp.choose_spec
      use w
      constructor
      · rw [← inverse_involution f, inv_pow_eq_pow_inv]
        exact hwm
      · exact hw
    · intro hyp
      let w := hyp.choose
      have ⟨hwm, hw⟩ := hyp.choose_spec
      use w
      constructor
      · exact hw
      · rw [inv_pow_eq_pow_inv]
        exact hwm

@[simp]
lemma inv_trans_eq_trans_inv (f : ARS α) : f∗⇐ = f⇐∗ := by
  ext x y
  constructor
  · intro hyp
    use hyp.choose
    have hn := hyp.choose_spec
    rw [inv_pow_eq_pow_inv] at hn
    exact hn
  · intro hyp
    simp only at hyp
    use hyp.choose
    have hn := hyp.choose_spec
    rw [inv_pow_eq_pow_inv]
    exact hn

/-- La plus petite relation d'équivalence contenant une relation -/
@[reducible]
def lubEquiv (f : ARS α) : ARS α :=  f⇔∗
notation:1024 elm "≡" => lubEquiv elm

lemma lubEquiv_is_trans (f : ARS α) : Transitive f≡ :=
    kstar_is_trans f⇔

lemma lubEquiv_is_refl (f : ARS α) : Reflexive f≡ :=
    kstar_is_refl f⇔

lemma symm_n_is_symm (f : ARS α) : ∀ n, Symmetric (f⇔^n) := by
    intro n
    cases n with
    | zero =>
      simp only [pow_zero]
      intro x y hxy
      rw [hxy]
      rfl
    | succ m =>
      rw [pow_succ]
      intro x y hxy
      let w := hxy.choose
      have hw := hxy.choose_spec
      rw [← ARS.npow_mul_eq_mul_npow]
      use w
      constructor
      · exact (symm_closure_is_symm f) hw.right
      · exact (symm_n_is_symm f m) hw.left

lemma lubEquiv_is_symm (f : ARS α) : Symmetric f≡ := by
  intro x y hxy
  let n := hxy.choose
  have h := hxy.choose_spec
  use n
  exact (symm_n_is_symm f n) h

lemma lubEquiv_is_equiv (f : ARS α) : Equivalence f≡ where
  refl := @lubEquiv_is_refl α f
  symm := @lubEquiv_is_symm α f
  trans := @lubEquiv_is_trans α f

/- Les lemmes suivants permettent de faire des calculs simples sur la clôture ≡ -/

@[simp]
lemma lubEquiv_contains_self {f : ARS α} : f ≤ f≡ := by
  rw [ARS.le_iff_imp]
  intro _ _ h
  use 1
  rw [pow_one]
  left
  exact h

@[simp]
lemma lubEquiv_contains_add {f g₁ g₂ : ARS α} : g₁ ≤ f≡ → g₂ ≤ f≡ → g₁ + g₂ ≤ f≡ := by
  intro hyp₁ hyp₂
  have := add_respects_le hyp₁ hyp₂
  rw [add_idem] at this
  exact this

@[simp]
lemma lubEquiv_contains_mul {f g₁ g₂ : ARS α} : g₁ ≤ f≡ → g₂ ≤ f≡ → g₁ * g₂ ≤ f≡ := by
  intro hyp₁ hyp₂
  rw [lubEquiv, ← kstar_mul_kstar, ← lubEquiv]
  exact mul_respects_le hyp₁ hyp₂

@[simp]
lemma lubEquiv_contains_pown {f g : ARS α} {n : ℕ} : g ≤ f≡ → g^n ≤ f≡ := by
  induction n with
  | zero =>
    intro _
    simp only [pow_zero, one_le_kstar]
  | succ n ih =>
    intro hyp
    rw [pow_add, pow_one]
    exact lubEquiv_contains_mul (ih hyp) (hyp)

@[simp]
lemma lubEquiv_contains_inverse {f g : ARS α} : g ≤ f≡ → g⇐ ≤ f≡ := by
  intro hyp
  rw [ARS.le_iff_imp] at hyp ⊢
  intro x y hyprev
  exact Equivalence.symm (lubEquiv_is_equiv f) (hyp y x hyprev)

@[simp]
lemma lubEquiv_contains_symm_closure {f g : ARS α} : g ≤ f≡ → g⇔ ≤ f≡ := by
  intro hyp
  refine lubEquiv_contains_add hyp (lubEquiv_contains_inverse hyp)

@[simp]
lemma lubEquiv_contains_kstar {f g : ARS α} : g ≤ f≡ → g∗ ≤ f≡ := by
  intro hyp
  rw [lubEquiv, ← kstar_idem f⇔, ← lubEquiv]
  exact kstar_mono hyp

lemma lubEquiv_contains_BandF {f : ARS α} {a b c : α} (hfab : f∗ a b) (hfac : f∗ a c) :
  (f≡) b c := by
    let nab := hfab.choose
    have hnab := hfab.choose_spec
    let nac := hfac.choose
    have hnac := hfac.choose_spec
    use nab+nac
    rw [pow_add]
    use a
    constructor
    · have ineq : f⇐ ≤ f⇔ := by simp only [add_eq_sup, le_sup_right]
      have implication : f⇐ ^ nab ≤ f⇔ ^ nab := topown_mono nab ineq
      have : (f⇐ ^ nab) b a := by
        rw [inv_pow_eq_pow_inv, inverse]
        exact hnab
      exact ARS.le_iff_imp.mp implication b a this
    · have ineq : f ≤ f⇔ := by simp only [add_eq_sup, le_sup_left]
      have implication : f ^ nac ≤ f⇔ ^ nac := topown_mono nac ineq
      have : (f ^ nac) a c := hnac
      exact ARS.le_iff_imp.mp implication a c this
