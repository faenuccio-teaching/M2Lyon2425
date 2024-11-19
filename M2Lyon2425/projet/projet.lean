import Mathlib

/-
On s'intéresse ici, pour `α` un type quelconque, aux relations binaires sur `α`,
c'est à dire aux fonctions `α → α → Prop`. On fixe `f : α → α → Prop`. On voit cette
relation binaire comme un flèche, si `x y : α`, on peut aller de `x` à `y` si et
seulement si `f x y`. On peut alos s'intéresser à de la réécriture : est-il possible
d'aller de `x` à `y` *via* un chemin fini ?

Dans un premier temps on remarque que le type `α → α → Prop`, abbrégé en `ARS α`,
est naturellement muni d'une structure d'algèbre de Kleene (un anneau non-commutatif,
dont l'addition est idempotente, et muni d'une opération spéciale `∗`
(en notation postfixe) vérifiant différentes propriétés)

Ceci étant fait, il est beaucoup plus simple de vérifier certaines propriétés
d'opérations sur `ARS α` (de même qu'il est plus facile de les énoncer).

On pourra voir le cours en pdf de P. Malbos, trouvable dans le dossier "projet_docs".
De ce document, on va voir les preuves de la partie 2.3 (Normalisation & Termination),
notamment 2.3.8, 2.3.9 ainsi que l'implémentation de quelques définitions (formes normales,
terminaison, normalisation (faible et forte), …)

La structure du fichier est la suivante :
1. on prouve d'abord des résultats portants sur les algèbres de Kleene,
2. on montre que l'on peut munir `ARS α` d'une structure d'algèbre de Kleene,
3. on applique les théorèmes de la première partie aux ARS.
4. Éventuellement, on pourrait faire les mêmes preuves sans la structure algébrique.
-/

variable {α : Type*}

notation:1024 elm "∗" => KStar.kstar elm
-- pour une raison que j'ignore, cette notation n'est pas déjà définie

section QuelquesProprietesKleeneAlgebra

/- Dans cette section, on établit quelques propriétés de élémentaires
des algèbres de Kleene. Beaucoup sont déjà prouvées dans Mathlib/Algebra/Order/Kleene. -/

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

end QuelquesProprietesKleeneAlgebra

/-- Un alias pour le type des relations binaires sur un type  `α`. -/
@[reducible]
def ARS (β : Type*) := β → β → Prop

namespace ARS
/- On montre qu'il y a une structure d'algèbre de Kleene sur le type `ARS α` -/

section KleeneAlgebra

section IdemSemiring

section Semiring

section NonUnitalSemiring

section NonUnitalNonAssocSemiring

section AddCommMonoid

section AddMonoid

section Add

@[simp]
def add (f g : ARS α) : ARS α :=
  fun x y ↦ (f x y ∨ g x y)

instance instAdd : Add (ARS α) where
  add := add

end Add

section Zero

def zero : ARS α :=
  fun _ _ ↦ False

instance instZeroARS : Zero (ARS α) where
  zero := zero

end Zero

lemma add_assoc (f g h : ARS α ) :
  (f + g) + h = f + (g + h) := by
    ext x y
    change (fun u v ↦ (f u v ∨ g u v) ∨ h u v) x y ↔ (fun u v ↦ f u v ∨ (g u v ∨ h u v)) x y
    simp only
    rw [or_assoc]

instance instAddSemigroupARS : AddSemigroup (ARS α) where
    add_assoc := add_assoc

lemma zero_add (f : ARS α) :
  0 + f = f := by
    ext x y
    change False ∨ f x y ↔ f x y
    simp only [false_or]

lemma add_zero (f : ARS α) :
  f + 0 = f := by
    ext x y
    change f x y ∨ False ↔ f x y
    simp only [or_false]

def nsmul (n : ℕ) (f : ARS α) : ARS α := by -- nécessaire
  match n with
  | 0 => exact 0
  | _ => exact f

-- lemme intermédiare
lemma nsmul_succ_succ (n : ℕ) (f : ARS α) -- nécessaire
  : nsmul (n + 1) f = f := by
    trivial

-- lemme intermédiare
@[simp]
lemma addIdem (f : ARS α) : f + f = f := by
  ext x y
  constructor
  · intro h
    cases h with
    | inl left => exact left
    | inr right => exact right
  · intro h
    left
    exact h

-- lemme intermédiare
lemma nsmul_succ_zero (f : ARS α) -- nécessaire
  : nsmul 0 f = zero := by
    trivial

lemma nsmul_succ (n : ℕ ) (f : ARS α) :
  nsmul (n+1) f = add (nsmul n f) f := by
    rw [nsmul_succ_succ]
    cases n with
    | zero =>
      rw [nsmul_succ_zero]
      symm
      exact zero_add f
    | succ m =>
      rw [nsmul_succ_succ]
      symm
      exact addIdem f

instance instAddMonoidARS : AddMonoid (ARS α) where
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmul
  nsmul_succ := nsmul_succ

end AddMonoid

lemma add_comm (f g : ARS α) :
  f + g = g + f := by
    ext x y
    change (fun u v  ↦ f u v ∨ g u v) x y ↔ (fun u v  ↦ g u v ∨ f u v) x y
    exact or_comm

instance instAddCommMonoidARS : AddCommMonoid (ARS α) where
  add_comm := add_comm

end AddCommMonoid

section Mul

def mul (f g : ARS α) : ARS α :=
  fun u v ↦ (∃ w, f u w ∧ g w v)

instance instMulARS : Mul (ARS α) where
  mul := mul

end Mul

lemma left_distrib (f g h : ARS α) :
  f * (g + h) = (f * g) + (f * h) := by
    ext x y
    change
      (fun u v ↦ ∃ w, f u w ∧ (g w v ∨ h w v)) x y
      ↔ (fun u v ↦ (∃ w, f u w ∧ g w v) ∨ (∃ w, f u w ∧ h w v)) x y
    simp only
    constructor
    · intro hyp
      let we := hyp.choose
      have ⟨hw1, hw2⟩ := hyp.choose_spec
      cases hw2 with
      | inl hw3 =>
        left
        use we
      | inr hw3 =>
        right
        use we
    · intro hyp
      cases hyp with
      | inl hypl =>
        let we := hypl.choose
        have hw1 := hypl.choose_spec
        use we
        constructor
        · exact hw1.left
        · left
          exact hw1.right
      | inr hypr =>
        let we := hypr.choose
        have hw1 := hypr.choose_spec
        use we
        constructor
        · exact hw1.left
        · right
          exact hw1.right

lemma right_distrib (f g h : ARS α) :
  (f + g) * h = (f * h) + (g * h) := by
    ext x y
    change
      (fun u v ↦ ∃ w, (f u w ∨ g u w) ∧ h w v) x y
      ↔ (fun u v ↦ (∃ w, f u w ∧ h w v) ∨ (∃ w, g u w ∧ h w v)) x y
    simp only
    constructor
    · intro hyp
      let we := hyp.choose
      have ⟨hwl, hwr⟩ := hyp.choose_spec
      cases hwl with
      | inl hwll =>
        left
        use we
      | inr hwlr =>
        right
        use we
    · intro hyp
      cases hyp with
      | inl hypl =>
        let we := hypl.choose
        have ⟨hwl, hwr⟩ := hypl.choose_spec
        use we
        constructor
        · left
          exact hwl
        · exact hwr
      | inr hypr =>
        let we := hypr.choose
        have ⟨hwl, hwr⟩ := hypr.choose_spec
        use we
        constructor
        · right
          exact hwl
        · exact hwr

lemma zero_mul (f : ARS α) : 0 * f = 0 := by
  ext x y
  constructor
  · intro hyp
    simp only at hyp
    have hw := hyp.choose_spec
    exact hw.left
  · intro absu
    exfalso
    exact absu

lemma mul_zero (f : ARS α) : f * 0 = 0 := by
  ext x y
  constructor
  · intro hyp
    simp only at hyp
    have hw := hyp.choose_spec
    exact hw.right
  · intro absu
    exfalso
    exact absu

instance instNonUnitalNonAssocSemiringARS : NonUnitalNonAssocSemiring (ARS α) where
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero

end NonUnitalNonAssocSemiring

lemma mul_assoc (f g h : ARS α) :
   (f * g) * h = f * (g * h) := by
    symm
    ext x y
    constructor
    · intro hyp
      simp only at hyp
      let w1 := hyp.choose
      have ⟨hw1l, hw1r⟩ := hyp.choose_spec
      let w2 := hw1r.choose
      have ⟨hw2l, hw2r⟩ := hw1r.choose_spec
      use w2
      constructor
      · use w1
      · exact hw2r
    · intro hyp
      let w1 := hyp.choose
      have ⟨hw1l, hw1r⟩ := hyp.choose_spec
      let w2 := hw1l.choose
      have ⟨hw2l, hw2r⟩ := hw1l.choose_spec
      use w2
      constructor
      · exact hw2l
      · use w1

instance instNonUnitalSemiringARS : NonUnitalSemiring (ARS α) where
  mul_assoc := mul_assoc

end NonUnitalSemiring

section One

@[simp] def one : ARS α :=
  (fun x y ↦ x = y)

instance instOneARS : One (ARS α) where
  one := one

end One

section NatCast

@[simp]
def natCast (n : ℕ) : ARS α := by
  match n with
  | 0 => exact 0
  | _ + 1 => exact 1

instance instNatCastARS : NatCast (ARS α) where
  natCast := natCast

end NatCast

lemma mul_one (f : ARS α) :
  f * 1 = f := by
    ext x y
    constructor
    · intro hyp
      let we := hyp.choose
      have ⟨hwl, hwr⟩ := hyp.choose_spec
      change we = y at hwr -- pas nécessaire, mais aide à la compréhension
      rw [← hwr]
      exact hwl
    · intro hyp
      use y
      trivial

lemma one_mul  (f : ARS α) :
  1 * f = f := by
    ext x y
    constructor
    · intro hyp
      let we := hyp.choose
      have ⟨hwl, hwr⟩ := hyp.choose_spec
      change x = we at hwl -- pas nécessaire, mais aide à la compréhension
      rw [hwl]
      exact hwr
    · intro hyp
      use x
      trivial

lemma natCast_succ (n : ℕ) : @natCast α (n + 1) = natCast n + 1 := by
  cases n with
  | zero =>
    simp only [natCast, _root_.zero_add]
  | succ m =>
    simp only [natCast, addIdem]

def npow (n : ℕ) (f : ARS α) :
  ARS α := by
    match n with
    | 0 => exact 1
    | m + 1 => exact (npow m f) * f

instance instSemiringARS : Semiring (ARS α) where
  one_mul := one_mul
  mul_one := mul_one
  natCast_succ := natCast_succ

end Semiring

section SemilatticeSup

section PartialOrder

section Preorder

section LE

def le (f g : ARS α) : Prop :=
  f + g = g

instance instLEARS : LE (ARS α) where
  le := le

end LE

section LT

@[simp]
def lt (f g : ARS α) : Prop :=
  f ≤ g ∧ ¬ (f = g)

instance instLTARS : LT (ARS α) where
  lt := lt

end LT

lemma le_refl (f : ARS α) :
  f ≤ f := by
    exact addIdem f

lemma le_trans {f g h : ARS α} :
  f ≤ g → g ≤ h → f ≤ h := by
    intro add_fg add_gh
    change f + h = h
    rw [← add_gh]
    nth_rw 2 [← add_fg]
    rw [add_assoc]

lemma lt_iff_le_not_le (f g : ARS α) :
  f < g ↔ f ≤ g ∧ ¬ g ≤ f := by
    constructor
    · intro ⟨le_fg, neq_fg⟩
      constructor
      · exact le_fg
      · intro le_gf
        change g + f = f at le_gf
        change f + g = g at le_fg
        rw [add_comm, le_gf] at le_fg
        exact neq_fg le_fg
    · intro ⟨le_fg, nle_gf⟩
      constructor
      · exact le_fg
      · intro eq_fg
        rw [eq_fg] at nle_gf
        exact nle_gf (le_refl g)

instance instPreorderARS : Preorder (ARS α) where
  le_refl := le_refl
  le_trans := @le_trans α
  lt_iff_le_not_le := lt_iff_le_not_le

end Preorder

lemma le_antisymm (f g : ARS α) :
  f ≤ g → g ≤ f → f = g := by
    intro add_fg add_gf
    rw [← add_fg]
    nth_rw 1 [← add_gf]
    exact add_comm g f

instance instPartialOrderARS : PartialOrder (ARS α) where
  le_antisymm := le_antisymm

end PartialOrder

section Sup

def sup (f g : ARS α) : ARS α := f + g

instance instSupARS : Sup (ARS α) where
  sup := sup

end Sup

lemma le_sup_left (f g : ARS α) :
  f ≤ (f + g) := by
    change f + (f + g) = f + g
    rw [← add_assoc, addIdem]

lemma le_sup_right (f g : ARS α) :
  g ≤ (f + g) := by
    change g + (f + g) = f +g
    rw [add_comm, add_assoc, addIdem]

lemma sup_le (f g h : ARS α) :
  f ≤ h → g ≤ h → (f + g) ≤ h := by
    intro add_fh add_gh
    change f + g + h = h
    rw [add_assoc, add_gh, add_fh]

instance instSemilatticeSupARS : SemilatticeSup (ARS α) where
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le := sup_le

end SemilatticeSup

lemma bot_le (f : ARS α) : 0 ≤ f := by
  exact zero_add f

instance instIdemSemiringARS : IdemSemiring (ARS α) where
  bot_le := bot_le

end IdemSemiring

section KStar

/-- On utilise ici le fait que le quantificateur existentiel peut être vu comme
une disjonction infinie sur le type sur lequel il quantifie : en d'autres termes,
`∃ (x : α), P x` est équivalent à `⋁ (x : α), P x`
Puisque `+` est une disjontion binaire, une somme infinie est une disjonction infinie -/
def kstar (f : ARS α) :
  ARS α := fun u v ↦ ∃ n, (f^n) u v

instance instKStarARS : KStar (ARS α) where
  kstar := kstar

end KStar

lemma one_le_kstar (f : ARS α) : 1 ≤ f∗ := by
  ext x y
  constructor
  · intro hyp
    cases hyp with
    | inl l =>
      use 0
      exact l
    | inr r => exact r
  · intro hyp
    right
    exact hyp

/- On a f^n f = f f^n, par récurrence -/
-- lemme intermédiare
lemma npow_mul_eq_mul_npow (n : ℕ) (f : ARS α) :
  f * (f^n) = (f ^ n) * f := by
    match n with
    | 0 =>
      rw [pow_zero, one_mul, mul_one]
    | m + 1 =>
      rw [pow_succ, ← mul_assoc, npow_mul_eq_mul_npow]

lemma mul_kstar_le_kstar (f : ARS α) :
  f * f∗ ≤ f∗ := by
    ext x y
    constructor
    · intro hyp
      cases hyp with
      | inl hyp_mul =>
        let w := hyp_mul.choose
        have ⟨hwl, hwr⟩ := hyp_mul.choose_spec
        let n := hwr.choose
        have hn := hwr.choose_spec
        use (n+1)
        rw [
          pow_succ,
          ← npow_mul_eq_mul_npow
        ]
        use w
      | inr hypr =>
        exact hypr
    · intro hyp
      right
      exact hyp

lemma kstar_mul_le_kstar (f : ARS α) :
   f∗ * f ≤ f∗ := by
    ext x y
    constructor
    · intro hyp
      cases hyp with
      | inl hyp_mul =>
        let w := hyp_mul.choose
        have ⟨hwl, hwr⟩ := hyp_mul.choose_spec
        let n := hwl.choose
        have hn := hwl.choose_spec
        use (n+1)
        rw [pow_succ]
        use w
      | inr hypr =>
        exact hypr
    · intro hyp
      right
      exact hyp

section QuelquesLemmes

-- lemme intermédiare
lemma ban_le_bam {f g : ARS α} :
  f * g ≤ f →
  ∀ (n : ℕ), f * (g^(n + 1)) ≤ f * g^n := by
    intro hyp n
    rw [
      pow_succ,
      ← npow_mul_eq_mul_npow,
      ← mul_assoc
    ]
    change f*g * g^n + f * g^n = f*g^n
    rw[
      ← right_distrib,
      hyp
    ]

-- lemme intermédiare
lemma ban_le_b {f g : ARS α} :
  (∀ n, f * g^(n + 1) ≤ f * g^n) →
  ∀ n, f * g ^ n ≤ f := by
    intro hyp n
    cases n with
    | zero =>
      simp only [pow_zero, _root_.mul_one, _root_.le_refl]
    | succ m =>
      exact le_trans (hyp m) (ban_le_b hyp m)

-- lemme intermédiare
lemma bak_le_b {f g : ARS α} :
  (∀ (n : ℕ), f * g^n ≤ f) →
  f * g∗ ≤ f := by
    intro hyp
    ext x y
    constructor
    · intro h2
      cases h2 with
      | inl l =>
        let w := l.choose
        have ⟨hwl, hwr⟩ := l.choose_spec
        let n := hwr.choose
        have hn := hwr.choose_spec
        have hypn := hyp n
        rw [← hypn]
        left
        use w
      | inr r =>
        exact r
    · intro hyp
      right
      exact hyp

-- lemme intermédiare
lemma anb_le_amb {f g : ARS α} :
  g * f ≤ f →
  ∀ (n : ℕ), (g^(n + 1)) * f ≤ g^n * f := by
    intro hyp n
    rw [
      pow_succ,
      mul_assoc
    ]
    change g^n * (g*f) + g^n * f = g^n * f
    rw[
      ← left_distrib,
      hyp
    ]

-- lemme intermédiare
lemma anb_le_b {f g : ARS α} :
  (∀ n, g^(n + 1) * f ≤ g^n * f) →
  ∀ n, g^n * f ≤ f := by
    intro hyp n
    cases n with
    | zero =>
      simp only [pow_zero, _root_.one_mul, _root_.le_refl]
    | succ m =>
      exact le_trans (hyp m) (anb_le_b hyp m)

-- lemme intermédiare
lemma akb_le_b {f g : ARS α} :
  (∀ (n : ℕ), g^n * f ≤ f) →
  g∗ * f ≤ f := by
    intro hyp
    ext x y
    constructor
    · intro h2
      cases h2 with
      | inl l =>
        let w := l.choose
        have ⟨hwl, hwr⟩ := l.choose_spec
        let n := hwl.choose
        have hn := hwl.choose_spec
        have hypn := hyp n
        rw [← hypn]
        left
        use w
      | inr r =>
        exact r
    · intro hyp
      right
      exact hyp

end QuelquesLemmes

lemma mul_kstar_le_self (g f : ARS α) :
  f * g ≤ f → f * g∗ ≤ f := by
    intro hyp
    exact bak_le_b (ban_le_b (ban_le_bam hyp))


lemma kstar_mul_le_self (g f : ARS α) :
  g * f ≤ f → g∗ * f ≤ f := by
    intro hyp
    exact akb_le_b (anb_le_b (anb_le_amb hyp))

instance instKleeneAlgebra : KleeneAlgebra (ARS α) where
  one_le_kstar := one_le_kstar
  mul_kstar_le_kstar := mul_kstar_le_kstar
  kstar_mul_le_kstar := kstar_mul_le_kstar
  mul_kstar_le_self := mul_kstar_le_self
  kstar_mul_le_self := kstar_mul_le_self

end KleeneAlgebra

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

end ARS

section QuelquesPreuves
/-
On montre quelques lemmes basiques spécifique aux ARS :
- la clôture symmétrique est symétrique,
- la cloture transitive est transitive,
- …
-/

/-- Une définition alternative de `∗`.-/
lemma kstar' (f : ARS α) :
  f∗ = ARS.big_sum (fun n ↦ f^n) := by
    rfl

/- `∗` n'est pas la clôture transitive, mais bien la clôture transitive *et* réflexive.-/
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

/-- Une définition alternative de `⁺`.-/
lemma plus' (f : ARS α) :
  f⁺ = ARS.big_sum (fun i ↦ f^(i+1)) := by
    ext x y
    constructor
    · intro hyp
      let n := hyp.choose
      have ⟨hf, _⟩ := hyp.choose_spec
      use hyp.choose - 1
      simp only
      have : n - 1 + 1 = n := by omega
      rw [this]
      exact hf
    · intro hyp
      have hf := hyp.choose_spec
      simp only at hf
      use hyp.choose + 1
      exact ⟨hf, by omega⟩

lemma tempo (f : ARS α) :
  ∀ i, (fun i _ ↦ f^(i+1)) i f = (fun i g ↦ g^(i+1)) i f := by
    intro i
    simp only

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

-- lemma plus_comm_pown {f : ARS α} {n : ℕ} : f⁺ * f^n = f^n * f⁺ := by
--   rw [plus']
--   refine ARS.big_sum_comm_from_comm (fun i g ↦ g^(i+1)) ?_
--   intro i
--   simp only
--   rw [← pow_add, ← pow_add, add_comm]

lemma _fonction_puissance_succ [Monoid α] (f : α) : (fun i ↦ f * f^i) = fun i ↦ f^(i+1) := by
  ext i
  nth_rw 1 [← pow_one f]
  rw [← pow_add, add_comm]

lemma plus_mul_kstar {f : ARS α} : f⁺ = f * f∗  := by
  rw [
    kstar',
    plus',
    ARS.big_sum_distrib_left,
    _fonction_puissance_succ
    ]

-- lemma plus_mul_pown {f : ARS α} {n : ℕ} : f⁺^(n+1) = f^n * f⁺ := by
--   induction n with
--   | zero =>
--     simp only [zero_add, pow_one, pow_zero, one_mul]
--   | succ m hm  =>
--     rw [
--       add_assoc,
--       one_add_one_eq_two,
--       add_comm,
--       pow_add,
--       add_comm,
--       pow_add,
--       pow_one,
--       mul_assoc,
--       ← hm,
--       add_comm,
--       pow_add,
--       pow_one,
--       ← mul_assoc,
--       self_mul_plus
--     ]


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

lemma inv_trans_eq_trans_inv (f : ARS α) : f⇐∗ = f∗⇐ := by
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

end QuelquesPreuves

section QuelquesProprietesARS

def isWeaklyCommuting (f₁ f₂ : ARS α) : Prop := f₁⇐ * f₂ ≤ f₂∗ * f₁⇐∗

def isCommuting (f₁ f₂ : ARS α) : Prop := f₁⇐ * f₂ ≤ f₂ * f₁⇐

def isDiamond (f : ARS α) : Prop := isCommuting f f

def isChurchRosser (f : ARS α) : Prop := f≡ ≤ f∗ * f⇐∗

def isConfluent (f : ARS α) : Prop := f⇐∗ * f∗ ≤ f∗ * f⇐∗

def isWeaklyConfluent (f : ARS α) : Prop := f⇐ * f ≤ f∗ * f⇐∗

theorem ChurchRosser (f : ARS α) : isConfluent f ↔ isChurchRosser f := by
  rw [isConfluent, isChurchRosser]
  exact KleeneChurchRosser

def isNormalForm (f : ARS α) (a : α) : Prop := ∀ b, ¬(f a b)

end QuelquesProprietesARS
