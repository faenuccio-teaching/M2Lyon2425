import Mathlib

/-- Un alias pour le type des relations binaires sur un type  `α`. -/
@[reducible]
def ARS (β : Type*) := β → β → Prop

variable {α : Type*}

namespace ARS -- on préfixe les instances `ARS α` par «ARS» -/

open Computability -- pour avoir la notation ∗

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

end ARS
