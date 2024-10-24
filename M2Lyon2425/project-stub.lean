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
-/


/-- Un alias pour le type des relations binaires sur un type  `α`. -/
@[reducible]
def ARS (α : Type*) := α → α → Prop

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
def ARS_add {α : Type*} (f g : ARS α) : ARS α :=
  fun x y ↦ (f x y ∨ g x y)

instance (α : Type*) : Add (ARS α) where
  add := ARS_add

end Add

section Zero

def ARS_zero {α : Type*} : ARS α :=
  fun _ _ ↦ False

instance (α : Type*) : Zero (ARS α) where
  zero := ARS_zero

end Zero

lemma ARS_add_assoc {α : Type*} (f g h : ARS α ) :
  (f + g) + h = f + (g + h) := by
    ext x y
    change (fun u v ↦ (f u v ∨ g u v) ∨ h u v) x y ↔ (fun u v ↦ f u v ∨ (g u v ∨ h u v)) x y
    simp
    rw [or_assoc]

instance (α : Type*) : AddSemigroup (ARS α) where
  add_assoc := ARS_add_assoc

lemma ARS_zero_add {α : Type*} (f : ARS α) :
  0 + f = f := by
    ext x y
    change False ∨ f x y ↔ f x y
    simp

lemma ARS_add_zero {α : Type*} (f : ARS α) :
  f + 0 = f := by
    ext x y
    change f x y ∨ False ↔ f x y
    simp

def ARS_nsmul {α : Type*} (n : ℕ) (f : ARS α) : ARS α := by -- nécessaire
  match n with
  | 0 => exact ARS_zero
  | _ => exact f

-- lemme intermédiare
lemma ARS_nsmul_succ_succ {α : Type*} (n : ℕ) (f : ARS α) -- nécessaire
  : ARS_nsmul (n + 1) f = f := by
    trivial

-- lemme intermédiare
@[simp]
lemma ARS_addIdem {α : Type*} (f : ARS α) : f + f = f := by
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
lemma ARS_nsmul_succ_zero {α : Type*} (f : ARS α) -- nécessaire
  : ARS_nsmul 0 f = ARS_zero := by
    trivial

lemma ARS_nsmul_succ {α : Type*} (n : ℕ ) (f : ARS α) :
  ARS_nsmul (n+1) f = ARS_add (ARS_nsmul n f) f := by
    rw [ARS_nsmul_succ_succ]
    cases n with
    | zero =>
      rw [ARS_nsmul_succ_zero]
      symm
      exact ARS_zero_add f
    | succ m =>
      rw [ARS_nsmul_succ_succ]
      symm
      exact ARS_addIdem f

instance (α : Type*) : AddMonoid (ARS α) where
  zero_add := ARS_zero_add
  add_zero := ARS_add_zero
  nsmul := ARS_nsmul
  nsmul_succ := ARS_nsmul_succ

end AddMonoid

lemma ARS_add_comm {α : Type*} (f g : ARS α) :
  f + g = g + f := by
    ext x y
    change (fun u v  ↦ f u v ∨ g u v) x y ↔ (fun u v  ↦ g u v ∨ f u v) x y
    exact or_comm

instance (α : Type*) : AddCommMonoid (ARS α) where
  add_comm := ARS_add_comm

end AddCommMonoid

section Mul

def ARS_mul {α : Type*} (f g : ARS α) : ARS α :=
  fun u v ↦ (∃ w, f u w ∧ g w v)

instance (α : Type*) : Mul (ARS α) where
  mul := ARS_mul

end Mul

lemma ARS_left_distrib {α : Type*} (f g h : ARS α) :
  f * (g + h) = (f * g) + (f * h) := by
    ext x y
    change
      (fun u v ↦ ∃ w, f u w ∧ (g w v ∨ h w v)) x y
      ↔ (fun u v ↦ (∃ w, f u w ∧ g w v) ∨ (∃ w, f u w ∧ h w v)) x y
    simp
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

lemma ARS_right_distrib {α : Type*} (f g h : ARS α) :
  (f + g) * h = (f * h) + (g * h) := by
    ext x y
    change
      (fun u v ↦ ∃ w, (f u w ∨ g u w) ∧ h w v) x y
      ↔ (fun u v ↦ (∃ w, f u w ∧ h w v) ∨ (∃ w, g u w ∧ h w v)) x y
    simp
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

lemma ARS_zero_mul {α : Type*} (f : ARS α) : 0 * f = 0 := by
  ext x y
  constructor
  · intro hyp
    simp at hyp
    have hw := hyp.choose_spec
    exact hw.left
  · intro absu
    exfalso
    exact absu

lemma ARS_mul_zero {α : Type*} (f : ARS α) : f * 0 = 0 := by
  ext x y
  constructor
  · intro hyp
    simp at hyp
    have hw := hyp.choose_spec
    exact hw.right
  · intro absu
    exfalso
    exact absu

instance (α : Type*) : NonUnitalNonAssocSemiring (ARS α) where
  left_distrib := ARS_left_distrib
  right_distrib := ARS_right_distrib
  zero_mul := ARS_zero_mul
  mul_zero := ARS_mul_zero

end NonUnitalNonAssocSemiring

lemma ARS_mul_assoc {α : Type*} (f g h : ARS α) :
   (f * g) * h = f * (g * h) := by
    symm
    ext x y
    constructor
    · intro hyp
      simp at hyp
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

instance (α : Type*) : NonUnitalSemiring (ARS α) where
  mul_assoc := ARS_mul_assoc

end NonUnitalSemiring

section One

@[simp] def ARS_one {α : Type*} : ARS α :=
  (fun x y ↦ x = y)

instance (α : Type*) : One (ARS α) where
  one := ARS_one

end One

section NatCast

@[simp]
def ARS_natCast {α : Type*} (n : ℕ) : ARS α := by
  match n with
  | 0 => exact 0
  | _ + 1 => exact 1

instance (α : Type*) : NatCast (ARS α) where
  natCast := ARS_natCast

end NatCast

lemma ARS_mul_one {α : Type*} (f : ARS α) :
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

lemma ARS_one_mul {α : Type*} (f : ARS α) :
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

lemma ARS_natCast_succ {α : Type*} (n : ℕ) : @ARS_natCast α (n + 1) = ARS_natCast n + 1 := by
  cases n with
  | zero =>
    simp
  | succ m =>
    simp

def ARS_npow {α : Type*} (n : ℕ) (f : ARS α) :
  ARS α := by
    match n with
    | 0 => exact 1
    | m + 1 => exact (ARS_npow m f) * f

instance (α : Type*) : Semiring (ARS α) where
  one_mul := ARS_one_mul
  mul_one := ARS_mul_one
  natCast_succ := ARS_natCast_succ

end Semiring

section SemilatticeSup

section PartialOrder

section Preorder

section LE

@[simp]
def ARS_le {α : Type*} (f g : ARS α) : Prop :=
  f + g = g

instance (α : Type*) : LE (ARS α) where
  le := ARS_le

end LE

section LT

@[simp]
def ARS_lt {α : Type*} (f g : ARS α) : Prop :=
  f ≤ g ∧ ¬ (f = g)

instance (α : Type*) : LT (ARS α) where
  lt := ARS_lt

end LT

lemma ARS_le_refl {α : Type*} (f : ARS α) :
  f ≤ f := by
    exact ARS_addIdem f

lemma ARS_le_trans {α : Type*} (f g h : ARS α) :
  f ≤ g → g ≤ h → f ≤ h := by
    intro add_fg add_gh
    change f + h = h
    rw [← add_gh]
    nth_rw 2 [← add_fg]
    rw [add_assoc]

lemma ARS_lt_iff_le_not_le {α : Type*} (f g : ARS α) :
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
        exact nle_gf (ARS_le_refl g)

instance (α : Type*) : Preorder (ARS α) where
  le_refl := ARS_le_refl
  le_trans := ARS_le_trans
  lt_iff_le_not_le := ARS_lt_iff_le_not_le

end Preorder

lemma ARS_le_antisymm {α : Type*} (f g : ARS α) :
  f ≤ g → g ≤ f → f = g := by
    intro add_fg add_gf
    rw [← add_fg]
    nth_rw 1 [← add_gf]
    exact add_comm g f

instance (α : Type*) : PartialOrder (ARS α) where
  le_antisymm := ARS_le_antisymm

end PartialOrder

section Sup

def ARS_sup {α : Type*} (f g : ARS α) : ARS α := f + g

instance (α : Type*) : Sup (ARS α) where
  sup := ARS_sup

end Sup

lemma ARS_le_sup_left {α : Type*} (f g : ARS α) :
  f ≤ (f + g) := by
    change f + (f + g) = f + g
    rw [← add_assoc, ARS_addIdem]

lemma ARS_le_sup_right {α : Type*} (f g : ARS α) :
  g ≤ (f + g) := by
    change g + (f + g) = f +g
    rw [add_comm, add_assoc, ARS_addIdem]

lemma ARS_sup_le {α : Type*} (f g h : ARS α) :
  f ≤ h → g ≤ h → (f + g) ≤ h := by
    intro add_fh add_gh
    change f + g + h = h
    rw [add_assoc, add_gh, add_fh]

instance (α : Type*) : SemilatticeSup (ARS α) where
  le_sup_left := ARS_le_sup_left
  le_sup_right := ARS_le_sup_right
  sup_le := ARS_sup_le

end SemilatticeSup

lemma ARS_bot_le {α : Type*} (f : ARS α) : 0 ≤ f := by
  exact zero_add f

instance (α : Type*) : IdemSemiring (ARS α) where
  bot_le := ARS_bot_le

end IdemSemiring

section KStar

/-- On utilise ici le fait que le quantificateur existentiel peut être vu comme
une disjonction infinie sur le type sur lequel il quantifie : en d'autres termes,
`∃ (x : α), P x` est équivalent à `⋁ (x : α), P x`
Puisque `+` est une disjontion binaire, une somme infinie est une disjonction infinie -/
def ARS_kstar {α : Type*} (f : ARS α) :
  ARS α := fun u v ↦ ∃ n, (f ^ n) u v

instance (α : Type*) : KStar (ARS α) where
  kstar := ARS_kstar

notation:1024 elm "∗ " => KStar.kstar elm
-- pour une raison que j'ignore, cette notation n'est pas déjà définie

end KStar

lemma ARS_one_le_kstar {α : Type*} (f : ARS α) :
  1 ≤ f∗ := by
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
lemma ARS_npow_mul_eq_mul_npow {α : Type*} (n : ℕ) (f : ARS α) :
  f * (f^n) = (f ^ n) * f := by
    match n with
    | 0 =>
      rw [pow_zero, one_mul, mul_one]
    | m + 1 =>
      rw [pow_succ, ← mul_assoc, ARS_npow_mul_eq_mul_npow]

lemma ARS_mul_kstar_le_kstar {α : Type*} (f : ARS α) :
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
          ← ARS_npow_mul_eq_mul_npow
        ]
        use w
      | inr hypr =>
        exact hypr
    · intro hyp
      right
      exact hyp

lemma ARS_kstar_mul_le_kstar {α : Type*} (f : ARS α) :
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
lemma ARS_ban_le_bam {α : Type*} {f g : ARS α} :
  f * g ≤ f →
  ∀ (n : ℕ), f * (g^(n + 1)) ≤ f * g^n := by
    intro hyp n
    rw [
      pow_succ,
      ← ARS_npow_mul_eq_mul_npow,
      ← mul_assoc
    ]
    change f*g * g^n + f * g^n = f*g^n
    rw[
      ← right_distrib,
      hyp
    ]

-- lemme intermédiare
lemma ARS_ban_le_b {α : Type*} {f g : ARS α} :
  (∀ n, f * g^(n + 1) ≤ f * g^n) →
  ∀ n, f * g ^ n ≤ f := by
    intro hyp n
    cases n with
    | zero =>
      simp
    | succ m =>
      exact le_trans (hyp m) (ARS_ban_le_b hyp m)

-- lemme intermédiare
lemma ARS_bak_le_b {α : Type*} {f g : ARS α} :
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
lemma ARS_anb_le_amb {α : Type*} {f g : ARS α} :
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
lemma ARS_anb_le_b {α : Type*} {f g : ARS α} :
  (∀ n, g^(n + 1) * f ≤ g^n * f) →
  ∀ n, g^n * f ≤ f := by
    intro hyp n
    cases n with
    | zero =>
      simp
    | succ m =>
      exact le_trans (hyp m) (ARS_anb_le_b hyp m)

-- lemme intermédiare
lemma ARS_akb_le_b {α : Type*} {f g : ARS α} :
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

lemma ARS_mul_kstar_le_self {α : Type*} (g f : ARS α) :
  f * g ≤ f → f * g∗ ≤ f := by
    intro hyp
    exact ARS_bak_le_b (ARS_ban_le_b (ARS_ban_le_bam hyp))


lemma ARS_kstar_mul_le_self {α : Type*} (g f : ARS α) :
  g * f ≤ f → g∗ * f ≤ f := by
    intro hyp
    exact ARS_akb_le_b (ARS_anb_le_b (ARS_anb_le_amb hyp))

instance {α : Type*} : KleeneAlgebra (ARS α) where
  one_le_kstar := ARS_one_le_kstar
  mul_kstar_le_kstar := ARS_mul_kstar_le_kstar
  kstar_mul_le_kstar := ARS_kstar_mul_le_kstar
  mul_kstar_le_self := ARS_mul_kstar_le_self
  kstar_mul_le_self := ARS_kstar_mul_le_self

end KleeneAlgebra

/-
On montre quelques lemmes basiques :
- la clôture symmétrique est symétrique,
- la cloture transitive est transitive,
- …
-/

section QuelquesPreuves

lemma ARS_kstar_is_refl {α : Type*} (f : ARS α) : Reflexive f∗ := by
  intro x
  use 0
  trivial

lemma ARS_kstar_is_trans {α : Type*} (f : ARS α) : Transitive f∗ := by
  intro x y z hxy hyz
  have pnxy := hxy.choose_spec
  have pnyz := hyz.choose_spec
  use hxy.choose + hyz.choose
  rw [pow_add]
  use y

/-- La relation inverse issue d'une relation donnée -/
@[reducible]
def ARS_inverse {α : Type*} (f : ARS α) : ARS α := fun x y ↦ f y x
notation:1024 elm "⇐ " => ARS_inverse elm

@[simp] lemma ARS_inverse_involution {α : Type*} (f : ARS α) : f⇐⇐ = f := by
  ext x y
  simp

@[simp] lemma ARS_inv_one {α : Type*} : (1 : ARS α)⇐ = 1 := by
  ext x y
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    rw [h]
    rfl

@[simp] lemma ARS_symm_over_add {α : Type*} (f g : ARS α) : (f + g)⇐ = f⇐ + g⇐ := by
  ext x y
  change f y x ∨ g y x ↔ f y x ∨ g y x
  rfl

/-- La plus petite relation contenant une relation et son inverse -/
@[reducible]
def ARS_symm_closure {α : Type*} (f : ARS α) : ARS α := f + f⇐
notation:1024 elm "⇔ " => ARS_symm_closure elm

lemma ARS_symm_is_idem {α : Type*} (f : ARS α) : f⇔⇔ = f⇔ := by
  change (f + f⇐) + (f + f⇐)⇐ = f + f⇐
  simp
  rw [add_assoc]
  nth_rw 2 [← add_assoc]
  rw [ARS_addIdem]
  nth_rw 2 [add_comm]
  nth_rw 1 [← add_assoc]
  rw [ARS_addIdem] -- une fois pour f, une fois pour f⇔

lemma ARS_symm_closure_is_symm {α : Type*} (f : ARS α) : Symmetric f⇔ := by
  intro x y hxy
  cases hxy with
  | inl direct =>
    right
    exact direct
  | inr indirect =>
    left
    exact indirect

lemma ARS_inv_pow_eq_pow_inv {α : Type*} (f : ARS α) (n : ℕ): f⇐^n = (f^n)⇐ := by
  match n with
  | 0 =>
    simp
  | m + 1 =>
    rw [pow_succ, pow_succ, ← ARS_npow_mul_eq_mul_npow]
    ext x y
    constructor
    · intro hyp
      let w := hyp.choose
      have ⟨hw, hwm⟩ := hyp.choose_spec
      use w
      constructor
      · rw [← ARS_inverse_involution f, ARS_inv_pow_eq_pow_inv]
        exact hwm
      · exact hw
    · intro hyp
      let w := hyp.choose
      have ⟨hwm, hw⟩ := hyp.choose_spec
      use w
      constructor
      · exact hw
      · rw [ARS_inv_pow_eq_pow_inv]
        exact hwm

lemma ARS_inv_trans_eq_trans_inv {α : Type*} (f : ARS α) : f⇐∗ = f∗⇐ := by
  ext x y
  constructor
  · intro hyp
    use hyp.choose
    have hn := hyp.choose_spec
    rw [ARS_inv_pow_eq_pow_inv] at hn
    exact hn
  · intro hyp
    simp at hyp
    use hyp.choose
    have hn := hyp.choose_spec
    rw [ARS_inv_pow_eq_pow_inv]
    exact hn

/-- La plus petite relation d'équivalence contenant une relation -/
@[reducible]
def ARS_lubEquiv {α : Type*} (f : ARS α) : ARS α :=  f⇔∗
notation:1024 elm "≡ " => ARS_lubEquiv elm

lemma ARS_lubEquiv_is_trans {α : Type*} (f : ARS α) : Transitive f≡ :=
    ARS_kstar_is_trans f⇔

lemma ARS_lubEquiv_is_refl {α : Type*} (f : ARS α) : Reflexive f⇔∗ :=
    ARS_kstar_is_refl f⇔

lemma ARS_symm_n_is_symm {α : Type*} (f : ARS α) : ∀ n, Symmetric (f⇔^n) := by
    intro n
    cases n with
    | zero =>
      simp -- pour la lisibilité ?
      intro x y hxy
      rw [hxy]
      rfl
    | succ m =>
      rw [pow_succ]
      intro x y hxy
      let w := hxy.choose
      have hw := hxy.choose_spec
      rw [← ARS_npow_mul_eq_mul_npow]
      use w
      constructor
      · exact (ARS_symm_closure_is_symm f) hw.right
      · exact (ARS_symm_n_is_symm f m) hw.left

lemma ARS_lubEquiv_is_symm {α : Type*} (f : ARS α) : Symmetric f≡ := by
  intro x y hxy
  let n := hxy.choose
  have h := hxy.choose_spec
  use n
  exact (ARS_symm_n_is_symm f n) h

lemma ARS_symm_trans_is_equiv {α : Type*} (f : ARS α) : Equivalence f≡ where
  refl := @ARS_lubEquiv_is_refl α f
  symm := @ARS_lubEquiv_is_symm α f
  trans := @ARS_lubEquiv_is_trans α f

end QuelquesPreuves

section QuelquesProprietes

def isWeaklyCommuting {α : Type*} (f₁ f₂ : ARS α) : Prop := f₁⇐ * f₂ ≤ f₂∗ * f₁⇐∗

def isCommuting {α : Type*} (f₁ f₂ : ARS α) : Prop := f₁⇐ * f₂ ≤ f₂ * f₁⇐

def isDiamond {α : Type*} (f : ARS α) : Prop := isCommuting f f

def isChurchRosser {α : Type*} (f : ARS α) : Prop := f≡ ≤ f∗ * f⇐∗

def isConfluent {α : Type*} (f : ARS α) : Prop := f⇐∗ * f∗ ≤ f∗ * f⇐∗

def isWeaklyConfluent {α : Type*} (f : ARS α) : Prop := f⇐ * f ≤ f∗ * f⇐∗

theorem KleeneChurchRosser {K : Type*} [KleeneAlgebra K] (a b : K) :
  a∗ * b∗ ≤ b∗ * a∗ ↔ (b + a)∗ ≤ b∗ * a∗ := by
    constructor
    · intro hyp

      sorry
    · sorry

theorem ChurchRosser {α : Type*} (f : ARS α) :  isConfluent f ↔ isChurchRosser f := by
  have := KleeneChurchRosser f⇐ f
  rw [isConfluent, isChurchRosser]
  exact this

end QuelquesProprietes
