import Mathlib

/--Un alias pour le type des relations binaires sur un type  α-/
@[reducible]
def ARS (α : Type*) := α → α → Prop

@[simp]
def ARS_add {α : Type*} (f g : ARS α) : ARS α :=
  fun x y ↦ (f x y ∨ g x y)

def ARS_zero {α : Type*} : ARS α :=
  fun _ _ ↦ False

lemma ARS_add_assoc {α : Type*} (f g h : ARS α ) :
  ARS_add (ARS_add f g) h = ARS_add f (ARS_add g h) := by
    ext x y
    change (fun u v ↦ (f u v ∨ g u v) ∨ h u v) x y ↔ (fun u v ↦ f u v ∨ (g u v ∨ h u v)) x y
    simp
    rw [or_assoc]

lemma ARS_zero_add {α : Type*} (f : ARS α) :
  ARS_add ARS_zero f = f := by
    ext x y
    change False ∨ f x y ↔ f x y
    simp

lemma ARS_add_zero {α : Type*} (f : ARS α) :
  ARS_add f ARS_zero = f := by
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
lemma ARS_addIdem {α : Type*} (f : ARS α) -- nécessaire
  : ARS_add f f = f := by
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

lemma ARS_add_comm {α : Type*} (f g : ARS α) :
  ARS_add f g = ARS_add g f := by
    ext x y
    change (fun u v  ↦ f u v ∨ g u v) x y ↔ (fun u v  ↦ g u v ∨ f u v) x y
    exact or_comm

def ARS_mul {α : Type*} (f g : ARS α) : ARS α :=
  fun u v ↦ (∃ w, f u w ∧ g w v)

lemma ARS_left_distrib {α : Type*} (f g h : ARS α) :
  ARS_mul f (ARS_add g h) = ARS_add (ARS_mul f g) (ARS_mul f h) := by
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
  ARS_mul (ARS_add f g) h = ARS_add (ARS_mul f h) (ARS_mul g h) := by
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

def ARS_one {α : Type*} : ARS α :=
  (fun x y ↦ x = y)

lemma ARS_zero_mul {α : Type*} (f : ARS α) : ARS_mul ARS_zero f = ARS_zero := by
  ext x y
  constructor
  · intro hyp
    rw [ARS_mul] at hyp
    have hw := hyp.choose_spec
    exact hw.left
  · intro absu
    exfalso
    exact absu

lemma ARS_mul_zero {α : Type*} (f : ARS α) : ARS_mul f ARS_zero = ARS_zero := by
  ext x y
  constructor
  · intro hyp
    rw [ARS_mul] at hyp
    have hw := hyp.choose_spec
    exact hw.right
  · intro absu
    exfalso
    exact absu

lemma ARS_mul_assoc {α : Type*} (f g h : ARS α) :
   ARS_mul (ARS_mul f g) h = ARS_mul f (ARS_mul g h) := by
    symm
    ext x y
    constructor
    · intro hyp
      rw [ARS_mul] at hyp
      rw [ARS_mul]
      let w1 := hyp.choose
      have ⟨hw1l, hw1r⟩ := hyp.choose_spec
      rw [ARS_mul] at hw1r
      let w2 := hw1r.choose
      have ⟨hw2l, hw2r⟩ := hw1r.choose_spec
      use w2
      rw [ARS_mul]
      constructor
      · use w1
      · exact hw2r
    · rw [ARS_mul, ARS_mul]
      intro hyp
      let w1 := hyp.choose
      have ⟨hw1l, hw1r⟩ := hyp.choose_spec
      rw [ARS_mul] at hw1l
      let w2 := hw1l.choose
      have ⟨hw2l, hw2r⟩ := hw1l.choose_spec
      use w2
      constructor
      · exact hw2l
      · rw [ARS_mul]
        use w1

lemma ARS_mul_one {α : Type*} (f : ARS α) :
  ARS_mul f ARS_one = f := by
    ext x y
    rw [ARS_mul]
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
  ARS_mul ARS_one f = f := by
    ext x y
    rw [ARS_mul]
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

@[simp]
def ARS_le {α : Type*} (f g : ARS α) : Prop :=
  ARS_add f g = g

@[simp]
def ARS_lt {α : Type*} (f g : ARS α) : Prop :=
  ARS_le f g ∧ ¬ (f = g)

lemma ARS_lt_iff_le_not_le {α : Type*} (f g : ARS α) :
  ARS_lt f g ↔ ARS_le f g ∧ ¬ ARS_le g f := by
    simp
    intro add_fg
    constructor
    · intro neq_fg add_gf
      rw [ARS_add_comm, add_gf] at add_fg
      exact neq_fg add_fg
    · intro hyp neq_fg
      rw [neq_fg, ARS_addIdem] at hyp
      trivial

lemma ARS_le_refl {α : Type*} (f : ARS α) :
  ARS_le f f := by
    rw [ARS_le]
    exact ARS_addIdem f

lemma ARS_le_trans {α : Type*} (f g h : ARS α) :
  ARS_le f g → ARS_le g h → ARS_le f h := by
    repeat rw [ARS_le]
    intro add_fg add_gh
    rw [← add_gh, ← ARS_add_assoc, add_fg]

lemma ARS_le_antisymm {α : Type*} (f g : ARS α) :
  ARS_le f g → ARS_le g f → f = g := by
    repeat rw [ARS_le]
    intro add_fg add_gf
    rw [← add_fg]
    nth_rw 1 [← add_gf]
    exact ARS_add_comm g f

lemma ARS_le_sup_left {α : Type*} (f g : ARS α) :
  ARS_le f (ARS_add f g) := by
    simp
    rw [← ARS_add_assoc, ARS_addIdem]

lemma ARS_le_sup_right {α : Type*} (f g : ARS α) :
  ARS_le g (ARS_add f g) := by
    simp
    rw [ARS_add_comm, ARS_add_assoc, ARS_addIdem]

lemma ARS_sup_le {α : Type*} (f g h : ARS α) :
  ARS_le f h → ARS_le g h → ARS_le (ARS_add f g) h := by
    simp
    intro add_fh add_gh
    rw [ARS_add_assoc, add_gh, add_fh]

lemma ARS_bot_le {α : Type*} (f : ARS α) : ARS_le ARS_zero f := by
  exact ARS_zero_add f

def ARS_npow {α : Type*} (n : ℕ) (f : ARS α) :
  ARS α := by
    match n with
    | 0 => exact ARS_one
    | m + 1 => exact ARS_mul (ARS_npow m f) f

lemma ARS_npow_zero {α : Type*} (f : ARS α) :
  ARS_npow 0 f = ARS_one := by trivial

lemma ARS_npow_succ {α : Type*} (n : ℕ) (f : ARS α) :
  ARS_npow (n+1) f = ARS_mul (ARS_npow n f) f := by trivial

/-- On utilise ici le fait que le quantificateur existentiel peut être vu comme
une disjonction infinie sur le type sur lequel il quantifie : en d'autres termes,
`∃ (x : α), P x` est équivalent à `⋁ (x : α), P x`
Puisque `+` est une disjontion binaire, une somme infinie est une disjonction infinie -/
def ARS_kstar {α : Type*} (f : ARS α) :
  ARS α := fun u v ↦ ∃ n, ARS_npow n f u v

lemma ARS_one_le_kstar {α : Type*} (f : ARS α) :
  ARS_le ARS_one (ARS_kstar f) := by
    ext x y
    constructor
    · intro hyp
      cases hyp with
      | inl l =>
        use 0
        rw [ARS_npow_zero]
        exact l
      | inr r => exact r
    · intro hyp
      right
      exact hyp

/- On a f^n f = f f^n, par récurrence -/
-- lemme intermédiare
lemma ARS_npow_mul_eq_mul_npow {α : Type*} (n : ℕ) (f : ARS α) :
  ARS_mul f (ARS_npow n f) = ARS_mul (ARS_npow n f) f := by
    match n with
    | 0 => rw [ARS_npow_zero, ARS_one_mul, ARS_mul_one]
    | m + 1 =>
      rw [ARS_npow_succ, ← ARS_mul_assoc]
      nth_rw 1 [← ARS_npow_mul_eq_mul_npow]

lemma ARS_mul_kstar_le_kstar {α : Type*} (f : ARS α) :
  ARS_le (ARS_mul f (ARS_kstar f)) (ARS_kstar f) := by
    change ARS_add (ARS_mul f (ARS_kstar f)) (ARS_kstar f) = ARS_kstar f
    nth_rw 2 [← ARS_one_mul (ARS_kstar f)]
    rw [
      ← ARS_right_distrib f ARS_one (ARS_kstar f),
      ARS_add_comm,
      ]
    ext x y
    constructor
    · intro hyp
      let w := hyp.choose
      have ⟨hwl, hwr⟩ := hyp.choose_spec
      let n := hwr.choose
      have hn := hwr.choose_spec
      cases hwl with
      | inl l =>
        rw [l]
        exact hwr
      | inr r =>
        use n + 1
        rw [ARS_npow_succ, ← ARS_npow_mul_eq_mul_npow]
        use w
    · intro hyp
      let n := hyp.choose
      have hn := hyp.choose_spec
      use x
      constructor
      · left
        rfl
      · use n

lemma ARS_kstar_mul_le_kstar {α : Type*} (f : ARS α) :
  ARS_le (ARS_mul (ARS_kstar f) f) (ARS_kstar f) := by
    change ARS_add (ARS_mul (ARS_kstar f) f) (ARS_kstar f) = ARS_kstar f
    nth_rw 2 [← ARS_mul_one (ARS_kstar f)]
    rw [
      ← ARS_left_distrib (ARS_kstar f) f ARS_one,
      ARS_add_comm,
      ]
    ext x y
    constructor
    · intro hyp
      let w := hyp.choose
      have ⟨hwl, hwr⟩ := hyp.choose_spec
      let n := hwl.choose
      have hn := hwl.choose_spec
      cases hwr with
      | inl l =>
        use n
        rw [← l]
        exact hn
      | inr r =>
        use n + 1
        rw [ARS_npow_succ]
        use w
    · intro hyp
      let n := hyp.choose
      have hn := hyp.choose_spec
      use y
      constructor
      · use n
      · left
        rfl

-- lemme intermédiare
lemma ARS_ban_le_bam {α : Type*} {f g : ARS α} :
  ARS_le (ARS_mul f g) f →
  ∀ (n : ℕ), ARS_le (ARS_mul f (ARS_npow (n + 1) g)) (ARS_mul f (ARS_npow (n ) g)) := by
    simp
    intro hyp n
    rw [
      ARS_npow_succ,
      ← ARS_npow_mul_eq_mul_npow n g,
      ← ARS_mul_assoc,
      ← ARS_right_distrib,
      hyp
    ]

-- lemme intermédiare
lemma ARS_ban_le_b {α : Type*} {f g : ARS α} :
  (∀ n, ARS_le (ARS_mul f (ARS_npow (n + 1) g)) (ARS_mul f (ARS_npow n g))) →
  ∀ n, ARS_le (ARS_mul f (ARS_npow n g)) f := by
    intro hyp n
    induction n with
    | zero =>
      rw [
        ARS_npow,
        ARS_mul_one,
      ]
      exact ARS_le_refl f
    | succ m hn =>
      exact ARS_le_trans
        (ARS_mul f (ARS_npow (m + 1) g)) (ARS_mul f (ARS_npow m g)) f
        (hyp m) hn

-- lemme intermédiare
lemma ARS_bak_le_b {α : Type*} {f g : ARS α} :
  (∀ (n : ℕ), ARS_le (ARS_mul f (ARS_npow n g)) f) →
  ARS_le (ARS_mul f (ARS_kstar g)) f := by
    simp
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

lemma ARS_mul_kstar_le_self {α : Type*} (g f : ARS α) :
  ARS_le (ARS_mul f g) f → ARS_le (ARS_mul f (ARS_kstar g)) f := by
    intro hyp
    exact ARS_bak_le_b (ARS_ban_le_b (ARS_ban_le_bam hyp))

-- lemme intermédiare
lemma ARS_anb_le_amb {α : Type*} {f g : ARS α} :
  ARS_le (ARS_mul g f) f →
  ∀ (n : ℕ), ARS_le (ARS_mul (ARS_npow (n + 1) g) f) (ARS_mul (ARS_npow (n ) g) f) := by
    simp
    intro hyp n
    rw [
      ARS_npow_succ,
      ARS_mul_assoc,
      ← ARS_left_distrib,
      hyp
    ]

-- lemme intermédiare
lemma ARS_anb_le_b {α : Type*} {f g : ARS α} :
  (∀ n, ARS_le (ARS_mul (ARS_npow (n + 1) g) f) (ARS_mul (ARS_npow n g) f)) →
  ∀ n, ARS_le (ARS_mul (ARS_npow n g) f) f := by
    intro hyp n
    induction n with
    | zero =>
      rw [
        ARS_npow,
        ARS_one_mul,
      ]
      exact ARS_le_refl f
    | succ m hn =>
      exact ARS_le_trans
        (ARS_mul (ARS_npow (m + 1) g) f) (ARS_mul (ARS_npow m g) f) f
         (hyp m) hn

-- lemme intermédiare
lemma ARS_akb_le_b {α : Type*} {f g : ARS α} :
  (∀ (n : ℕ), ARS_le (ARS_mul (ARS_npow n g) f) f) →
  ARS_le (ARS_mul (ARS_kstar g) f) f := by
    simp
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

lemma ARS_kstar_mul_le_self {α : Type*} (g f : ARS α) :
  ARS_le (ARS_mul g f) f → ARS_le (ARS_mul (ARS_kstar g) f) f := by
    intro hyp
    exact ARS_akb_le_b (ARS_anb_le_b (ARS_anb_le_amb hyp))


instance ARSisKleeneAlgebra {α : Type*} : KleeneAlgebra (ARS α) where
  add := ARS_add
  zero := ARS_zero
  add_assoc := ARS_add_assoc
  zero_add := ARS_zero_add
  add_zero := ARS_add_zero
  nsmul := ARS_nsmul
  nsmul_succ := ARS_nsmul_succ
  add_comm := ARS_add_comm
  mul := ARS_mul
  left_distrib := ARS_left_distrib
  right_distrib := ARS_right_distrib
  zero_mul := ARS_zero_mul
  mul_zero := ARS_mul_zero
  mul_assoc := ARS_mul_assoc
  one := ARS_one
  one_mul := ARS_one_mul
  mul_one := ARS_mul_one
  le := ARS_le
  lt := ARS_lt
  le_refl := ARS_le_refl
  le_trans := ARS_le_trans
  lt_iff_le_not_le := ARS_lt_iff_le_not_le
  le_antisymm := ARS_le_antisymm
  sup := ARS_add -- il faut toujours que `⊔` et `+` soient égaux
  le_sup_left := ARS_le_sup_left
  le_sup_right := ARS_le_sup_right
  sup_le := ARS_sup_le
  bot_le := ARS_bot_le
  npow := ARS_npow
  kstar := ARS_kstar
  one_le_kstar := ARS_one_le_kstar
  mul_kstar_le_kstar := ARS_mul_kstar_le_kstar
  kstar_mul_le_kstar := ARS_kstar_mul_le_kstar
  mul_kstar_le_self := ARS_mul_kstar_le_self
  kstar_mul_le_self := ARS_kstar_mul_le_self


/-
#print KleeneAlgebra
#print IdemSemiring
#print SemilatticeSup
#print PartialOrder
#print Preorder
-/
