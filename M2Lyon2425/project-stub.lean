import Mathlib


/-
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Int
-/

-- def ARS (α : Type*) := α → α → Prop

def ARS_add {α : Type*} (f g : α → α → Prop) : α → α → Prop :=
  fun x y ↦ (f x y ∨ g x y)

def ARS_zero {α : Type*} : α → α → Prop :=
  fun _ _ ↦ False

lemma ARS_add_assoc {α : Type*} (f g h : α → α → Prop) :
  ARS_add (ARS_add f g) h = ARS_add f (ARS_add g h) := by
    ext x y
    change (fun u v ↦ (f u v ∨ g u v) ∨ h u v) x y ↔ (fun u v ↦ f u v ∨ (g u v ∨ h u v)) x y
    simp
    rw [or_assoc]

lemma ARS_zero_add {α : Type*} (f : α → α → Prop) :
  ARS_add ARS_zero f = f := by
    ext x y
    change False ∨ f x y ↔ f x y
    simp

lemma ARS_add_zero {α : Type*} (f : α → α → Prop) :
  ARS_add f ARS_zero = f := by
    ext x y
    change f x y ∨ False ↔ f x y
    simp

def ARS_nsmul {α : Type*} (n : ℕ) (f : α → α → Prop) : α → α → Prop := by -- nécessaire
  cases n with
  | zero => exact ARS_zero
  | succ m => exact f

lemma ARS_nsmul_succ_succ {α : Type*} (n : ℕ) (f : α → α → Prop) -- nécessaire
  : ARS_nsmul (n + 1) f = f := by
    trivial

lemma ARS_addIdem {α : Type*} (f : α → α → Prop) -- nécessaire
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

lemma ARS_nsmul_succ_zero {α : Type*} (f : α → α → Prop) -- nécessaire
  : ARS_nsmul 0 f = ARS_zero := by
    trivial

lemma ARS_nsmul_succ {α : Type*} (n : ℕ ) (f : α → α → Prop) :
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

lemma ARS_add_comm {α : Type*} (f g : α → α → Prop) :
  ARS_add f g = ARS_add g f := by
    ext x y
    change (fun u v  ↦ f u v ∨ g u v) x y ↔ (fun u v  ↦ g u v ∨ f u v) x y
    exact or_comm

def ARS_mul {α : Type*} (f g : α → α → Prop) : α → α → Prop :=
  fun u v ↦ (∃ w, f u w ∧ g w v)

lemma ARS_left_distrib {α : Type*} (f g h : α → α → Prop) :
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

lemma ARS_right_distrib {α : Type*} (f g h : α → α → Prop) :
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

def ARS_one {α : Type*} : α → α → Prop :=
  (fun x y ↦ x = y)

lemma ARS_zero_mul {α : Type*} (f : α → α → Prop) : ARS_mul ARS_zero f = ARS_zero := by
  ext x y
  constructor
  · intro hyp
    rw [ARS_mul] at hyp
    have hw := hyp.choose_spec
    exact hw.left
  · intro absu
    exfalso
    exact absu

lemma ARS_mul_zero {α : Type*} (f : α → α → Prop) : ARS_mul f ARS_zero = ARS_zero := by
  ext x y
  constructor
  · intro hyp
    rw [ARS_mul] at hyp
    have hw := hyp.choose_spec
    exact hw.right
  · intro absu
    exfalso
    exact absu

lemma ARS_mul_assoc {α : Type*} (f g h : α → α → Prop) :
  ARS_mul f (ARS_mul g h) = ARS_mul (ARS_mul f g) h := by
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

lemma ARS_mul_one {α : Type*} (f : α → α → Prop) :
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

lemma ARS_one_mul {α : Type*} (f : α → α → Prop) :
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
def ARS_le {α : Type*} (f g : α → α → Prop) : Prop :=
  ARS_add f g = g

@[simp]
def ARS_lt {α : Type*} (f g : α → α → Prop) : Prop :=
  ARS_le f g ∧ ¬ (f = g)

lemma ARS_lt_iff_le_not_le {α : Type*} (f g : α → α → Prop) :
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


lemma ARS_le_refl {α : Type*} (f : α → α → Prop) :
  ARS_le f f := by
    rw [ARS_le]
    exact ARS_addIdem f

lemma ARS_le_trans {α : Type*} (f g h : α → α → Prop) :
  ARS_le f g → ARS_le g h → ARS_le f h := by
    repeat rw [ARS_le]
    intro add_fg add_gh
    rw [← add_gh, ← ARS_add_assoc, add_fg]

lemma ARS_le_antisymm {α : Type*} (f g : α → α → Prop) :
  ARS_le f g → ARS_le g f → f = g := by
    repeat rw [ARS_le]
    intro add_fg add_gf
    rw [← add_fg]
    nth_rw 1 [← add_gf]
    exact ARS_add_comm g f

lemma ARS_le_sup_left {α : Type*} (f g : α → α → Prop) :
  ARS_le f (ARS_add f g) := by
    simp
    rw [← ARS_add_assoc, ARS_addIdem]

lemma ARS_le_sup_right {α : Type*} (f g : α → α → Prop) :
  ARS_le g (ARS_add f g) := by
    simp
    rw [ARS_add_comm, ARS_add_assoc, ARS_addIdem]

lemma ARS_sup_le {α : Type*} (f g h : α → α → Prop) :
  ARS_le f h → ARS_le g h → ARS_le (ARS_add f g) h := by
    simp
    intro add_fh add_gh
    rw [ARS_add_assoc, add_gh, add_fh]


lemma ARS_bot_le {α : Type*} (f : α → α → Prop) : ARS_le ARS_zero f := by
  exact ARS_zero_add f

-- #synth (AddMonoid (ℕ → ℕ → Prop))
-- il n'y a pas de struture de monoïde idempotent sur les relations binaires d'un type

#print KleeneAlgebra


instance ARS {α : Type*} : KleeneAlgebra (α → α → Prop) where
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
  mul_assoc f g h := by symm; exact ARS_mul_assoc f g h
  one := ARS_one
  one_mul := ARS_one_mul
  mul_one := ARS_mul_one
  le := ARS_le
  lt := ARS_lt
  le_refl := ARS_le_refl
  le_trans := ARS_le_trans
  lt_iff_le_not_le := ARS_lt_iff_le_not_le
  le_antisymm := ARS_le_antisymm
  sup := ARS_add -- il faut toujours que ⊔ et + soient égaux
  le_sup_left := ARS_le_sup_left
  le_sup_right := ARS_le_sup_right
  sup_le := ARS_sup_le
  bot_le := sorry
  kstar := sorry
  one_le_kstar := sorry
  mul_kstar_le_kstar := sorry
  kstar_mul_le_kstar := sorry
  mul_kstar_le_self := sorry
  kstar_mul_le_self := sorry

#check KleeneAlgebra.one_le_kstar

#print KleeneAlgebra
#print IdemSemiring
#print SemilatticeSup
#print PartialOrder
#print Preorder
