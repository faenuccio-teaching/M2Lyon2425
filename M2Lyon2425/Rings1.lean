/-
  ## Rings, fields, polynomials and linear algebra 1
  Credits.
  * Formalising Mathematics 2022 - 2024, K. Buzzard
  * Mathematics in Lean, J. Avigad, P. Massot
  * The Mechanics of Proof, H. Macbeth
-/
import Mathlib.Tactic.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Data.Real.Basic

/-
  # Modified operations
  Operations are defined on types so that have to be defined for all values.
  Therefore, it is sometimes necessary to ``extend'' the existing definitions.
-/

example : (5 : ℕ) - 3 = 2 := by
  sorry

example : (1 : ℕ) - 3 = 0 :=  by
  sorry

example : (2 : ℝ) / 2 = 1 := by
  sorry

example : (2 : ℝ) / 0 = 0 := by
  sorry

-- This result is false
example (a b : ℕ) : a - b + b = a := by
  sorry

example (a b : ℕ) (h : b ≤ a) : a - b + b = a := by
  sorry

-- This result is false
example (a b : ℝ) : a * (a⁻¹ * b) = b := by
  sorry

example (a b : ℝ) (h : a ≠ 0): a * (a⁻¹ * b) = b := by
  sorry

/-
  # All flavors of rings
  The type of rings is `Ring` and `CommRing` for commutative rings but it is possible to define many kind of rings
-/

-- This result is false
example {R : Type*} [Ring R] (a b : R) : a * b = b * a := by
  sorry

example {R : Type*} [CommRing R] (a b : R) : a * b = b * a := by
  sorry

-- Integral domain
class integralDomain (R : Type*) extends CommRing R, IsDomain R

example : integralDomain ℤ := by
  sorry

-- Principal ideal domain
class PID (R : Type*) extends CommRing R, IsDomain R, IsPrincipalIdealRing R

example : PID ℤ := by
  sorry

-- Unique factorization domain
class UFD (R : Type*) extends CommRing R, IsDomain R, UniqueFactorizationMonoid R

example : UFD ℤ := by
  sorry

-- GCD domain
class GCDdomain (R : Type*) extends CommRing R, IsDomain R, GCDMonoid R

example : GCDdomain ℤ := by
  sorry

-- Integrally closed domain
class ICR (R : Type*) extends CommRing R, IsIntegralClosure R R (FractionRing R)

example : ICR ℤ := by
  sorry

-- However, defining classes like above is not a good idea since they carry data and it is
-- better to use mixin to avoid diamonds. For example, assume we want to work with a ring that is
-- both a ICR and a GCDdomain

variable (R₁ : Type*) [ICR R₁] [GCDdomain R₁]

-- Does not work
example (a b : R₁) : gcd a b ∣ a :=
  sorry

variable (R : Type*) [CommRing R] [IsIntegralClosure R R (FractionRing R)] [IsDomain R] [GCDMonoid R]

example (a b : R) : gcd a b ∣ a := by
  sorry

-- It is also possible to not require addition to form a group (only a monoid) in this case, we
-- have the classes `Semiring` and `CommSemiRing`

#synth CommSemiring ℕ

-- The `ring` tactic is used to prove symbolic expression using ring operations.
-- It requires a `CommRing`

example (R : Type*) [CommRing R] (a b : R) :
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
  ring

-- This result is false
example (R : Type*) [Ring R] (a b : R) :
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
  ring -- does nothing
  sorry

/-
  # Subgroup of units
-/

variable {R : Type*} [Ring R]

-- Fails
example (a : R) : a* a⁻¹ = 1 := sorry

-- Every ring (in fact, monoid) `R` comes with a function `IsUnit : R → Prop` asserting the
-- existence of inverses on both sides (since `R` may not be commutative).

-- Still fails
example (a : R) (ha : IsUnit a) : a * a⁻¹ = 1 := sorry

-- The type of units of `R` is denoted `Rˣ` (use `R\^x` to write `Rˣ`). it is a group

#synth Group Rˣ

example (a : Rˣ) : a * a⁻¹ = 1 := by
  sorry

-- There is a coercion for `Rˣ` to `R` and an element of `a : R` that satisfies `ha : IsUnit a`
-- can be promoted to a unit of `R`

example (a : Rˣ) (b : R) : a * b = a ^ 2 * a⁻¹ * b := by
  sorry

example (a : R) (ha : IsUnit a) : a * ha.unit⁻¹ = 1 := by
  sorry

example (x : ℤˣ) : x = 1 ∨ x = -1 := by
  sorry

/-
  # Morphisms between rings
  The type of morphisms between two rings `R` and `S` is `RingHom R S` denoted `R →+* S`.
  The type of isomorphisms between two rings `R` and `S` is `RingEquiv R S` denoted `R ≃+* S`.
-/

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) :
    f (a + b) = f a + f b := by
  sorry

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) :
    f (a * b) = f a * f b := by
  sorry

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x : R) (hx : IsUnit x) : IsUnit (f x) := by
  sorry

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ := by
  sorry

/-
  # Ideals and quotients
  The theory of ideals in Mathlib has only been developed in the case of commutative rings
  for historical reason, so we will only focus on this case.
  The type of ideal of `R` is defined as `Submodule R R` (see the linear algebra section).
-/

variable (R : Type*) [CommRing R] (I J : Ideal R)

-- Mathlib knows about the addition and multiplication of ideals and the corresponding properties

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  sorry

example : I * J ≤ J := by
  sorry

example : I * J ≤ I := by
  sorry

-- Note that the ideals form a complete lattice for the inclusion. In particular, the LUB
-- (least upper bound) of two ideals is their sum and the GLB (greatest lower bound) is the
-- intersection

example : I ⊔ J = I + J := by -- use `\lub` to write `⊔`
  sorry

example : I ⊓ J = (I : Set R) ∩ (J : Set R) := by  -- use `\glb` to write `⊓`
  sorry

-- An ideal is principal if it is principal as a `Submodule` that is it satisfies
-- `Submodule.IsPrincipal`. Since an ideal `I` is by definition a submodule, we can still use
-- the `.` notation.

example (hI : I.IsPrincipal) : ∃ a, I = Submodule.span R { a } := by
  sorry

-- A PID is a ring in which all ideals are principal
example [IsPrincipalIdealRing R] : I.IsPrincipal := by
  sorry

-- The quotient of a ring by an ideal is defined. it is also a commutative ring
#synth CommRing (R ⧸ I) -- use `\quo` to write `⧸`

-- It comes with the natural morphism from `R` to `R⧸I`
example : R →+* (R ⧸ I) := Ideal.Quotient.mk I

example (a : R) : Ideal.Quotient.mk I a = 0 ↔ a ∈ I := by
  sorry

example (S : Type*) [CommRing S] (f : R →+* S) (h : I ≤ RingHom.ker f) :
    R ⧸ I →+* S := by
  sorry

-- The first isomorphism
example (S : Type*) [CommRing S] (f : R →+* S) :
    R ⧸ RingHom.ker f ≃+* RingHom.range f := by
  sorry

/-
  # Digression: quotient in Lean / Mathlib
-/

-- Quotient in Lean are defined using a setoid, that is a type equipped with an equivalence relation

variable (α : Type*) (r : α → α → Prop)

example :
    Equivalence r ↔ (∀ x, r x x) ∧ (∀ x y, r x y → r y x) ∧ (∀ x y z, r x y → r y z → r x z) := by
  refine ⟨fun h ↦ ⟨h.1, ?_, ?_⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, ?_, ?_⟩⟩
  all_goals sorry

example (h : Equivalence r) : Setoid α := ⟨r, h⟩

-- The quotient of `α` by the setoid `s`is called `Quotient s`, it comes with the
-- natural map `Quotient.mk s` from `α` to `Q`

example (s : Setoid α) : α → Quotient s := Quotient.mk s

-- The Quotient axiom `Quot.sound` then says that if two elements are in relation then their classes
-- in the quotient are equal
example (a b : α) (s : Setoid α) (h : a ≈ b) : -- (Use `\~~` to write `≈`)
    Quotient.mk s a = Quotient.mk s b := Quotient.sound h

-- Note that the quotient and the quotient map comes in three different versions: `Quotient.mk`,
-- `Quotient.mk'` and `Quotient.mk''` depending (respectively) if the setoid is given as an
-- argument, should be inferred by typeclass inference or is given as an implicit argument.

-- If `I` is an ideal of `R`, then there is an equivalence relation and thus a setoid of `R`
-- constructed from it (in fact, it is constructed for submodules) and Lean can infer from that
-- the quotient `R ⧸ I`.

/-
  # Let's construct our own version of `ℤ`
  We will prove the following result: The ring `ℤ` is isomorphic to the quotient of `ℕ × ℕ`
  by the equivalence relation `(a, b) ≈ (c, d)` iff `a + d = c + b`.
  The ideal being that the class of `(a,b)` corresponds to the integer `a - b`.
-/

noncomputable section

def rZ : ℕ × ℕ → ℕ × ℕ → Prop := fun (a, b) (c, d) ↦ a + d = c + b

theorem rZ_iff (a b c d : ℕ) : rZ (a, b) (c, d) ↔ a + d = c + b := by
  rw [rZ]

theorem rZ_iff' (x y : ℕ × ℕ) : rZ x y ↔ x.1 + y.2 = y.1 + x.2 := by
  rw [rZ]

theorem rZ_reflexive : Reflexive rZ := by
  sorry

theorem rZ_symmetric : Symmetric rZ := by
  sorry

theorem rZ_transitive : Transitive rZ := by
  sorry

-- We make an instance so we don't have to precise the setoid every time
instance rZSetoid : Setoid (ℕ × ℕ) := by
  refine ⟨rZ, ?_, ?_, ?_⟩
  sorry
  sorry
  sorry

-- Note: try to remove the `by`
example (x y : ℕ × ℕ) : x ≈ y ↔ rZ x y := by rfl

-- Some useful API
@[simp]
theorem rZSetoid_apply (x y : ℕ × ℕ) : rZSetoid.Rel x y ↔ x.1 + y.2 = y.1 + x.2 := by rfl

@[simp]
theorem rZ_equiv_def (a b c d : ℕ) : (a, b) ≈ (c, d) ↔ a + d = c + b := by rfl

-- We can now define our own version of `ℤ`
abbrev ZZ := Quotient rZSetoid

-- Now, we want to give a ring structure on `ZZ`
-- There are a lot of fields to fill in in the class definition of `Ring`, so we want to use some
-- shortcuts. The idea is to construct the structure on `ZZ` step by step.

namespace ZZ

-- First, we define `0` and `1` elements of `ZZ` and tell Lean about them

-- `⟦x⟧` is the notation for `Quotient.mk'`
def zero : ZZ := ⟦(0,0)⟧ -- Use `\[[` and `\]]` to write `⟦⟧`

def one : ZZ := ⟦(1,0)⟧

instance : Zero ZZ := ⟨zero⟩

instance : One ZZ := ⟨one⟩

-- Let's add some more API

@[simp]
theorem zero_def : (0 : ZZ) = ⟦(0,0)⟧ := rfl

@[simp]
theorem one_def : (1 : ZZ) = ⟦(1,0)⟧ := rfl

-- Now, we define the negation of `ZZ`. The way to define a map on a quotient is the following: we
-- define a map `ℕ × ℕ → ZZ`, we prove that this function is constant on equivalence classes and then
-- we use the `Quotient.lift` function to construct a function `ZZ → ZZ` from it.

def neg_aux (x : ℕ × ℕ) : ZZ := ⟦(x.2, x.1)⟧

def neg : ZZ → ZZ := by
  refine Quotient.lift neg_aux fun x y h ↦ ?_
  rw [neg_aux, neg_aux, Quotient.eq] -- Note the use of the function `Quotient.eq`
  sorry

instance : Neg ZZ := ⟨neg⟩

@[simp]
theorem neg_def (a b : ℕ) : (- ⟦(a, b)⟧ : ZZ) = ⟦(b, a)⟧ := rfl

-- Now, we define an addition on `ZZ` using the same process

def add_aux (x y : ℕ × ℕ) : ZZ := ⟦(x.1 + y.1, x.2 + y.2)⟧

def add : ZZ → ZZ → ZZ := by
  apply Quotient.lift₂ add_aux  -- Note the use of `Quotient.lift₂`
  intro x₁ x₂ y₁ y₂ h₁ h₂
  sorry

instance : Add ZZ := ⟨add⟩

@[simp]
theorem add_def (a b c d : ℕ) : (⟦(a, b)⟧ + ⟦(c, d)⟧ : ZZ) = ⟦(a + c, b + d)⟧ := rfl

-- Defining subtraction is now direct

def sub (x y : ZZ) : ZZ := x + -y

instance : Sub ZZ := ⟨sub⟩

-- Okay, so we have enough to prove that `ZZ` is a `AddCommGroup`.

-- We need this to prevent Lean from changing `(0,0)` to `(0)`
attribute [-simp] Prod.mk_zero_zero

instance addCommGroup : AddCommGroup ZZ where
  zero := 0
  add := (· + ·)
  neg := neg
  sub := sub
  nsmul := nsmulRec -- This is generated automatically
  zsmul := zsmulRec -- This is generated automatically
  -- To prove the results, we need to get back to the definition as quotient using
  -- the function `Quotient.inductionOn` and its variants
  zero_add := by
    intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨a, b⟩
    simp
  add_zero := sorry
  add_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    sorry
  add_assoc := by
    sorry
  neg_add_cancel := by
    intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨a, b⟩
    simp
    ring

-- The next step is to define the multiplication on `ZZ`. We use a different approach.
-- We first define it as a map `ℕ × ℕ → ℕ × ℕ → ℕ × ℕ` and then use `Quotient.map₂` to
-- construct the quotient map on `ZZ → ZZ → ZZ`.

def mul_aux (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

def mul : ZZ → ZZ → ZZ := by
  refine Quotient.map₂ mul_aux ?_
  intro x y hxy w z hwz
  rw [rZ_equiv_def] at hxy hwz
  rw [mul_aux, mul_aux, rZ_equiv_def]
  nlinarith -- The `magic` tactic that makes everything works

instance : Mul ZZ := ⟨mul⟩

@[simp]
theorem mul_def (a b c d : ℕ) :
    (⟦(a, b)⟧ * ⟦(c, d)⟧ : ZZ) = ⟦(a * c + b * d, a * d + b * c)⟧ := rfl

-- Finally, we get the ring structure

instance commRing : CommRing ZZ where
  mul_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    simp
    ring
  left_distrib := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    simp
    ring
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  one_mul := sorry
  mul_one := sorry
  mul_comm := sorry
  zsmul := zsmulRec -- I don't know why we need to define this again...
  neg_add_cancel := neg_add_cancel -- I don't know why we need to define this again...

-- The final step is to prove that `ZZ` and `ℤ` are isomorphic

def N2Z (x : ℕ × ℕ) : ℤ := x.1 - x.2

#print N2Z

theorem N2Z_surjective : Function.Surjective N2Z := by
  sorry

-- A function `f` define a setoid with the relation : `x ≈ y ↔ f x = f y`.
-- It is called `Setoid.ker`. We prove that the setoid `rZSetoid` is equal to `Setoid.ker N2Z`.
theorem setoid_eq_setoid : rZSetoid = Setoid.ker N2Z := by
  rw [Setoid.eq_iff_rel_eq]
  ext x y
  rw [rZSetoid_apply, Setoid.ker_def, N2Z, N2Z, sub_eq_sub_iff_add_eq_add, ← Nat.cast_add,
    ← Nat.cast_add, Nat.cast_inj]

-- We construct an equiv between `ZZ` and `ℤ` in several steps

def equiv₁ : ZZ ≃ Quotient (Setoid.ker N2Z) := by
  apply Quotient.congrRight
  intro _ _
  rw [setoid_eq_setoid]

@[simp]
theorem equiv₁_apply (x : ℕ × ℕ) : equiv₁ ⟦x⟧ = ⟦x⟧ := rfl

-- The first isomorphism theorem for sets: the quotient by the kernel of a function f bijects
-- with the image of f.
def equiv₂ : Quotient (Setoid.ker N2Z) ≃ (Set.range N2Z) := Setoid.quotientKerEquivRange N2Z

@[simp]
theorem equiv₂_apply (x : ℕ × ℕ) : equiv₂ ⟦x⟧ = ⟨x.1 - x.2, N2Z_surjective _⟩ := rfl

def equiv₃ : (Set.range N2Z) ≃ ℤ := by
  refine Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, ?_⟩
  intro x
  exact ⟨⟨x, N2Z_surjective x⟩, rfl⟩

@[simp]
theorem equiv₃_apply (z : ℤ) (hz : z ∈ Set.range N2Z) : equiv₃ ⟨z, hz⟩ = z := rfl

def equiv : ZZ ≃ ℤ := equiv₁.trans (equiv₂.trans equiv₃)

-- Some API
@[simp]
theorem equiv_apply (x : ℕ × ℕ) : equiv ⟦x⟧ = x.1 - x.2 := rfl

-- Finally, we construct an `RingEquiv` from this `Equiv`
def ringEquiv : ZZ ≃+* ℤ where
  toFun := equiv
  invFun := equiv.symm
  left_inv := equiv.leftInverse_symm
  right_inv := equiv.rightInverse_symm
  map_add' := sorry
  map_mul' := sorry

theorem ringEquiv_apply (x : ℕ × ℕ) : ringEquiv ⟦x⟧ = x.1 - x.2 := rfl

-- Can you fill in the following statement and proof?
theorem ringEquiv_apply_symm (z : ℤ) : ringEquiv.symm z = sorry := sorry
