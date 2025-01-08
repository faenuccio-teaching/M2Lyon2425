/-
  ## Structures
  Credits.
  * Mathematics in Lean, J. Avigad, P. Massot
-/
import Mathlib.Algebra.BigOperators.Ring

-- The following class records that the given type `α` is endowed with a distinguished element
-- called one. At this stage, it has no property at all.
class One₁ (α : Type*) where
  /-- The element one -/
  one : α

-- The class command above defines a structure One₁ with parameter `α : Type` and
-- a single field one. It also mark this structure as a class so that arguments of type
-- `One₁ α` for some type `α` will be inferrable using the instance resolution procedure.

#check One₁.one

-- The structure command with class attribute does the same thing except that
-- the class command also ensures that `One₁ α` appears as an instance-implicit argument
-- in its own fields

@[class] structure One₂ (α : Type*) where
  /-- The element one -/
  one : α

#check One₂.one

example (α : Type*) [One₁ α] : α := One₁.one

-- Lean cannot figure out what is the type of the output

example (α : Type*) [One₁ α] := One₁.one

-- Given the type explicitly fixes the issue

example (α : Type*) [One₁ α] := (One₁.one : α)

example (α : Type*) (h : One₂ α) : α := h.one

-- We assign a notation to `One₁.one`. Since we don’t want collisions with the builtin
-- notation for `1`, we will use `𝟙`.

@[inherit_doc]
notation "𝟙" => One₁.one -- Use `\b1` to write `𝟙`

example {α : Type*} [One₁ α] : α := 𝟙

example {α : Type*} [One₁ α] : (𝟙 : α) = 𝟙 := rfl

--  Now, we define a data-carrying class recording a binary operation

class Dia₁ (α : Type*) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia -- Use `\diamond` to write `⋄`

-- As in the `One₁` example, the operation has no property at all at this stage.
-- We define the class of semigroup structures where the operation is denoted by `⋄`.
-- For now, we define it by hand as a structure with two fields, a `Dia₁` instance and
-- some Prop-valued field `dia_assoc` asserting associativity of `⋄`.

class Semigroup₁ (α : Type*) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, (a ⋄ b) ⋄ c = a ⋄ (b ⋄ c)

-- While stating `dia_assoc`, the previously defined field `toDia₁` is in the local context
-- hence can be used when Lean searches for an instance of `Dia₁ α` to make sense of `a ⋄ b`.
-- However it is not part of the type class instances database.

example {α : Type*} [Semigroup₁ α] (a b : α) : α := a ⋄ b

-- We fix this by adding the instance attribute.

attribute [instance] Semigroup₁.toDia₁

example {α : Type*} [Semigroup₁ α] (a b : α) : α := a ⋄ b

-- A more convenient way to extend structures than explicitly writing fields by hand and
-- adding attribute is to use the `extends`.

class Semigroup₂ (α : Type*) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, (a ⋄ b) ⋄ c = a ⋄ (b ⋄ c)

-- Lean can automatically infer the operation of `α`.

example {α : Type*} [Semigroup₂ α] (a b : α) : α := a ⋄ b

-- We combine a diamond operation and a distinguished one with axioms saying this element
-- is neutral on both sides.

class DiaOneClass₁ (α : Type*) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- To see how Lean finds those instances we set a tracing option whose result can be
-- seen in the Infoview.

set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙

-- We don’t need to include extra fields where combining existing classes.
-- Hence we can define monoids as:

class Monoid₁ (α : Type*) extends Semigroup₁ α, DiaOneClass₁ α

-- If we try to build a monoid class by hand, we get two completely unrelated diamond operations

class Monoid₂ (α : Type*) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

example {α : Type*} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl

#check Monoid₂.mk

-- Indeed, we see that `Monoid₁` takes `Semigroup₁ α` argument as expected but then it won’t take a
-- would-be overlapping `DiaOneClass₁ α` argument but instead tears it apart and includes only
-- the non-overlapping parts. And it also auto-generated an instance `Monoid₁.toDiaOneClass₁`.

#check Monoid₁.mk

#check Monoid₁.toSemigroup₁

#check Monoid₁.toDiaOneClass₁

example  {α : Type*} [Monoid₁ α] (a : α) : 𝟙 ⋄ a = a := by exact DiaOneClass₁.one_dia a

example  {α : Type*} [Monoid₂ α] (a : α) : 𝟙 ⋄ a = a := by exact?

-- We are now very close to defining groups. We could add to the monoid structure a field asserting
-- the existence of an inverse for every element. But then we would need to work to access these inverses.
-- In practice it is more convenient to add it as data.

-- To optimize reusability, we define a new data-carrying class, and then give it some notation.

class Inv₁ (α : Type*) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type*) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙

-- Note that we only ask that `a⁻¹` is a left-inverse of `a` since the other side is automatic.
-- In order to prove that, we need a preliminary lemma.

#check DiaOneClass₁.one_dia
#check Semigroup₁.dia_assoc

lemma left_inv_eq_right_inv₁ {M : Type*} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) :
    b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one]

-- It is pretty annoying to give full names of the lemma. One way to fix this is to use the export
-- command to copy those facts as lemmas in the root name space.

export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)

-- Then we can rewrite the proof.

example {M : Type*} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
   rw [← one_dia c, ← hba, dia_assoc, hac, dia_one]

-- Now, let's prove things about our algebraic structures.

lemma inv_eq_of_dia {G : Type*} [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b := by
  refine left_inv_eq_right_inv₁ ?_ h
  exact inv_dia a

lemma dia_inv {G : Type*} [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  have : a⁻¹⁻¹ = a := inv_eq_of_dia (inv_dia a)
  rw [← inv_dia a⁻¹, this]

-- We would like to move on to define rings, but there is a serious issue. A ring structure on a
-- type contains both an additive group structure and a multiplicative monoid structure, and
-- some properties about their interaction. But so far we hard-coded a notation `⋄` for all our operations.
-- More fundamentally, the type class system assumes every type has only one instance of each type class.
-- To solve this issue, Mathlib uses the naive idea to duplicate everything for additive and multiplicative
-- theories with the help of some code-generating attribute.

--  Structures and classes are defined in both additive and multiplicative notation with an attribute
-- `to_additive` linking them.

class AddSemigroup₃ (α : Type*) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type*) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type*) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type*) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

-- Lemmas are then only stated in multiplicative notation and marked with the attribute `to_additive`
-- to generate the additive version.

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type*} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) :
    b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'

-- Equipped with this technology, we can easily define also commutative semigroups, monoids and
-- groups, and then define rings.

class AddCommSemigroup₃ (α : Type*) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type*) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type*) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type*) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type*) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type*) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1

-- We should remember to tag lemmas with `simp` when appropriate.

attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

-- we need to repeat ourselves a bit since we switch to standard notations, but at least
-- `to_additive` does the work of translating from the multiplicative notation to the additive one.

export Group₃ (inv_mul)

@[to_additive]
lemma inv_eq_of_mul {G : Type*} [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  refine left_inv_eq_right_inv' ?_ h
  rw [inv_mul]

-- Note that `to_additive` can be asked to tag a lemma with `simp` and propagate that
-- attribute to the additive version.

@[to_additive (attr := simp)]
lemma mul_inv₃ {G : Type*} [Group₃ G] (a : G) : a * a⁻¹ = 1 := by
  have : a⁻¹⁻¹ = a := inv_eq_of_mul (inv_mul a)
  rw [← inv_mul a⁻¹, this]

@[to_additive]
lemma mul_left_cancel₃ {G : Type*} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← inv_mul a, mul_assoc₃, h, ← mul_assoc₃, inv_mul, one_mul]

@[to_additive]
lemma mul_right_cancel₃ {G : Type*} [Group₃ G] {a b c : G} (h : b * a = c * a) : b = c := by
  rw [← mul_one b, ← mul_inv₃ a, ← mul_assoc₃, h, mul_assoc₃, mul_inv₃, mul_one]

class AddCommGroup₃ (G : Type*) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type*) extends Group₃ G, CommMonoid₃ G

-- We are now ready for rings. For demonstration purposes we won’t assume that addition is commutative,
-- and then immediately provide an instance of `AddCommGroup₃`.

class Ring₃ (R : Type*) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

-- It is an example of building an instance using the syntax that allows to provide a parent structure
-- and some extra fields.

instance {R : Type*} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
    intro a b
    have : a + (a + b + b) = a + (b + a + b) := by
      sorry
    exact add_right_cancel₃ (add_left_cancel₃ this) }

-- We can also build concrete instances, such as a ring structure on integers.

instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := by
    intro a b c
    rw [mul_add]
  right_distrib := by
    intro a b c
    rw [add_mul]

-- As an exercise you can now set up a simple hierarchy for order relations, including a class
-- for ordered commutative monoids, which have both a partial order and a commutative monoid
-- structure such that `∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b`.

class LE₁ (α : Type*) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type*)
  extends LE₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c

class PartialOrder₁ (α : Type*)
  extends Preorder₁ α where
  le_antisymm : ∀ a b : α, a ≤₁ b → b ≤₁ a → a = b

class OrderedCommMonoid₁ (α : Type*)
  extends PartialOrder₁ α, CommMonoid₃ α where
  mul_of_le : ∀ a b : α, a ≤₁ b → ∀ c : α, c * a ≤₁ c * b

instance : PartialOrder₁ ℕ where
  le := fun a b ↦ ∃ c : ℕ, b = a + c
  le_refl := by
    intro a
    use 0
    rw [add_zero]
  le_trans := by
    intro a b c h1 h2
    obtain ⟨d, hd⟩ := h1
    obtain ⟨e, he⟩ := h2
    use d + e
    rw [he, hd, add_assoc]
  le_antisymm := by
    intro a b h1 h2
    obtain ⟨d, hd⟩ := h1
    obtain ⟨e, he⟩ := h2
    rw [he, add_assoc, self_eq_add_right, add_eq_zero] at hd
    rwa [hd.1, add_zero] at he

instance : CommMonoid₃ ℕ where
  mul_assoc₃ := by
    intro a b c
    rw [Nat.mul_assoc]
  one_mul := by simp
  mul_one := by simp
  mul_comm := by
    intro a b
    exact Nat.mul_comm a b

instance : OrderedCommMonoid₁ ℕ :=
{ (inferInstance : CommMonoid₃ ℕ), (inferInstance : PartialOrder₁ ℕ) with
  mul_of_le := by
    intro a b h c
    obtain ⟨d, hd⟩ := h
    use c * d
    rw [hd, mul_add]
}

-- We now discuss algebraic structures involving several types. The prime example is modules over rings.
-- Those are commutative additive groups equipped with a scalar multiplication by elements of some ring.

class SMul₃ (α : Type*) (β : Type*) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul

class Module₁ (R : Type*) [Ring₃ R] (M : Type*) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • (b • m)
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

-- Note that the following does not work:

class Module₂ (R : Type*) [Ring₃ R] (M : Type*) extends SMul₃ R M, AddCommGroup₃ M where

-- Remember that such an extends clause would lead to a field `Module₂.toAddCommGroup₃` marked as an
-- instance. This instance would have the signature:
-- `(R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M`.
-- But with such an instance, each time Lean would look for a `AddCommGroup₃ M` instance for some M,
-- it would need to go hunting for a completely unspecified type `R` and a `Ring₃ R` instance
-- and then try to find a `Module₁ R M` instance. Such a `Module₃.toAddCommGroup₃` instance would then
--  be a huge trap for the instance resolution procedure and thus class command refuses to set it up.

-- What about `extends SMul₃ R M` then? That one creates a field
-- `Module₁.toSMul₃ : {R : Type} →  [inst : Ring₃ R] → {M : Type} → [inst_1 : AddCommGroup₃ M] → [self : Module₁ R M] → SMul₃ R M`
-- whose end result `SMul₃ R M` mentions both `R` and `M` so this field can safely be used as an instance.

-- The rule is easy to remember: each class appearing in the `extends` clause should mention
-- every type appearing in the parameters.


-- Our first module instance is that a ring is a module over itself using its multiplication
-- as a scalar multiplication.

instance selfModule (R : Type*) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib

-- Second example: every abelian group is a module over `ℤ`. First one can define scalar multiplication
-- by a natural number for any type equipped with a zero and an addition, then extends to scalar
-- multiplication by an integer by ensuring `(-1) • a = -a`.

-- For `n : ℕ`, `n • a` is defined as `a + (n - 1) • a` with `0 • a = 0`.

def nsmul₁ {M : Type*} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a

-- Proving this gives rise to a module structure is a bit tedious, so we `sorry` all axioms.
-- *You are not asked to replace those sorries with proofs.* If you insist on doing it then you
-- will probably want to state and prove several intermediate lemmas about `nsmul₁` and `zsmul₁`.

instance abGrpModule (A : Type*) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry

-- An important issue is that we now have two module structures over the ring `ℤ` for `ℤ` itself:
-- `abGrpModule ℤ` since `ℤ` is a abelian group, and `selfModule ℤ` since `ℤ` is a ring.
-- Those two module structure correspond to the same abelian group structure, but it is not obvious
-- that they have the same scalar multiplication. They actually do, but this isn’t true by definition,
-- it requires a proof. This is very bad news for the type class instance resolution procedure and
-- will lead to very frustrating failures for users of this hierarchy.
-- This situation is known as a bad diamond.

-- Note that when asked to find an instance, Lean will just pick one.

#synth Module₁ ℤ ℤ -- abGrpModule ℤ

-- All diamonds are not bad. In fact there are diamonds everywhere in `Mathlib`, and also in the code
-- above. Indeed, we can go from `Monoid₁ α` to `Dia₁ α` through either `Semigroup₁ α` or `DiaOneClass₁ α`
-- but the resulting two `Dia₁ α` instances are *definitionally equal*.

-- In particular a diamond having a Prop-valued class at the bottom cannot be bad since any too proofs
-- of the same statement are definitionally equal.

-- In our module construction, the offending piece is the `smul` field which is data, not a proof,
-- and we have two constructions that are not definitionally equal. The robust way of fixing this
-- issue is to make sure that going from a rich structure to a poor structure is always done by
-- forgetting data, not by defining data. This well-known pattern as been named “forgetful inheritance”.

-- In our case, we can modify the definition of `AddMonoid₃` to include a `nsmul` data field and
-- some Prop-valued fields ensuring this operation is provably the one we constructed above.

class AddMonoid₄ (M : Type*) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type*} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

-- We can now handle the special case of `ℤ` where we want to build `nsmul` using the coercion
-- of `ℕ` to `ℤ` and the multiplication on `ℤ`.
-- Note in particular how the proof fields contain more work than in the default value above.

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]

-- We check that we have solved our issue. Because Lean already has a definition of scalar
-- multiplication of a natural number and an integer, and we want to make sure our instance is used,
-- we don’t use the `•` notation but call `SMul.mul` and explicitly provide our instance defined above.

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl

-- Then of course we need to incorporate a `zsmul` field into the definition of groups and similar tricks...
