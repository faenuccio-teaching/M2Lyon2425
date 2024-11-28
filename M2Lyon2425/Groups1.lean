-- Credit: I stole (almost)  everything from *Mathematics in Lean*.
import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic

open Classical

/-!
Announcement about projects: you should let us know what final exam project you want
to work on by November 15, but it would be better if you did it earlier (say after
you come back from fall break).
Also, to communicate your project topic to us, you should create a branch in the
`M2Lyon2425` git repository and add in it a file containing the project description.
This will teach you to use branches, which will be necessary when you turn in your
project.
-/

/-## Structures

A *structure* is a type consisting of a collection of data, with optionally some
conditions that the data should satisfy (which are just data of type `Prop`).

An *instance* of a structure is a particular example of the structure.
-/

-- The following structure has no condition, it is just the data of three real numbers.
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- We can define terms of type `Point` in several different ways.
def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

-- We can access the fields of a term of type `Point` using the projections `.x`, `.y`
-- and `.z`.
#check myPoint1.x
#check myPoint1.z

-- The annotation `@[ext]` automatically generates a theorem `Point.ext` that says that
-- two terms of type `Point` are equal if and only if all their fields are equal.

#check Point.ext

example : myPoint1 = myPoint2 := by
  apply Point.ext
  · rfl
  · rfl
  · rfl

-- Of course `Point` is "the same" as `ℝ × ℝ × ℝ`, but one advantage of `Point` is
-- that, as the fields are named, we can ignore the order on the coordinates.

def myPoint4 : Point where
  z := 2
  x := -1
  y := 4

/- A more complicated structure: equivalences between two types `α` and `β`.-/

@[ext]
structure Equiv₁ (α β : Type*) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ (x : α), invFun (toFun x) = x
  right_inv : ∀ (y : β), toFun (invFun y) = y

#print Equiv₁

-- To check that two equivalences are equal, we need to check the equality of
-- their `toFun` and `invFun` fields, which is not ideal.
#check Equiv₁.ext

namespace Equiv₁

variable {α β γ : Type*}

theorem better_ext {f g : Equiv₁ α β} (h : f.toFun = g.toFun) : f = g := by
  apply Equiv₁.ext
  · exact h
  · ext y
    have := f.right_inv y
    conv_rhs => rw [← this, h, g.left_inv]

-- The identity as equivalence.

def refl (α) : Equiv₁ α α where
  toFun := fun x ↦ x
  invFun := fun x ↦ x
  left_inv _ := rfl
  right_inv _ := rfl

-- Defining functions on structures: inverse and composition of equivalences.

def symm (f : Equiv₁ α β) : Equiv₁ β α where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv

def symm' (f : Equiv₁ α β) : Equiv₁ β α :=
  {
    toFun := f.invFun
    invFun := f.toFun
    left_inv:= f.right_inv
    right_inv := f.left_inv
  }

def symm'' (f : Equiv₁ α β) : Equiv₁ β α := by
  -- apply Equiv₁.mk
  refine Equiv₁.mk ?_ ?_ ?_ ?_
  · exact f.invFun
  · exact f.toFun
  · exact f.right_inv
  · exact f.left_inv

def trans (f : Equiv₁ α β) (g : Equiv₁ β γ) : Equiv₁ α γ where
  toFun := g.toFun ∘ f.toFun
  invFun := f.invFun ∘ g.invFun
  left_inv := by intro x; simp; rw [g.left_inv, f.left_inv]
  right_inv := by intro x; simp; rw [f.right_inv, g.right_inv]

end Equiv₁


/- On to groups! There are two choices: making the underlying set of the group a
field of the structure, or not.-/

structure BundledGroup₁ where
  carrier : Type*
  one : carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  mul_one : ∀ (x : carrier), mul x one = x
  one_mul : ∀ (x : carrier), mul one x = x
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : carrier), mul (inv x) x = one
-- You might want to put one more condition called `mul_inv_cancel`, but we can
-- actually prove it from the others, see later.

structure Group₁ (α : Type*) where
  one : α
  mul : α → α → α
  inv : α → α
  mul_one : ∀ (x : α), mul x one = x
  one_mul : ∀ (x : α), mul one x = x
  mul_assoc : ∀ (x y z : α), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : α), mul (inv x) x = one

/- Mathlib chose the second solution, because this way we can put a group structure
on an already defined type, such as `ℤ` or `Equiv₁ α α`.

(But when we define the category of groups, its objects are terms of a type resembling
`BundledGroup₁`.)
-/

example {α : Type*} : BundledGroup₁ where
  carrier := Equiv₁ α α
  one := Equiv₁.refl α
  mul := Equiv₁.trans
  inv := Equiv₁.symm
  mul_one _ := rfl
  one_mul _ := rfl
  mul_assoc _ _ _ := rfl
  inv_mul_cancel := by 
    intro ⟨ f, g, L, R ⟩; apply Equiv₁.better_ext
    ext y; exact R y

example {α : Type*} : Group₁ (Equiv₁ α α) where
  one := Equiv₁.refl α
  mul := Equiv₁.trans
  inv := Equiv₁.symm
  mul_one _ := rfl
  one_mul _ := rfl
  mul_assoc _ _ _ := rfl
  inv_mul_cancel := by
    intro ⟨ f, g, L, R ⟩; apply Equiv₁.better_ext
    ext y; exact R y

lemma Group₁.inv_eq_of_mul {α : Type*} (G : Group₁ α) (x y : α) :
    G.mul x y = G.one → G.inv x = y := by
  intro e
  rw [←(G.mul_one (G.inv x)), ←e, ←G.mul_assoc, G.inv_mul_cancel, G.one_mul]

lemma Group₁.mul_inv_cancel {α : Type*} (G : Group₁ α) (x : α) :
    G.mul x (G.inv x) = G.one := by
  have := Group₁.inv_eq_of_mul _ _ _ (G.inv_mul_cancel x)
  conv_lhs => congr; rfl; rw [←this]
  exact G.inv_mul_cancel (G.inv x)

-- Hint: you might find the following lemma useful:
/-
lemma Group₁.inv_eq_of_mul {α : Type*} (G : Group₁ α) (x y : α) :
    G.mul x y = G.one → G.inv x = y := sorry
-/

/- The last example is kind of painful to write. We would like to:
(1) not have to give a name for the group structure on `α`;
(2) be able to use more standard notation like `1`, `x * y`, `x⁻¹`.

The answer to (1) is `instance magic`, and the answer to (2) is `inheritance and
instances`.

Let's start with (1). As said before, an instance is a particular example of a
structure. We would like to be able to declare a particular `Group` instance on
a structure such as `Equiv₁ α α` or `ℤ` and never have to refer to it explicitly
again, and we would also like Lean to be able to guess what this instance is.
This is done by the (black, black) magic of *type class inference*.

We already saw implicit arguments written `{x : α}`, Lean is supposed to figure
these out from context.

We can also have arguments written `[grp : Group α]` and Lean is supposed to
synthesize these using type class inference, i.e. by looking through a number
of previously declared *instances*. (Usually we write `[Group α]`, since we are
not supposed to need to use the name.)
-/

#synth Group ℤ -- oh no, mathlib only uses `Group` for groups written multiplicatively!
-- this helps when we come to rings and have two composition laws written `+` and `*`
#synth AddGroup ℤ
#synth Ring ℝ
#synth Field ℚ
#synth LinearOrder ℝ

lemma Group₁.mul_inv_cancel' {α : Type*} [Group₁ α] (x : α) :
     mul x (inv x) = one := sorry
-- This does not work, because in order to use a structure for type class inference,
-- we should declare it as a *class*.

class Group₂ (α : Type*) where
  one : α
  mul : α → α → α
  inv : α → α
  mul_one : ∀ (x : α), mul x one = x
  one_mul : ∀ (x : α), mul one x = x
  mul_assoc : ∀ (x y z : α), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : α), mul (inv x) x = one

lemma Group₂.inv_eq_of_mul {α : Type*} [Group₂ α] (x y : α) :
    mul x y = one → inv x = y := by
  intro e
  rw [←(mul_one (inv x)), ←e, ←mul_assoc, inv_mul_cancel, one_mul]

lemma Group₂.mul_inv_cancel {α : Type*} [Group₂ α] (x : α) :
     mul x (inv x) = one := by
  have := Group₂.inv_eq_of_mul _ _ (inv_mul_cancel x)
  conv_lhs => congr; rw [←this]
  exact inv_mul_cancel (inv x)

instance {α : Type*} : Group₂ (Equiv₁ α α) where
  one := Equiv₁.refl α
  mul := Equiv₁.trans
  inv := Equiv₁.symm
  mul_one _ := rfl
  one_mul _ := rfl
  mul_assoc _ _ _ := rfl
  inv_mul_cancel := by
    intro ⟨ f, g, L, R ⟩
    apply Equiv₁.better_ext
    ext y; exact R y

section Tests

variable {α : Type*}

#synth Group₂ (Equiv₁ α α) -- Lean automatically chose a name for the nameless instance we declared
#check Equiv.Perm α
#print Equiv.Perm
#print Equiv
#synth Group (Equiv.Perm α)

end Tests

/- *How does Lean know that a group is a monoid ?*

Remember that a *monoid* is a set with an associative composition law and a unit
(but not necessarily inverses). For example, `ℕ` is a monoid for addition.

It is easy enough to define a class for monoids in Lean.
-/

class Monoid₁ (α : Type*) where
  one : α
  mul : α → α → α
  mul_one : ∀ (x : α), mul x one = x
  one_mul : ∀ (x : α), mul one x = x
  mul_assoc : ∀ (x y z : α), mul (mul x y) z = mul x (mul y z)

instance : Monoid₁ ℕ where
  one := 0
  mul a b := a + b
  mul_one _ := rfl
  one_mul _ := by simp
  mul_assoc := add_assoc

/- But every group is also a monoid, and Lean should know this. How do we tell it?

Mathlib's answer is *inheritance*. We actually define the class of groups to
extend that of monoids, by adding the fields that `Monoid₁` doesn't have.
-/

class Group₃ (α : Type*) extends Monoid₁ α where
  inv : α → α
  inv_mul_cancel : ∀ (x : α), mul (inv x) x = one

#print Group₃

-- We get a function sending a group to a monoid, but Lean can also do that
-- automatically.
#check Group₃.toMonoid₁

instance {α : Type*} : Group₃ (Equiv₁ α α) := sorry

section Tests

variable (α : Type*)
#synth Monoid₁ (Equiv₁ α α)

end Tests

-- NB: We can also use inheritance with structures that are not classes.
-- Here is a stupid example.

structure Involution₁ (α : Type*) extends Equiv₁ α α where
  inv : ∀ (x : α), toFun (toFun x) = x

#print Involution₁

example : Involution₁ ℤ where
  toFun := fun x ↦ -x
  invFun := fun x ↦ -x
  left_inv _ := by simp
  right_inv _ := by simp
  inv _ := by simp

/- What about using notation?

What we do is declare all the "pieces" making up a group as a different classes
and introduce notation for them (so they can be used in various contexts). Then we
"glue" them together using inheritance.
-/

-- Let's start by defining a class for types with a binary operation. We use
-- the diamond notation for the operation so it doesn't clash with anything else.

class Dia₁ (α : Type*) where
  dia : α → α → α

-- Notation.
--(The `inherit_doc` tells Lean to use the same documentation for
-- `⋄` as for `Dia₁.dia`.)
@[inherit_doc]
infixl:70 " ⋄ " => Dia₁.dia -- type ⋄ using \ + diamond (or just \ + dia)
 
-- The binary operation on permutations.
instance {α : Type*} : Dia₁ (Equiv₁ α α) where
  dia := Equiv₁.trans

-- Now we can use the `⋄` notation to multiply permutations!
example (α : Type*) (σ τ : Equiv₁ α α) : Equiv₁ α α := σ ⋄ τ

-- A semigroup is a type with an associative binary law.
class Semigroup₁ (α : Type*) extends Dia₁ α where
  dia_assoc : ∀ (x y z : α), x ⋄ y ⋄ z = x ⋄ (y ⋄ z)

instance {α : Type*} : Semigroup₁ (Equiv₁ α α) where
  dia_assoc _ _ _ := rfl

-- Let's do the same with the unit element.
class One₁ (α : Type*) where
  /-- The element one -/
  one : α

instance {α : Type*} : One₁ (Equiv₁ α α) where
  one := Equiv₁.refl α

#check (One₁.one : Equiv₁ ℕ ℕ)

-- Notation.
@[inherit_doc]
notation "𝟙" => One₁.one  -- type using \ + b1

#check (𝟙 : Equiv₁ ℕ ℕ)

example (a : ℕ) : (𝟙 : Equiv₁ ℕ ℕ).toFun a = a := by rfl

-- To define monoids, we just need to put semigroups and unit elements together,
-- and to add a couple of axioms.
-- First we define types with a multiplication and a unit such that the unit is a
-- neutral element.

class DiaOneClass₁ (α : Type*) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

class Monoid₂ (α : Type*) extends DiaOneClass₁ α, Semigroup₁ α

#print Monoid₂ -- note that Lean knows that the binary operations coming from the
               -- DiaOneClass₁ and the Semigroup₁ are the same

-- Here is a bad idea, because we will get two binary operations that are not the same:
class Monoid₃ (α : Type*) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

example {α : Type*} [Monoid₂ α] :
  (Monoid₂.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₂.toDiaOneClass₁.toDia₁.dia := rfl

example {α : Type*} [Monoid₃ α] :
  (Monoid₃.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₃.toDiaOneClass₁.toDia₁.dia := rfl
-- `rfl` does not work.

#print Monoid₃
#check Monoid₃.mk
#check Monoid₂.mk


instance {α : Type*} : DiaOneClass₁ (Equiv₁ α α) where
  one_dia _ := rfl
  dia_one _ := rfl

instance {α : Type*} : Monoid₂ (Equiv₁ α α) where
  dia_assoc := Semigroup₁.dia_assoc

#synth Monoid₂ (Equiv₁ ℕ ℕ)

-- To finish, we do the same with inverses.
class Inv₁ (α : Type*) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

instance {α : Type*} : Inv₁ (Equiv₁ α α) where
  inv := Equiv₁.symm

example (σ : Equiv₁ ℕ ℕ) : Equiv₁ ℕ ℕ := σ⁻¹

class Group₄ (G : Type*) extends Monoid₂ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙

instance {α : Type*} : Group₄ (Equiv₁ α α) where
  inv_dia := by
    intro ⟨ f, g, L, R ⟩
    apply Equiv₁.better_ext
    ext y; exact R y

lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₂ M] {a b c : M}
    (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]

-- Using `export`, we can use the lemmas without their prefixes.
export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₄ (inv_dia)

lemma left_inv_eq_right_inv₁' {M : Type} [Monoid₂ M] {a b c : M}
    (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]


class Ast₁ (α : Type*) where
  ast : α → α → α

@[inherit_doc]
infixl:70 " ∗ " => Ast₁.ast

class OneBis (α : Type*) where
  oneBis : α

@[inherit_doc]
notation "𝟏" => OneBis.oneBis

class AstOneBisClass₁ (α : Type*) extends OneBis α, Ast₁ α where
  one_ast : ∀ x : α, 𝟏 ∗ x = x
  ast_one : ∀ x : α, x ∗ 𝟏 = x

class TwoCompatibleLaws (α : Type*) extends DiaOneClass₁ α, AstOneBisClass₁ α where
  exchange : ∀ x y z t : α, (x ⋄ y) ∗ (z ⋄ t) = (x ∗ z) ⋄ (y ∗ t)

lemma one_eq_oneBis {α : Type*} (M : TwoCompatibleLaws α) : (𝟙 : α) = (𝟏 : α) := by
  rw [←(M.ast_one 𝟙)]  
  rw [←(dia_one (𝟙 ∗ 𝟏))]  
  conv_lhs => congr; rfl; rw [←(M.one_ast 𝟙)]
  rw [←M.exchange, dia_one, one_dia, M.ast_one]

lemma dia_eq_ast {α : Type*} (M : TwoCompatibleLaws α) (x y : α) : x ⋄ y = x ∗ y := by
  conv_lhs => congr; rw [←(M.ast_one x)]; rfl; rw [←(M.one_ast y)]
  rw [←M.exchange, ←one_eq_oneBis, M.dia_one, M.one_dia]

lemma dia_comm {α : Type*} (M : TwoCompatibleLaws α) (x y : α) : x ⋄ y = y ⋄ x := by
  conv_lhs => rw [dia_eq_ast, ←(one_dia x), ←(dia_one y)]
  rw [M.exchange, one_eq_oneBis, M.one_ast, M.ast_one]
  
lemma dia_assoc {α : Type*} (M : TwoCompatibleLaws α) (x y z : α) : x ⋄ y ⋄ z = x ⋄ (y ⋄ z) := by
  conv_lhs => rw [dia_eq_ast]; congr; rfl; rw [←(M.one_dia z)]
  rw [M.exchange, one_eq_oneBis, M.ast_one, ←dia_eq_ast]
