
import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic

open Classical

@[ext]
structure Equiv₁ (α β : Type*) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ (x : α), invFun (toFun x) = x 
  right_inv : ∀ (y : β), toFun (invFun y) = y

namespace Equiv₁

variable {α β γ : Type*}

theorem better_ext {f g : Equiv₁ α β} (h : f.toFun = g.toFun) : f = g := by
  apply Equiv₁.ext h
  ext y 
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
  -- apply Equiv₁.mk --we don't use this bc it would ask me for the arguments in a weird order, and it's clearer as done below
  refine Equiv₁.mk ?_ ?_ ?_ ?_
  · exact f.invFun
  · exact f.toFun
  · exact f.right_inv
  · exact f.left_inv

def trans (f : Equiv₁ α β) (g : Equiv₁ β γ) : Equiv₁ α γ where
  toFun := g.toFun ∘ f.toFun
  invFun := f.invFun ∘ g.invFun
  left_inv := by
    intro x 
    rw [Function.comp_apply, Function.comp_apply, g.left_inv, f.left_inv]
  right_inv := by 
    intro y 
    rw [Function.comp_apply, Function.comp_apply, f.right_inv, g.right_inv]

end Equiv₁

structure BundledGroup₁ where --bc everything is introduced inside ("Bundled")
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



example {α : Type*} : BundledGroup₁ where --Equiv is a group, we see it explicitly here
  carrier := Equiv₁ α α
  one := Equiv₁.refl α
  mul := Equiv₁.trans
  inv := Equiv₁.symm
  mul_one f := by 
    apply Equiv₁.better_ext 
    ext 
    rfl
  one_mul f := by 
    apply Equiv₁.better_ext 
    ext 
    rfl
  mul_assoc f g h := by 
    apply Equiv₁.better_ext 
    rfl
  inv_mul_cancel f := by 
    apply Equiv₁.better_ext
    ext x 
    erw [f.right_inv] 
    /- or we could
    change f.toFun (f.invFun x) = x
    rw [f.right_inv]
    to change it as we wanted.-/
    rfl

    

example {α : Type*} : Group₁ (Equiv₁ α α) where
  one := Equiv₁.refl α
  mul := Equiv₁.trans
  inv := Equiv₁.symm
  mul_one f := by 
    apply Equiv₁.better_ext 
    ext 
    rfl
  one_mul f := by 
    apply Equiv₁.better_ext 
    ext 
    rfl
  mul_assoc f g h := by
    apply Equiv₁.better_ext 
    rfl
  inv_mul_cancel f := by
    apply Equiv₁.better_ext 
    ext x 
    erw [f.right_inv] 
    rfl

lemma Group₁.inv_eq_of_mul {α : Type*} (G : Group₁ α) (x y : α) :
    G.mul x y = G.one → G.inv x = y := by
    intro h 
    apply_fun (fun z ↦ G.mul (G.inv x) z) at h 
    rw [G.mul_one] at h 
    rw [← G.mul_assoc, G.inv_mul_cancel, G.one_mul] at h
    exact h.symm

lemma Group₁.mul_inv_cancel {α : Type*} (G : Group₁ α) (x : α) :
    G.mul x (G.inv x) = G.one := by
    have heq : G.inv (G.inv x) = x := by 
      apply Group₁.inv_eq_of_mul
      exact G.inv_mul_cancel x
    have : G.mul x (G.inv x) = G.mul (G.inv (G.inv x)) (G.inv x) := by 
      rw [heq]
    rw [this]
    exact G.inv_mul_cancel (G.inv x)


#synth AddGroup ℤ
#synth Ring ℝ
#synth Field ℚ
#synth LinearOrder ℝ


class Group₂ (α : Type*) where
  one : α
  mul : α → α → α
  inv : α → α
  mul_one : ∀ (x : α), mul x one = x
  one_mul : ∀ (x : α), mul one x = x
  mul_assoc : ∀ (x y z : α), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : α), mul (inv x) x = one

lemma Group₂.mul_inv_cancel {α : Type*} [Group₂ α] (x : α) :
     mul x (inv x) = one := by
     have : ∀ x : α, ∀ y : α, mul x y = one → inv x = y := by 
       intro a b h
       apply_fun (fun z ↦ mul (inv a) z) at h
       rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h
       exact h.symm
     have h : inv (inv x) = x := by 
       apply this 
       exact inv_mul_cancel x
     apply_fun (fun z ↦ mul z (inv x)) at h
     rw [inv_mul_cancel (inv x)] at h 
     exact h.symm

instance {α : Type*} : Group₂ (Equiv₁ α α) where
  one := Equiv₁.refl α
  mul := Equiv₁.trans
  inv := Equiv₁.symm
  mul_one f := by 
    apply Equiv₁.better_ext 
    rfl
  one_mul f := by 
    apply Equiv₁.better_ext 
    rfl
  mul_assoc f g h:= by 
    apply Equiv₁.better_ext 
    rfl
  inv_mul_cancel f := by 
    apply Equiv₁.better_ext 
    ext x
    erw [f.right_inv] 
    rfl

section Tests

variable {α : Type*}

#synth Group₂ (Equiv₁ α α)
#check Equiv.Perm α
#print Equiv.Perm
#print Equiv
#synth Group (Equiv.Perm α)

end Tests


/- *How does Lean know that a group is a monoid ?*

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
  mul_one a := Nat.add_zero a
  one_mul a := Nat.zero_add a
  mul_assoc := add_assoc


class Group₃ (α : Type*) extends Monoid₁ α where
  inv : α → α
  inv_mul_cancel : ∀ (x : α), mul (inv x) x = one

#print Group₃

-- We get a function sending a group to a monoid, but Lean can also do that
-- automatically.
#check Group₃.toMonoid₁

instance {α : Type*} : Group₃ (Equiv₁ α α) where 
  one := Equiv₁.refl α
  mul := Equiv₁.trans
  mul_one a := by apply Equiv₁.better_ext; rfl
  one_mul a := by apply Equiv₁.better_ext; rfl
  mul_assoc a b c:= by apply Equiv₁.better_ext; rfl
  inv := Equiv₁.symm
  inv_mul_cancel a := by apply Equiv₁.better_ext; ext x; erw [a.right_inv]; rfl

section Tests

variable (α : Type*)
#synth Group₃ (Equiv₁ α α)
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
  left_inv x := Int.neg_neg x
  right_inv x := Int.neg_neg x
  inv x := Int.neg_neg x


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
--@[inherit_doc]
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
  dia_assoc f g h := by rfl

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

example (a : ℕ) : (𝟙 : Equiv₁ ℕ ℕ).toFun a = a := rfl

-- To define monoids, we just need to put semigroups and unit elements together,
-- and to add a couple of axioms.
-- First we define types with a multiplication and a unit such that the unit is a
-- neutral element.

class DiaOneClass₁_no_unit (α : Type*) extends One₁ α, Dia₁ α

#print DiaOneClass₁_no_unit

example : DiaOneClass₁_no_unit ℕ where 
  one := 0
  dia := fun a b ↦ a + b

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

#print Monoid₃

example {α : Type*} [Monoid₂ α] :
  (Monoid₂.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₂.toDiaOneClass₁.toDia₁.dia := rfl

example {α : Type*} [Monoid₃ α] :
  (Monoid₃.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₃.toDiaOneClass₁.toDia₁.dia := rfl
-- `rfl` does not work.

#print Monoid₃
#check Monoid₃.mk
#check Monoid₂.mk


instance {α : Type*} : DiaOneClass₁ (Equiv₁ α α) where
  one_dia f := by apply Equiv₁.better_ext; rfl
  dia_one f := rfl

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
  inv_dia f := by apply Equiv₁.better_ext; ext s; erw [f.right_inv]; rfl

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

/- Exercise: define a second binary operator class, say `Ast₁` with notation `∗` (\ + ast),
and a second unit `OneBis` with notation `𝟭` (\ + sb1); define a class `AstOneBisClass₁` similar
to `DiaOneClass₁`.
Then introduce a class `TwoCompatibleLaws` extending `DiaOneClass₁` and `AstOneBisClass₁` with
the extra condition that `exchange : ∀ x y z t, (x ⋄ y) ∗ (z ⋄ t) = (x ∗ z) ⋄ (y ∗ t)`.

Then prove the following lemmas:

lemma one_eq_oneBis {α : Type*} (M : TwoCompatibleLaws α) : 𝟙 = 𝟭 := sorry

lemma dia_eq_ast {α : Type*} (M : TwoCompatibleLaws α) (x y : α) : x ⋄ y = x ∗ y := sorry

lemma dia_comm {α : Type*} (M : TwoCompatibleLaws α) (x y : α) : x ⋄ y = y ⋄ x := sorry

lemma dia_assoc {α : Type*} (M : TwoCompatibleLaws α) (x y z : α) : x ⋄ y ⋄ z = x ⋄ (y ⋄ x) := sorry
-/

class Ast₁ (α : Type*) where 
  Ast : α → α → α

--@[inherit_doc]
infixl:70 " ∗ " => Ast₁.Ast

class OneBis (α : Type*) where 
  onebis : α 

--@[inherit_doc]
notation "𝟭" => OneBis.onebis

class AstOneBisClass₁ (α : Type*) extends Ast₁ α, OneBis α where 
  one_ast : ∀ a : α, 𝟭 ∗ a = a
  ast_one : ∀ a : α, a ∗ 𝟭 = a

class TwoCompatibleLaws (α : Type*) extends DiaOneClass₁ α, AstOneBisClass₁ α where
  exchange : ∀ x y z t : α, (x ⋄ y) ∗ (z ⋄ t) = (x ∗ z) ⋄ (y ∗ t) 

export TwoCompatibleLaws (exchange)
export AstOneBisClass₁ (one_ast ast_one)

lemma one_eq_oneBis {α : Type*} (M : TwoCompatibleLaws α) : 𝟙 = (𝟭 : α) := by 
  have := exchange (𝟭 : α) 𝟙 𝟙 𝟭
  rw [ast_one, dia_one (𝟭 ∗ 𝟙), one_ast, dia_one, one_dia, one_ast] at this
  exact this.symm

lemma dia_eq_ast {α : Type*} (M : TwoCompatibleLaws α) (x y : α) : x ⋄ y = x ∗ y := by
  conv_rhs => rw [← dia_one x, ← one_dia y, exchange, one_eq_oneBis, ast_one, one_ast] 

lemma dia_comm {α : Type*} (M : TwoCompatibleLaws α) (x y : α) : x ⋄ y = y ⋄ x := by 
  have := exchange 𝟙 x y 𝟭
  rw [one_dia, ast_one, one_eq_oneBis, one_ast, ← one_eq_oneBis, dia_one, ← dia_eq_ast] at this
  exact this

lemma dia_assoc {α : Type*} (M : TwoCompatibleLaws α) (x y z : α) : x ⋄ y ⋄ z = x ⋄ (y ⋄ z) := by 
  conv_rhs => rw [dia_eq_ast M y z, ← ast_one x, ← exchange, ← one_eq_oneBis, one_dia, ← dia_eq_ast]
