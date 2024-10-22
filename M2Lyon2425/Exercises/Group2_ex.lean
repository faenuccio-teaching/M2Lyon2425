-- Partially completed - only the things done on 16/10
import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Quotient
import Mathlib.Tactic

section Morphisms

@[ext]
structure MonoidHom₁ (M N : Type*) [Monoid M] [Monoid N] where
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = (toFun x) * (toFun y)

structure IsMonoidHom₁ {M N : Type*} [Monoid M] [Monoid N] (f : M → N) where
  map_one : f 1 = 1
  map_mul : ∀ (x y : M), f (x * y) = (f x) * (f y)

def f : MonoidHom₁ (ℕ × ℕ) ℕ where
  toFun p := p.1 * p.2
  map_one := rfl
  map_mul x y := by simp; exact Nat.mul_mul_mul_comm x.1 y.1 x.2 y.2

instance {G H : Type*} [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun

namespace MonoidHom₁

lemma map_pow {M N : Type*} [Monoid M] [Monoid N] (f : MonoidHom₁ M N) (a : M) (n : ℕ) :
    f (a ^ n) = (f a) ^ n := by
  induction' n with n hn
  · simp
    exact f.map_one
  · rw [npow_add, npow_add, map_mul, pow_one, pow_one, hn]

end MonoidHom₁

@[ext]
structure AddMonoidHom₁ (G H : Type*) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

@[ext]
structure RingHom₁ (R S : Type*) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

section MisguidedStuff

class MonoidHomClass₁ (F : Type*) (M N : Type*) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance (M N : Type*) [Monoid M] [Monoid N] : MonoidHomClass₁ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type*) [Ring R] [Ring S] : MonoidHomClass₁ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul

namespace MonoidHomClass₁


lemma map_pow {M N F : Type*} [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] (f : F) (a : M) (n : ℕ) :
    toFun f (a ^ n) = (toFun f a : N) ^ n := by
  induction' n with n hn
  · simp --simp? shows which lemmas it's calling
    rw [map_one]
  · rw [pow_succ, pow_succ, map_mul, hn]

end MonoidHomClass₁

example {R S : Type*} [Ring R] [Ring S] (f : RingHom₁ R S) (a : R) (n : ℕ) :
    MonoidHomClass₁.toFun f (a ^ n) = (MonoidHomClass₁.toFun f a : S) ^ n := by
  rw [MonoidHomClass₁.map_pow]


class MonoidHomClass₂ (F : Type*) (M N : outParam Type*) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance {F M N : Type*} [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] :
    CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun

-- Let's put `MonoidHomClass₂` instances on monoid and ring morphisms.

instance (M N : Type*) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type*) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
  
variable (R S : Type*) [Ring R] [Ring S] (f : RingHom₁ R S) (a : R)

namespace MonoidHomClass₂

lemma map_pow {M N F : Type*} [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) (a : M) (n : ℕ) :
    f (a ^ n) = (f a : N) ^ n := by -- coercions work now
  induction' n with n hn
  · simp; rw [map_one]
  · rw [pow_succ, map_mul, hn, pow_succ]

end MonoidHomClass₂

example {R S : Type*} [Ring R] [Ring S] (f : RingHom₁ R S) (a : R) (n : ℕ) :
    f (a ^ n) = (f a : S) ^ n := by
  rw [MonoidHomClass₂.map_pow]

end MisguidedStuff


class MonoidHomClass₃ (F : Type*) (M N : outParam Type*) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type*) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' _ _ := MonoidHom₁.ext --or equiv, coe_injective' := by intro _ _; exact MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul

section Exo

@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N


class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β] 
   extends DFunLike F α (fun _ ↦ β) where 
  le_of_le : ∀ (f : F) a a', a ≤ a' → f a ≤ f a'

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where  
   coe := OrderPresHom.toFun --by intro a b; apply a.toFun; exact b no lol
   coe_injective' _ _ := OrderPresHom.ext 
   le_of_le := OrderPresHom.le_of_le


instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
  coe f := f.toMonoidHom₁.toFun --somehow Lean is clever enough to accept f.toFun as well lol
  coe_injective' _ _ := OrderPresMonoidHom.ext
  le_of_le := OrderPresMonoidHom.le_of_le

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β where 
     coe f := f.toFun
     coe_injective' _ _ := OrderPresMonoidHom.ext 
     map_one f := f.toMonoidHom₁.map_one
     map_mul f := f.map_mul

--we basically proved the same thing twice, with different ramifications. So, what we should be doing, is defining the common things first and then extend. So

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] : DFunLike (OrderPresMonoidHom α β) α (fun _ ↦ β) where 
 coe f := f.toFun 
 coe_injective' _ _ := OrderPresMonoidHom.ext

--and now we can 

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
  le_of_le := OrderPresMonoidHom.le_of_le

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β where
     map_one f := f.map_one
     map_mul f := f.map_mul

end Exo

end Morphisms

section Subgroups

variable (G : Type*) [Group G]


@[ext]
structure Subgroup₁ where
  /-- The carrier of a subgroup. -/
  carrier : Set G
  /-- The product of two elements of a subgroup belongs to the subgroup. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The inverse of an element of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier
  /-- The unit element belongs to the subgroup. -/
  one_mem : 1 ∈ carrier

variable (H : Subgroup₁ G) (α : Type*) (f : G → α)


/-- Subgroups in `G` can be seen as sets in `G`. -/
instance : SetLike (Subgroup₁ G) G where
  coe := Subgroup₁.carrier
  coe_injective' _ _ := Subgroup₁.ext

variable (H : Subgroup₁ G) (α : Type*) (f : G → α)



instance Subgroup₁Group (H : Subgroup₁ G) : Group H where
  mul x y := 
  { val := x * y 
    property := H.mul_mem x.property y.property} 
  mul_assoc := by
    intro x y z 
    apply SetCoe.ext
    change x.1 * y.1 * z.1 = _ 
    exact mul_assoc _ _ _
  one := ⟨1, H.one_mem⟩
  one_mul x := by 
    apply SetCoe.ext 
    apply one_mul 
  mul_one x := by 
    apply SetCoe.ext; apply mul_one
  inv x := 
  { val := (x.1)⁻¹
    property := H.inv_mem x.2}
  inv_mul_cancel x := by 
    apply SetCoe.ext 
    change (x.1)⁻¹ * x.1 = _
    apply inv_mul_cancel



class SubgroupClass₁ (S : Type*) (G : Type*) [Group G] [SetLike S G] : Prop where
  mul_mem : ∀ (s : S) {a b : G}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

class SubgroupClass₂ (S : Type*) (G : outParam Type*) [Group G] extends SetLike S G where
  mul_mem : ∀ (s : S) {a b : G}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance : SubgroupClass₁ (Subgroup₁ G) G where
  mul_mem := Subgroup₁.mul_mem
  one_mem := Subgroup₁.one_mem
  inv_mem := Subgroup₁.inv_mem

section BadIdea

class SubgroupClass₃ (S : Type*) (G : outParam Type*) [Group G] extends SetLike S G where
  mul_mem : ∀ (s : S) {a b : G}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance : SubgroupClass₃ (Subgroup₁ G) G where
  mul_mem := Subgroup₁.mul_mem
  one_mem := Subgroup₁.one_mem
  inv_mem := Subgroup₁.inv_mem

end BadIdea

/- The intersection of two subgroups is a subgroup.-/

instance : Inf (Subgroup₁ G) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩
      inv_mem := fun ⟨hx, hx'⟩ ↦ ⟨S₁.inv_mem hx, S₂.inv_mem hx'⟩
      }⟩


#synth PartialOrder (Set G)
#synth PartialOrder (Subgroup₁ G) -- ≤ ⊓ ⊔ 

-- Less code duplication this way:
instance : SemilatticeInf (Subgroup₁ G) :=
  {SetLike.instPartialOrder with
   inf := Inf.inf
   inf_le_left := by intro S₁ S₂; rw [SetLike.le_def]; intro x h; rw [← SetLike.mem_coe]; exact
     Set.mem_of_mem_inter_left h
   inf_le_right := by intro S₁ S₂; rw [SetLike.le_def]; intro x h; rw [← SetLike.mem_coe]; exact
     Set.mem_of_mem_inter_right h
   le_inf := by intro R S T h1 h2; rw [SetLike.le_def]; intro x h; replace h1 := h1 h; replace h2 := h2 h; exact ⟨h1, h2⟩
   }
