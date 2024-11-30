import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib
set_option autoImplicit true

noncomputable section
namespace CounterExample1

/- The plan of the project is to formalize some Counter Examples in analysis. -/

/-The formal statement of the theorem is :-
Given a Real Valued function f : ℝ → ℝ, let {hₙ} be a sequence of real numbers converging to 0. Then there exists a function
F : ℝ → ℝ such that
lim{n → ∞} [F(x + hₙ) - F(x)]/hₙ = f(x). -/

/-Defining the sequence which tends to 0-/
variable (h : ℕ → ℝ) (h1 : Filter.Tendsto h atTop (nhds 0))(f : ℝ → ℝ)

/-First define the equivalence relation-/
def isLinearCombination(a1 : ℝ)(a2 : ℝ) : Prop :=
    ∃ l : ℕ →₀ ℝ , a1 - a2 =  ∑ i ∈ l.support, l i • h i

instance LinCombEquiv : Equivalence (isLinearCombination h) where
  refl := by
    intro x
    rw[isLinearCombination]
    set l : ℕ →₀ ℝ := 0 with hl
    use l
    rw[hl]
    simp only [sub_self, Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero]
  symm := by
    intros x y hxy
    rw[isLinearCombination] at *
    set l := hxy.choose with hl
    set l' : ℕ →₀ ℝ := {
      support := l.support,
      toFun := λ i => - (l.toFun i),
      mem_support_toFun := by
        intro i
        rw[l.mem_support_toFun]
        simp only [ne_eq, neg_eq_zero]
    } with hl'
    use l'
    rw[hl']
    simp only [Finsupp.coe_mk, smul_eq_mul, neg_mul, Finset.sum_neg_distrib]
    have hll := hxy.choose_spec
    rw[←hl] at hll
    simp only [Finsupp.coe_mk,smul_eq_mul] at hll
    rw[Finsupp.coe_mk] at hll
    have hl': l = Classical.choose hxy := by rfl
    rw[← hl'] at hll
    rw[← hll]
    simp only [neg_sub]
  trans := by
    intros a b c hxy hyz
    rw[isLinearCombination] at *
    obtain ⟨l,hl⟩ := hxy
    obtain ⟨l',hl'⟩ := hyz
    set l'' := l + l' with hl''
    use l''
    rw[hl'']
    simp only [ Pi.add_apply, smul_eq_mul]
    have new : a-c = (a-b) + (b-c) := by ring
    rw[new,hl',hl]
    simp only [smul_eq_mul]
    have f1 (s : Finset ℕ)(f : ℕ →₀ ℝ )(hs : f.support ⊆ s): ∑ i in s, f i * h i  = ∑ i in f.support, f i * h i := by
      rw[Finset.sum_subset hs]
      intros x hx  hxs
      rw[Finsupp.not_mem_support_iff] at hxs
      rw[hxs]
      ring
    set s := l.support ∪ l'.support with hs
    have hss : l.support ⊆ s := by
      rw[hs]
      exact Finset.subset_union_left
    have hss' : l'.support ⊆ s := by
      rw[hs]
      exact Finset.subset_union_right
    have hs1 : (l + l').support ⊆ s := by
      rw[hs]
      exact Finsupp.support_add
    rw[← f1 s l hss,← f1 s l' hss',← f1 s (l+l') hs1,← Finset.sum_add_distrib]
    apply Finset.sum_congr
    rfl
    intros x hx
    simp only [Finsupp.add_apply]
    ring

instance ℝhasequiv : HasEquiv ℝ := ⟨isLinearCombination h⟩

/-Now having made these equivalences, we use Setoid.Classes to make classes on these elements, then creating an
Setoid.IndexedPartition  on ℝ  -/
instance SR : Setoid ℝ where
  r := isLinearCombination h
  iseqv := LinCombEquiv h

/-Defining the index set for the partition-/

def s : (Quotient (SR h)) → Set ℝ := λ x => {y : ℝ | x = ⟦y⟧}

/-Defining the Indexed partition-/

instance IndexedPartion : IndexedPartition (s h) where
  eq_of_mem := by
    intros x i j hxi hxj
    rw[s] at *
    simp at *
    rw[hxi,hxj]
  some := by
    intros x
    have qrepr : ∃ (a : ℝ), Quotient.mk (SR h) a = x := by
      exact Quotient.exists_rep x
    set y :=  qrepr.choose with hy
    exact y
  some_mem := by
    intros x
    rw[s]
    simp only [Set.mem_setOf_eq]
    have qrepr : ∃ (a : ℝ), Quotient.mk (SR h) a = x := by
      exact Quotient.exists_rep x
    set y :=  qrepr.choose with hy
    rw[hy,Eq.comm]
    exact qrepr.choose_spec
  index := by
    intros x
    exact ⟦x⟧
  mem_index := by
    intros x
    rw[s]
    simp only [Set.mem_setOf_eq]

/-Now we define the function F on ℝpartition-/



/-Here, ℝ = ⋃ Eᵅ  where α is chosen from a particular Eᵅ  , which becomes our indexing set-/
/-Prove that Eᵅ is countable for each α   -/
/- Define a ennumeration {xᵢᵅ} for each Eᵅ. with α = x₁ᵅ -/
/-Let Eᵅᵢ = {xᵢᵅ} ∪  ⋃ⱼ {xᵢᵅ + hⱼ} , where j ∈ ℕ   -/

/-Prove that Eᵅ = ⋃ᵢ Eᵅᵢ , where i ∈ ℕ -/
/-Let Rᵅₘ = Eᵅₘ \ ⋃ⱼ Eᵅⱼ where j ∈ {1,2..m-1} if m ≥ 2  and Rᵅ₁ = Eᵅ₁.-/

/- Prove that Eᵅ = ⋃ₘ Rᵅₘ. make this an indexed partition -/

/- # Defining F on Eᵅ-/

/-For each  x ∈  Rᵅₘ, if x ≠ xᵅₘ , then F(x) = F(xₘᵅ) + (x - xₘᵅ)f(xₘᵅ)  otherwise  F(x) = 0 where x = xₘᵅ-/
/-lift this F to Eᵅ by using Indexed.PartitionPiecewise-/

/-# Defining F on ℝ -/
/-Lift this F to ℝ by  using Indexed.PartitionPiecewise.-/

/-If x ∈ ℝ → ∃ n,α st. x = xᵅₘ -/

/-Prove that there exists some N₀ st. xᵅₘ  + hₙ ∈ Rᵅₘ ∀ n ≥ N₀ -/
/-Proof Sketch :- consider an open interval I st. xᵅⱼ ∉ I for j ≤ m-1 (If m = 1, our case is already satisfied). -/
/- Then choose N₁ st.  Aⱼ = {xᵅⱼ + hₙ, n ≥ N₁} where j≤m and I∩Aⱼ = ∅ ∀ j≤m-1 and Aₘ ⊆ I .-/
/-This implies Aₘ ∩ Aⱼ = ∅ ∀ j ≤ m-1  -/

/-Then remove all  the finite points from
  Aₘ that come from Bⱼ = {xᵅⱼ + hₙ, n ≤  N₁} where j≤m, call it A-/
/-A contains a set Cₘ st. ∃ ℕ₂ C = {xᵅⱼ + hₙ, n ≥ ℕ₂}. Then C ⊆ Rᵅₘ  -/
/-Thus ∀ n ≥ N₂
F(xₘᵅ +hₙ) - F(xₘᵅ) / hₙ  = (F(xₘᵅ) + (xᵅₘ + hₙ - xₘᵅ)f(xₘᵅ) - F(xₘᵅ))/hₙ  = f(xᵅₘ)ₙ-/

end CounterExample1

namespace CounterExample2

/-## CounterExample 2 -/
/-Given any closed subinterval [a,b] of ℝ with a < b and any sequence ${hₙ}$ with n ∈ ℕ of nonzero real numbers converging to 0, there exists a continuous function F:[a,b] → ℝ s.t.   -/
/-for any measurable function f : [a,b] → ℝ there exists a subsequence ${hₗ}$ where l ⊆ ℕ  such that :-  -/
/- lim {k → ∞} (F(x + hₗ) - F(x))/hₗ  = f(x) almost everywhere on [a,b]  -/
/-# Proof -/
/- -/
end CounterExample2

namespace CounterExample3
/-There exists a Lebesgue Integrable Function $f : ℝ → ℝ$ such that for all   -/
end CounterExample3
