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
    ∃ l : ℕ →₀ ℤ  , a1 - a2 =  ∑ i ∈ l.support, l i • h i

instance LinCombEquiv : Equivalence (isLinearCombination h) where
  refl := by
    intro x
    rw[isLinearCombination]
    set l : ℕ →₀ ℤ := 0 with hl
    use l
    rw[hl]
    simp only [sub_self, Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero]
  symm := by
    intros x y hxy
    rw[isLinearCombination] at *
    set l := hxy.choose with hl
    set l' : ℕ →₀ ℤ := {
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
    simp only [neg_smul, zsmul_eq_mul, Finset.sum_neg_distrib]
    rw[Finsupp.coe_mk] at hll
    have hl': l = Classical.choose hxy := by rfl
    rw[← hl'] at hll
    simp only [zsmul_eq_mul] at hll
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
    have new : a-c = (a-b) + (b-c) := by ring
    rw[new,hl',hl]
    simp only [zsmul_eq_mul, Pi.add_apply, Int.cast_add]
    have f1 (s : Finset ℕ)(f : ℕ →₀ ℤ )(hs : f.support ⊆ s): ∑ i in s, f i * h i  = ∑ i in f.support, f i * h i := by
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
    simp only [Finsupp.coe_add, Pi.add_apply, Int.cast_add]
    ring


/-Now having made these equivalences, we use Setoid.Classes to make classes on these elements, then creating an
Setoid.IndexedPartition  on ℝ  -/
instance SR : Setoid ℝ where
  r := isLinearCombination h
  iseqv := LinCombEquiv h

@[simp]
lemma equiv_aux(a : ℝ )(b : ℝ)(hb : (isLinearCombination h) a b): (⟦a⟧ : Quotient (SR h)) = (⟦b⟧ : Quotient (SR h)) := Quotient.eq.mpr hb


/-Defining the index set for the partition-/

def E : (Quotient (SR h)) → Set ℝ := λ x => {y : ℝ | x = ⟦y⟧}


/-Defining the Indexed partition-/

instance IndexedPartiononℝ : IndexedPartition (E h) where
  eq_of_mem := by
    intros x i j hxi hxj
    rw[E] at *
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
    rw[E]
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
    rw[E]
    simp only [Set.mem_setOf_eq]



/-We specify that each equivalence class is countable -/
theorem EalphaCountable (α : Quotient (SR h)) : ((E h) α).Countable := by
  rw[E,←Set.countable_coe_iff,countable_iff_exists_injective]
  sorry


theorem Ealphadefault(α : Quotient (SR h)) : ∃ x : ℝ , ⟦x⟧ = α := by
  exact (Quotient.exists_rep α)



/-Enumeration of the set-/
def EnumerateEalpha (α : Quotient (SR h)) : ℕ → ℝ := (Set.enumerateCountable (EalphaCountable h α)  (Ealphadefault h α).choose)


/-Now we define the function F on ℝpartition-/
/-Here, ℝ = ⋃ Eᵅ  where α is chosen from a particular Eᵅ  , which becomes our indexing set-/
/-Prove that Eᵅ is countable for each α   -/

/- Define a ennumeration {xᵢᵅ} for each Eᵅ. -/

/-Let Eᵅᵢ = {xᵢᵅ} ∪  ⋃ⱼ {xᵢᵅ + hⱼ} , where j ∈ ℕ   -/
def Ealphai1 (α : Quotient (SR h))(i : ℕ) (n: ℕ) : Set ℝ := {(EnumerateEalpha h α i) + h n}

def Ealpha0 (α : Quotient (SR h))(i : ℕ) : Set ℝ := {EnumerateEalpha h α i}

def Ealphai (α : Quotient (SR h))(i : ℕ) : Set ℝ := Ealpha0 h α i ∪ ⋃ n, Ealphai1 h α i n

lemma EalphaUnionEalphai_aux (α : Quotient (SR h)) : (Ealphadefault h α).choose ∈ E h α := by
  rw[E]
  simp only [Set.mem_setOf_eq]
  exact ((Ealphadefault h α).choose_spec).symm


lemma EalphaUnionEalphai_aux1 (α : Quotient (SR h)) : Set.range (EnumerateEalpha h α) = E h α  := by
  rw[EnumerateEalpha]
  apply Set.range_enumerateCountable_of_mem
  exact EalphaUnionEalphai_aux h α

lemma EnumerateEalpha_injective (α : Quotient (SR h)) : Function.Injective (EnumerateEalpha h α) := by
  rw[EnumerateEalpha]

  sorry

lemma EalphaUnionEalphai_aux2(α : Quotient (SR h)) : ⟦ EnumerateEalpha h α i ⟧ = α := by
  have lem : EnumerateEalpha h α i ∈ E h α := by
    rw[←EalphaUnionEalphai_aux1 h α]
    simp only [Set.mem_range, exists_apply_eq_apply]
  rw[E] at lem
  simp at lem
  exact lem.symm

/-Prove that Eᵅ = ⋃ᵢ Eᵅᵢ , where i ∈ ℕ -/
lemma EalphaUnionEalphai (α : Quotient (SR h)) : (E h α) = ⋃ i, Ealphai h α i := by
  apply subset_antisymm
  intro x hx
  have h1 : E h α ⊆ Set.range (EnumerateEalpha h α) := by
    apply Set.subset_range_enumerate
  have h2 : x ∈ Set.range (EnumerateEalpha h α) := by
    exact h1 hx
  obtain ⟨i,hi⟩ := Set.mem_range.mp h2
  apply Set.mem_iUnion_of_mem i
  simp only [Ealphai, Ealpha0, Set.singleton_union, Set.mem_insert_iff, Set.mem_iUnion]
  left
  exact hi.symm
  apply Set.iUnion_subset
  intro i
  simp[Ealphai]
  constructor
  rw[Ealpha0]
  rw[←EalphaUnionEalphai_aux1]
  simp only [Set.singleton_subset_iff, Set.mem_range, exists_apply_eq_apply]
  intro j
  rw[Ealphai1,E]
  simp only [Set.singleton_subset_iff, Set.mem_setOf_eq]
  have lemma2 : ⟦ EnumerateEalpha h α i⟧ = α := EalphaUnionEalphai_aux2 h α
  nth_rewrite 1 [← lemma2]
  apply equiv_aux
  rw[isLinearCombination]
  set l : ℕ →₀ ℤ := {
    support := {j},
    toFun := λ i => if i = j then -1 else 0,
    mem_support_toFun := by
      intro j1
      constructor
      intro hj
      simp only [Int.reduceNeg, ne_eq, ite_eq_right_iff, neg_eq_zero, one_ne_zero, imp_false,
        Decidable.not_not]
      simp only [Finset.mem_singleton] at hj
      assumption
      simp only [Int.reduceNeg, ne_eq, ite_eq_right_iff, neg_eq_zero, one_ne_zero, imp_false,
        Decidable.not_not, Finset.mem_singleton, imp_self]
  } with hl
  use l
  simp only [sub_add_cancel_left, zsmul_eq_mul, Finset.sum_singleton]
  have lem : ↑(l j) = -1 := by
    rw[hl]
    simp only [Int.reduceNeg, Finsupp.coe_mk, ↓reduceIte]
  rw[lem]
  ring

/-Let Rᵅₘ = Eᵅₘ \ ⋃ⱼ Eᵅⱼ where j ∈ {1,2..m-1} if m ≥ 2  and Rᵅ₁ = Eᵅ₁.-/
def Ralpha (α : Quotient (SR h))(m : ℕ) : Set ℝ :=  match m with
  | 0 => Ealphai h α 0
  | i + 1 => Ealphai h α (i + 1) \( ⋃  j ∈ Finset.range (i+1), Ealphai h α j)

/-Prove that there exists some N₀ st. xᵅₘ  + hₙ ∈ Rᵅₘ ∀ n ≥ N₀ -/
/-Proof Sketch :- consider an open interval I st. xᵅⱼ ∉ I for j ≤ m-1 (If m = 1, our case is already satisfied). -/
def I (α : Quotient (SR h))(m : ℕ) : Set ℝ := by
  set p := EnumerateEalpha h α m with hp
  have main(n : ℕ)(hn : n ∈ Finset.range (m)) :  ¬ (∀ ε > 0, (EnumerateEalpha h α n) ∈  (Metric.ball p ε)) := by
    by_contra lem
    set d := |(EnumerateEalpha h α n) - p|/2 with hd1
    have hd : d > 0 := by
      rw[hd1,hp]
      simp only [gt_iff_lt, Nat.ofNat_pos, div_pos_iff_of_pos_right, abs_pos, ne_eq]
      intros h2
      have h3 : EnumerateEalpha h α n = EnumerateEalpha h α m := by
        linarith
      have h4 : n =m := by
        apply EnumerateEalpha_injective
        rw[h3]
      rw[h4] at hn
      simp only [Finset.mem_range, lt_self_iff_false] at hn
    specialize lem d hd
    rw[Real.ball_eq_Ioo] at lem
    rw[Set.Ioo,hd1] at lem
    simp only [Set.mem_setOf_eq] at lem
    have lem1 := lem.1
    have lem2 := lem.2
    have lem3 : p - EnumerateEalpha h α n < |(EnumerateEalpha h α n) - p|/2 := by
      linarith
    have lem4 : EnumerateEalpha h α n - p < |(EnumerateEalpha h α n) - p|/2 := by
      linarith
    have lem5 : p ≤ (EnumerateEalpha h α n) ∨  (EnumerateEalpha h α n) < p := le_or_lt p (EnumerateEalpha h α n)
    cases lem5
    case inl hp1 =>
      have lem6 : |(EnumerateEalpha h α n) - p| = (EnumerateEalpha h α n) - p := by
        rw[abs_eq_self]
        linarith
      linarith
    case inr hp1 =>
      have lem6 : |(EnumerateEalpha h α n) - p| =  -((EnumerateEalpha h α n) - p) := by
        rw[abs_eq_neg_self]
        linarith
      linarith
  push_neg at main

  sorry

/- Then choose N₁ st.  Aⱼ = {xᵅⱼ + hₙ, n ≥ N₁} where j≤m and I∩Aⱼ = ∅ ∀ j≤m-1 and Aₘ ⊆ I .-/
/-This implies Aₘ ∩ Aⱼ = ∅ ∀ j ≤ m-1  -/

/-Then remove all  the finite points from
  Aₘ that come from Bⱼ = {xᵅⱼ + hₙ, n ≤  N₁} where j≤m, call it A-/
/-A contains a set Cₘ st. ∃ ℕ₂ C = {xᵅⱼ + hₙ, n ≥ ℕ₂}. Then C ⊆ Rᵅₘ  -/
/-Thus ∀ n ≥ N₂
F(xₘᵅ +hₙ) - F(xₘᵅ) / hₙ  = (F(xₘᵅ) + (xᵅₘ + hₙ - xₘᵅ)f(xₘᵅ) - F(xₘᵅ))/hₙ  = f(xᵅₘ)ₙ-/

lemma Ralphanonemptyexistence (α : Quotient (SR h))(m : ℕ) : ∀ᶠ (n:ℕ) in atTop, EnumerateEalpha h α m + h n ∈ Ralpha h α m := by

  sorry



/- Prove that Eᵅ = ⋃ₘ Rᵅₘ. make this an indexed partition -/

/- # Defining F on Eᵅ-/

/-For each  x ∈  Rᵅₘ, if x ≠ xᵅₘ , then F(x) = F(xₘᵅ) + (x - xₘᵅ)f(xₘᵅ)  otherwise  F(x) = 0 where x = xₘᵅ-/
/-lift this F to Eᵅ by using Indexed.PartitionPiecewise-/

/-# Defining F on ℝ -/
/-Lift this F to ℝ by  using Indexed.PartitionPiecewise.-/

/-If x ∈ ℝ → ∃ n,α st. x = xᵅₘ -/

/-Prove that there exists some N₀ st. xᵅₘ  + hₙ ∈ Rᵅₘ ∀ n ≥ N₀ -/


end CounterExample1

namespace CounterExample2

/-## CounterExample 2 -/
/-Given any closed subinterval [a,b] of ℝ with a < b and any sequence ${hₙ}$ with n ∈ ℕ of nonzero real numbers converging to 0, there exists a continuous function F:[a,b] → ℝ s.t.   -/
/-for any measurable function f : [a,b] → ℝ there exists a subsequence ${hₗ}$ where l ⊆ ℕ  such that :-  -/
/- lim {k → ∞} (F(x + hₗ) - F(x))/hₗ  = f(x) almost everywhere on [a,b].  -/
/- By Lusin'a Approximation theorem, f(x) is continuous in a subset R of [a,b] where μ([a,b]\R) < ε, it is also a bounded continous function  -/
/-# Proof -/

/-By Weirstrass Approximation theorem, there exists a sequence of polynomial functions {Pₖ}, such that they converge to f almost everywhere -/
/-Consider the set A ⊆ C[a,b] which contains functions like g which satisfy :- -/
/-((g(x + hₘ) - g(x))/hₘ - Pₖ) < 1/n. holds except for points that have lebesgue measure < 1/n. -/
/-Let S = C[a,b] \ A -/
/-Sₙₖ be subsets of S that contain elements g which satisfy ∀ m > n:--/
/-((g(x + hₘ) - g(x))/hₘ - Pₖ) ≥ 1/n holds on some set having lebesgue lebesgue measure > 1/n -/
/-Prove that S = ∪Sₙₖ ∀ k,n -/
/-Now show Sₙₖ is nowhere dense in C[a,b] by showing it is closed and C[a,b]\Sₙₖ is dense in C[a,b] for all positive integers n and k.  -/
/-If Sₙₖ is empty then the result is already true. Say, Sₙₖ is non-empty and there exists a sequence of functions {gₘ} in Sₙₖ that converge to g. We prove that g ∈ Sₙₖ.-/
/-Chhose ε> 0 such that there exists N ∈ ℕ such that ∀ m ≥ N, ‖gₘ(x) - g(x) ‖ < ε ∀ x ∈ [a,b].Then for m>n, and j > n  we see that -/
/-‖ (gₘ(x + hⱼ) - gₘ(x))/hⱼ - (g(x + hⱼ) - g(x))/hⱼ ‖ ≤ ‖ (gₘ(x + hⱼ) - g(x + hⱼ))/hⱼ‖ + ‖ (gₘ(x) - g(x))/hⱼ‖  ≤ 2ε/|hⱼ|-/
/-Now use the property that each gₘ ∈ Sₙₖ for all integers j > n on a set having lebesgue measure not less than 1/n we see that,-/
/-2ε/|hⱼ| ≥  ‖ (gₘ(x + hⱼ) - gₘ(x))/hⱼ - (g(x + hⱼ) - g(x))/hⱼ ‖  = ‖ (gₘ(x + hⱼ) - gₘ(x))/hⱼ -Pₖ - ((g(x + hⱼ) - g(x))/hⱼ - Pₖ) ‖ ≥ ‖ (gₐ(x + hⱼ) - gₘ(x))/hⱼ -Pₖ‖ - ‖ (g(x + hⱼ) - g(x))/hⱼ -Pₖ ‖ ≥ 1/n - ‖ (g(x + hⱼ) - g(x))/hⱼ -Pₖ ‖ -/
/-‖ (g(x + hⱼ) - g(x))/hⱼ -Pₖ ‖ ≥ 1/n - 2ε/|hⱼ| -/
/-This proves that g ∈ Sₙₖ , and hence Sₙₖ is closed. -/
/- Formalizing the Cantor function along with the fact that it's derivative is 0 almost everywhere. denote it by Can(x)-/
/-Let g ∈ Sₙₖ ,and Rₖ(x) be a polynomial such that Rₖ'(x) = P(x)-/
/-Find a partition of [a,b] :- {a₀,a₂ ⋯ aₙ} such that:- -/
/-sup ‖ g(x) - g(y) ‖ < ε/2 and sup ‖ Rₖ(x) - Rₖ(y) ‖ < ε/2 when x,y ∈[aᵢ,aᵢ₊₁]   -/
/-Construct a piecewise function Hᵢ(k) such that -/
/-Hᵢ(x) = g(aᵢ) - Rₖ(aᵢ) + (g(aᵢ₊₁) - Rₖ(aᵢ₊₁) + Rₖ(aᵢ) - g(aᵢ))Can((x-aᵢ₊₁)/(aᵢ - aᵢ₊₁))  -/
/-Then lift Hᵢ(x) to H(x)-/
/-h(x) = Rₖ(x) + H(x) -/
/-Then h'(x) = Pₖ(x) almost everywhere , so h(x) ∈ C[a,b]\Sₙₖ -/
/-Then show ‖ h(x) - g(x) ‖ ≤  ε  -/
/-Thus C[a,b]\Sₙₖ in C[a,b], Sₙₖ is nowhere dense in C[a,b]. Here C[a,b] is a complete normed space , so it is a baire space.  -/
/-Thus S is nowhere dense, and C[a,b]\S is non-empty,and we are done.-/
end CounterExample2

namespace CounterExample3
/-There exists a bounded Lebesgue Integrable Function $f : [0,1] → ℝ$ such that for all the functions g : [0,1] → ℝ which is equal to f almost everywhere with respect to the lebesgue measure, is never Riemann Integrable-/
/-## Proof-/
/-Let A be a set which is contained in [0,1] and has lebesgue measure less than 1 and contains all the rationals in [0,1]. -/
/- This is constructed by sets Ioo(rₙ - 1/2ⁿ, rₙ + 1/2ⁿ )  where rₙ is an enumeration of the rationals -/
/- Let the bounded integrable function f be the Indicator function on A. -/
/-If g is equal to A almost everywhere, then there exists a null set:= N s.t g(x) = 1 ∀ A\N and g(x) = 0 for x ∉ N ∪ A -/
/-We then use the fact that every bounded Riemann Integrable function is continuous almost everywhere.-/
/-Since A is open and dense in [0,1], A\N is dense in [0,1]  and (A∪N)ᶜ has some finite measure. -/

/- # Proof-/
/-A is open and dense in [0,1], so for any open interval I in [0,1], I∩A ≠ ∅. Thus ∃ an open interval I₁ such that I₁ ⊆ I∩A-/
/-μ(I∩A) > 0  -/
/- μ(A∩I) = μ(A∩I∖N) + μ(A∩I∩N) = μ(A∩I\N) ≤ μ(A\N)-/
/-So, g is discontinuous at all the points (A∪N)ᶜ-/
end CounterExample3
