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
variable (h : ℕ → ℝ) (h1 : Filter.Tendsto h Filter.atTop (nhds 0))(f : ℝ → ℝ)

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


/-Prove that there exists some N₀ st. xᵅₘ  + hₙ ∈ Rᵅₘ ∀ n ≥ N₀ -/
lemma I_constructor (α : Quotient (SR h))(m : ℕ)(n : ℕ)(hn : n ∈ Finset.range (m)) : ¬ (∀ ε > 0, (EnumerateEalpha h α n) ∈  (Metric.closedBall (EnumerateEalpha h α m) ε)) := by
  set p := EnumerateEalpha h α m with hp
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
  rw[Real.closedBall_eq_Icc] at lem
  rw[Set.Icc,hd1] at lem
  simp only [Set.mem_setOf_eq] at lem
  have lem1 := lem.1
  have lem2 := lem.2
  have lem3 : p - EnumerateEalpha h α n ≤  |(EnumerateEalpha h α n) - p|/2 := by
    linarith
  have lem4 : EnumerateEalpha h α n - p ≤  |(EnumerateEalpha h α n) - p|/2 := by
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

def fconst(α : Quotient (SR h))(m : ℕ)(x : ℕ)(hx : x ∈ Finset.range m) : {y : ℝ // y > 0 ∧ (EnumerateEalpha h α x) ∉ (Metric.closedBall (EnumerateEalpha h α m) y)}  := by
  have main(n : ℕ)(hn : n ∈ Finset.range (m)) : ¬ (∀ ε > 0, (EnumerateEalpha h α n) ∈  (Metric.closedBall (EnumerateEalpha h α m) ε)) := by
    apply I_constructor
    exact hn
  push_neg at main
  specialize main x hx
  constructor
  exact main.choose_spec

def fconst' (α : Quotient (SR h))(m : ℕ)(x : ℕ) : ℝ := by
  if x ∈ Finset.range m then
   rename_i hx
   exact (fconst h α m x hx).1
  else
    exact 0

def elist(α : Quotient (SR h))(m : ℕ)(x : ℕ)(hx : x ∈ Finset.range m): List ℝ :=
  match x with
  | 0 => [(fconst h α m (0) hx).1]
  | y + 1 => by
    have hy : y ∈ Finset.range (m) := by
      simp only [Finset.mem_range] at *
      linarith
    exact (fconst h α m (y+1) hx).1 :: (elist α m y hy)

lemma elist_nonempty(α : Quotient (SR h))(m : ℕ)(x : ℕ)(hx : x ∈ Finset.range m)  : 0 < (elist h α m x hx).length := by
  rw[List.length_pos]
  simp only [ne_eq]
  by_contra h1
  rw[elist.eq_def] at h1
  simp at h1
  match x with
  | 0 =>
    simp only [List.cons_ne_self] at h1
  |y + 1 =>
    simp only [reduceCtorEq] at h1

def elist_min(α : Quotient (SR h))(m : ℕ)(x : ℕ)(hx : x ∈ Finset.range m) : ℝ := List.minimum_of_length_pos (elist_nonempty h α m x hx )


lemma elist_min_mem(α : Quotient (SR h))(m : ℕ)(x : ℕ)(hx : x ∈ Finset.range m) : elist_min h α m x hx ∈ elist h α m x hx := by
  apply List.minimum_of_length_pos_mem

lemma elist_length(α : Quotient (SR h))(m : ℕ)(n : ℕ)(hn : n ∈ Finset.range m)(hm1 : m -1 ∈ Finset.range m) : (elist h α m n hn).length > n := by
  match n with
  | 0 =>
    rw[elist]
    simp only [List.length_singleton, gt_iff_lt, zero_lt_one]
  | x + 1 =>
    rw[elist]
    simp only [List.length_cons, gt_iff_lt, add_lt_add_iff_right]
    apply elist_length
    exact hm1

lemma I_constructor_aux3(r : ℝ)(α : Quotient (SR h))(m : ℕ)(hm : m > 0)(p : ℝ)(hp : p = EnumerateEalpha h α m)(n : ℕ)(hn : n ∈ Finset.range (m))(m1 : ℕ)(hnm1 : m1 ≥ n)(hm1 : m1 ∈ Finset.range m)(hr : r = (elist h α m m1 hm1)[m1 - n]!): r < dist (EnumerateEalpha h α n) p:= by
  rw[elist.eq_def] at hr
  match m1 with
  | 0 =>
    have hn1 : n = 0 := by
      linarith
    simp only [hn1, List.getElem!_cons_zero] at hr
    rw[hn1]
    have hp1 : EnumerateEalpha h α 0 ∉ Metric.closedBall p r:= by
      simp_rw[hp,hr]
      apply (fconst h α m 0 hm1).2.2
    simp only [Metric.mem_closedBall, not_lt,not_le] at hp1
    assumption
  | x + 1 =>
    have triv : x + 1 ≠ 0 := by simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
      and_false, not_false_eq_true]
    simp[triv] at hr
    by_cases hn1 : n = x + 1
    rw[hn1] at hr
    simp at hr
    rw[hn1]
    have hp1 : EnumerateEalpha h α (x+1) ∉ Metric.closedBall p r:= by
      simp_rw[hp,hr]
      apply (fconst h α m (x+1) hm1).2.2
    simp only [Metric.mem_closedBall, not_lt,not_le] at hp1
    assumption
    have triv2 :  n ≤ x := by
      apply Nat.le_of_lt_succ
      rw[Nat.lt_iff_le_and_ne]
      constructor
      all_goals assumption
    have triv1 : (x +1) - n = (x - n) + 1 := by
      rw[Nat.succ_sub]
      assumption
    rw[triv1] at hr
    rw[List.getElem!_cons_succ] at hr
    apply I_constructor_aux3 r
    repeat assumption




lemma I_constructor_aux2(α : Quotient (SR h))(m : ℕ)(hm : m > 0)(p : ℝ)(hp : p = EnumerateEalpha h α m)(n : ℕ)(hn : n ∈ Finset.range (m))(hm1 : m -1 ∈ Finset.range m): ∃ r ∈  elist h α m (m-1) hm1, r < dist (EnumerateEalpha h α n) p:= by
  have hr'' : (elist h α m (m-1) hm1).length > (m-1)-n := by
    have hr' : (elist h α m (m-1) hm1).length > (m-1) := by
      apply elist_length
      assumption
    apply lt_of_lt_of_le'
    exact hr'
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
  set r := (elist h α m (m-1) hm1)[m-1 -n]! with hr
  use r
  constructor
  rw[hr,getElem!_pos]
  apply List.getElem_mem
  apply hr''
  apply I_constructor_aux3 h r α m hm p hp n hn (m-1)
  simp only [Finset.mem_range] at hn
  apply Nat.le_pred_of_lt
  assumption
  assumption



lemma eset_min_form(α : Quotient (SR h))(m : ℕ)(x : ℕ)(hm : m > 0)(hx : x ∈ Finset.range m) :∃ y, y ∈ Finset.range m ∧  elist_min h α m x hx = (fconst' h α m y) := by
  have eset_min_mem1 := elist_min_mem h α m x hx
  rw[elist.eq_def] at eset_min_mem1
  match x with
  | 0 =>
    simp only [List.mem_singleton] at eset_min_mem1
    use 0
    constructor
    simp only [Finset.mem_range]
    assumption
    rw[fconst']
    simp only [hx, ↓reduceDIte]
    assumption
  | x + 1 =>
    simp only [List.mem_cons] at eset_min_mem1
    by_cases h1 : elist_min h α m (x+1) hx = (fconst h α m (x+1) hx).1
    use x + 1
    constructor
    assumption
    rw[fconst']
    simp only [hx, ↓reduceDIte]
    assumption
    simp only [h1, false_or] at eset_min_mem1
    have hx1 : x ∈ Finset.range m := by
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_range]
      linarith
    have elist_min_eq : elist_min h α m x hx1 = elist_min h α m (x+1) hx := by
      rw[eq_iff_le_not_lt]
      constructor
      rw[elist_min]
      apply List.minimum_of_length_pos_le_of_mem
      assumption
      simp only [not_lt]
      rw[elist_min]
      apply List.minimum_of_length_pos_le_of_mem
      rw[elist.eq_def]
      have hx2 : x + 1 ≠ 0 := by
        simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
          not_false_eq_true]
      simp only [List.mem_cons]
      right
      exact elist_min_mem h α m (x) hx1
    rw[← elist_min_eq]
    apply eset_min_form
    assumption



#check Nat.eq_iff_le_and_ge

lemma I_constructor_aux(α : Quotient (SR h))(m : ℕ)(hm : m > 0): ∃ ε₀ > 0 , ∀ n ∈ Finset.range (m), (EnumerateEalpha h α n) ∉  (Metric.closedBall (EnumerateEalpha h α m) ε₀) := by
  set p := EnumerateEalpha h α m with hp
  have main(n : ℕ)(hn : n ∈ Finset.range (m)) : ¬ (∀ ε > 0, (EnumerateEalpha h α n) ∈  (Metric.closedBall (EnumerateEalpha h α m) ε)) := by
    apply I_constructor
    exact hn
  push_neg at main
  have lem : m -1 ∈ Finset.range m := by
    simp only [Finset.mem_range]
    simp only [tsub_lt_self_iff, zero_lt_one, and_true]
    assumption
  set m1 := m -1 with hm1
  set ε₀ := elist_min h α m m1 lem with hε₀
  use ε₀
  constructor
  have hε₀1 : ∃ y, y ∈ Finset.range m ∧  ε₀ = (fconst' h α m y) := by
    rw[hε₀]
    apply eset_min_form
    assumption
  obtain ⟨y,hy1,hy2⟩ := hε₀1
  rw[fconst'] at hy2
  simp only [hy1, ↓reduceDIte] at hy2
  rw[hy2]
  exact ((fconst h α m y hy1).2).1
  intro n hn
  simp only [Metric.mem_closedBall, not_lt,not_le]
  rw[hε₀,elist_min]
  have some_lem : ∃ r ∈ elist h α m m1 lem, r < dist (EnumerateEalpha h α n) p:= by
    apply I_constructor_aux2 h α m hm p hp n hn lem
  apply LE.le.trans_lt
  any_goals exact some_lem.choose_spec.2
  apply List.minimum_of_length_pos_le_of_mem
  exact some_lem.choose_spec.1



/-Proof Sketch :- consider an open interval I st. xᵅⱼ ∉ I for j ≤ m-1 (If m = 1, our case is already satisfied). -/
def I (α : Quotient (SR h))(m : ℕ)(hm : m > 0) : Set ℝ := by
  set p := EnumerateEalpha h α m with hp
  set ε₀ := (I_constructor_aux h α m hm).choose with hε₀
  exact Metric.closedBall p ε₀

lemma I_nonempty(α : Quotient (SR h))(m : ℕ)(hm : m > 0) : (I h α m hm).Nonempty := by
  rw[I,Metric.nonempty_closedBall]
  apply le_of_lt
  exact (I_constructor_aux h α m hm).choose_spec.1

lemma I_property(α : Quotient (SR h))(m : ℕ)(hm : m > 0) : ∀ n ∈ Finset.range (m), (EnumerateEalpha h α n) ∉  (I h α m hm) := by
  intro n hn
  rw[I]
  exact (I_constructor_aux h α m hm).choose_spec.2 n hn

/--Property describing membership of elements in I -/
def p (α: Quotient (SR h))(m : ℕ)(hm : m > 0)(n : ℕ)(hn : n ∈ Finset.range m)(x : ℕ ) : Prop := by
  match n with
  | 0 =>
    exact EnumerateEalpha h α 0 + h x ∉ I h α m hm
  | y + 1 =>
    have hy : y ∈ Finset.range m := by
      simp only [Finset.mem_range] at *
      linarith
    exact EnumerateEalpha h α (y+1) + h x ∉ I h α m hm ∧ p α m hm y hy x



include h1
lemma distance_equiv : ∀ ε > 0, ∃ N, ∀ n ≥ N, |h n| < ε := by
  rw[Filter.HasBasis.tendsto_iff Filter.atTop_basis (nhds_basis_Ioo_pos 0)] at h1
  simp only [Set.mem_Ici, zero_sub, zero_add] at h1
  intros e he
  specialize h1 e he
  obtain ⟨N,hN⟩ := h1
  use N
  simp only [Set.mem_Ioo, true_and] at hN
  intros n hnN
  specialize hN n hnN
  rw[abs_lt]
  assumption


include h1
lemma I_eventually_property(α : Quotient (SR h))(m : ℕ)(hm : m > 0)(n : ℕ)(hn : n ∈ Finset.range m) : ∀ᶠ n1 in Filter.atTop  , EnumerateEalpha h α n + h n1 ∉ I h α m hm  := by
  rw[Filter.eventually_atTop,I,Metric.closedBall]
  set ε₀ := (I_constructor_aux h α m hm).choose with hε₀
  simp only [ge_iff_le, gt_iff_lt, Finset.mem_range, not_lt, Set.mem_setOf_eq,dist,Metric.mem_closedBall, not_le]
  have he1 : ε₀ > 0 := by
    rw[hε₀]
    exact (I_constructor_aux h α m hm).choose_spec.1
  have he : (EnumerateEalpha h α n) ∉  (Metric.closedBall (EnumerateEalpha h α m) ε₀) := by
    exact (I_constructor_aux h α m hm).choose_spec.2 n hn
  have he2 : ε₀ < |EnumerateEalpha h α n - EnumerateEalpha h α m| := by
    simp only [Metric.mem_closedBall, not_le,dist] at he
    exact he
  set s := |EnumerateEalpha h α n - EnumerateEalpha h α m| with hs
  set t := (s - ε₀)/2 with ht
  have ht1 : t > 0 := by
    rw[ht]
    linarith
  have traingle(b : ℕ) : |EnumerateEalpha h α n - EnumerateEalpha h α m| - |h b| ≤  |(EnumerateEalpha h α n - EnumerateEalpha h α m) + h b| := by
    rw[← abs_neg (h b)]
    trans
    apply abs_sub_abs_le_abs_sub
    simp only [sub_neg_eq_add, le_refl]
  have ht2 : ε₀ < s - t := by
    rw[ht,hs]
    linarith
  obtain ⟨N,hN1⟩ := distance_equiv h h1 t ht1
  use N
  intros b hb
  specialize hN1 b hb
  specialize traingle b
  have hst : s - t < s - |h b| := by
    linarith
  rw[← hs] at traingle
  trans
  exact ht2
  apply lt_of_lt_of_le
  exact hst
  trans
  exact traingle
  ring_nf
  simp only [le_refl]


/- Then choose N₁ st.  Aⱼ = {xᵅⱼ + hₙ, n ≥ N₁} where j≤m and I∩Aⱼ = ∅ ∀ j≤m-1 and Aₘ ⊆ I .-/
/-This implies Aₘ ∩ Aⱼ = ∅ ∀ j ≤ m-1  -/

/-Then remove all  the finite points from
  Aₘ that come from Bⱼ = {xᵅⱼ + hₙ, n ≤  N₁} where j≤m, call it A-/
/-A contains a set Cₘ st. ∃ ℕ₂ C = {xᵅⱼ + hₙ, n ≥ ℕ₂}. Then C ⊆ Rᵅₘ  -/
/-Thus ∀ n ≥ N₂
F(xₘᵅ +hₙ) - F(xₘᵅ) / hₙ  = (F(xₘᵅ) + (xᵅₘ + hₙ - xₘᵅ)f(xₘᵅ) - F(xₘᵅ))/hₙ  = f(xᵅₘ)ₙ-/

/-Let Rᵅₘ = Eᵅₘ \ ⋃ⱼ Eᵅⱼ where j ∈ {1,2..m-1} if m ≥ 2  and Rᵅ₁ = Eᵅ₁.-/
def Ralpha (α : Quotient (SR h))(m : ℕ) : Set ℝ :=  match m with
  | 0 => Ealphai h α 0
  | i + 1 => Ealphai h α (i + 1) \( ⋃  j ∈ Finset.range (i+1), Ealphai h α j)

lemma RalphaUnionEalphai_aux (α : Quotient (SR h))(m : ℕ) :⋃ (j : ℕ), Ralpha h α j = ⋃ (i : ℕ ), Ealphai h α i  := by

  sorry

lemma Ralphanonemptyexistence (α : Quotient (SR h))(m : ℕ) : ∀ᶠ (n:ℕ) in atTop, EnumerateEalpha h α m + h n ∈ Ralpha h α m := by
  match m with
  | 0 => sorry
  | i + 1 => sorry




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
/-((g(x + hₘ) - g(x))/hₘ - Pₖ) ≥ 1/n holds on some set having lebesgue  measure > 1/n -/
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
