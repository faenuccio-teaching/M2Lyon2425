import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Path
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Constructions

open TopologicalSpace FundamentalGroup Set FundamentalGroupoid Path

#check PathConnectedSpace
#check FundamentalGroup
#print Path
#print Path.trans
#print Quotient.map
#check Path.Homotopic
#print Relator.LiftFun
#print Path.Homotopic.map
#print Path.Homotopy
#print Path.Homotopic
#print map
#print Icc
#print HDiv

set_option maxHeartbeats 999999999999999999999999999

--variable {X : TopCat} {x₀ : ↑X} {p :  { as := x₀ } ⟶ { as := x₀ }}

/-lemma rea {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂: X} {p : Path x₀ x₁} {q : Path x₁ x₀} {p₁ : Path x₁ x₂} : 
(⟦Path.trans (Path.trans (Path.trans (Path.symm (Path.refl x₀)) p) q) (Path.trans (Path.symm q) p₁)⟧ : Path.Homotopic.Quotient x₀ x₂) = 
⟦Path.trans p p₁⟧ := by
  rw [@refl_symm]
  rw [eqpath (Path.Homotopy.transAssoc ((Path.refl x₀).trans p) q (q.symm.trans p₁))]
  replace this := Path.Homotopy.transAssoc -/

/-inductive tri
| one : tri
| two : tri
| three : tri-/

instance f1 {X : Type*} [TopologicalSpace X] (x₀ : X) : Setoid (Path x₀ x₀) where 
  r := fun p₁ p₂ ↦ Homotopic p₁ p₂ 
  iseqv := Path.Homotopic.equivalence

def funmap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (h : Continuous f)
(x₀ : X) (y₀ : Y) (hf₀ : f x₀ = y₀) : Path x₀ x₀ → Path y₀ y₀ := by 
  rw [← hf₀]
  intro p
  exact map p h

lemma fg1 {X : Type*} [TopologicalSpace X] (x₀ : X) : FundamentalGroup X x₀ = Quotient (f1 x₀) := by
  sorry

lemma homot_fun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
(f : X → Y) (h : Continuous f) (x₀ : X) (y₀ : Y) (hf₀ : f x₀ = y₀) : ∀ ⦃p₁ p₂ : Path x₀ x₀⦄,
p₁ ≈ p₂ → (funmap f h x₀ y₀ hf₀ p₁) ≈ (funmap f h x₀ y₀ hf₀ p₂) := by 
  intro _ _ H
  sorry

def Quotient.map₁.{u_1, u_2} : {α : Sort u_1} →
  {β : Sort u_2} →
    [sa : Setoid α] →
      [sb : Setoid β] → (f : α → β) → (h : ∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) → Quotient sa → Quotient sb :=
fun {α} {β} [Setoid α] [Setoid β] f h ↦ Quot.map f h

-- Induced map on fundamental group (loop homotopy classes)
def induced_map_pi1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] 
(f : X → Y) (h : Continuous f) (x₀ : X) (y₀ : Y) (hf₀ : f x₀ = y₀): FundamentalGroup X x₀ → FundamentalGroup Y y₀ := by
    rw [fg1 x₀, fg1 y₀]
    exact @Quotient.map₁ (Path x₀ x₀) (Path y₀ y₀) (f1 x₀) (f1 y₀) (funmap f h x₀ y₀ hf₀) (homot_fun f h x₀ y₀ hf₀)

lemma pi1_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
{x₀ : X} {y₀ : Y} {z₀ : Z} (hf₀ : f x₀ = y₀) (hg₀ : g y₀ = z₀) : (g ∘ f) x₀ = z₀ := by rw [← hf₀] at hg₀; exact hg₀

lemma induced_map_pi1_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
{f : X → Y} {g : Y → Z} {h1 : Continuous f} {h2 : Continuous g} {x₀ : X} {y₀ : Y} {z₀ : Z} (hf₀ : f x₀ = y₀) (hg₀ : g y₀ = z₀): 
induced_map_pi1 g h2 y₀ z₀ hg₀ ∘ induced_map_pi1 f h1 x₀ y₀ hf₀ = induced_map_pi1 (g ∘ f) (Continuous.comp h2 h1) x₀ z₀ (pi1_comp hf₀ hg₀) := by 
  ext s 
  simp
  sorry

def coe_subpath {X : Type*} [TopologicalSpace X] {A : Set X} {x₀ x₁ : X} (hx₀ : x₀ ∈ A) (hx₁ : x₁ ∈ A) 
(p : @Path ↑A instTopologicalSpaceSubtype ⟨x₀, hx₀⟩ ⟨x₁, hx₁⟩) : Path x₀ x₁ := by 
  let map : ↑unitInterval → X := fun a ↦ (p.toContinuousMap a) 
  have cont : Continuous map := 
  Continuous.subtype_val (ContinuousMap.continuous p.toContinuousMap)
  have source : map 0 = x₀ := by 
    simp only [map, coe_toContinuousMap, Path.source] 
  have target : map 1 = x₁ := by simp only [map, coe_toContinuousMap, Path.target]
  exact Path.mk ⟨map, cont⟩ source target

/-lemma eqpath {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} {p q : Path x₀ x₁}: p.Homotopy q → (⟦p⟧ : Path.Homotopic.Quotient x₀ x₁) = ⟦q⟧ := by 
  intro h 
  refine Quotient.sound ?_
  -/

theorem Path.Homotopic.comp_lift₁ {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X} {P₀ : Path x₀ x₁} {P₁ : Path x₁ x₂} :
⟦P₀.trans P₁⟧ = Path.Homotopic.Quotient.comp ⟦P₀⟧ ⟦P₁⟧ := Path.Homotopic.comp_lift P₀ P₁


lemma fact (n : ℕ+) : ∀ (i : Icc 0 n.1), ((i : ℝ) / n) ∈ unitInterval := by 
      intro i
      rw [@mem_Icc]
      refine ⟨?_, ?_⟩ 
      · rw [@div_nonneg_iff]
        left 
        refine ⟨Nat.cast_nonneg' ↑i, Nat.cast_nonneg' n⟩
      · rw [@div_le_one_iff]
        have H : 0 < n.1 := n.2 
        left 
        refine ⟨Nat.cast_pos'.mpr H, ?_⟩ 
        simp 
        have := i.2
        rw [mem_Icc] at this 
        exact this.2

lemma fact4 (n : ℕ+) (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : i < n) (t : ℝ) : t ∈ unitInterval → ((↑i + t) / ↑n) ∈ unitInterval := by 
  intro hh 
  rw [@mem_Icc] at h hh ⊢
  constructor 
  · rw [@div_nonneg_iff] 
    left 
    refine ⟨Left.add_nonneg (Nat.cast_nonneg' i) hh.1, Nat.cast_nonneg' n⟩
  · rw [@div_le_one_iff] 
    have H : 0 < n.1 := n.2
    left
    refine ⟨Nat.cast_pos'.mpr H, ?_⟩
    have : ↑i + t ≤ ↑i + 1 := by exact (add_le_add_iff_left ↑i).mpr hh.2 
    have this2 : (i : ℝ) + 1 ≤ ↑n := by 
      rw [← @Nat.cast_add_one]
      exact Nat.cast_le.mpr h1
    exact le_trans this this2

lemma path_open_covering {X ι : Type*} [TopologicalSpace X] 
  (A : ι → Set X) (hA : ∀ (j : ι), IsOpen (A j)) (hA_cover : X = ⋃ j, A j) (x₀ x₁ : X)
  (α : Path x₀ x₁) : ∃ (n : ℕ+), ∀ (i : Ico 0 n.1), ∃ (j : ι) (a : unitInterval) (b : unitInterval),
    a = ⟨(i : ℝ) / n, fact n ⟨i.1, Ico_subset_Icc_self i.2⟩⟩ ∧ 
    b = ⟨((i + 1) : ℝ) / n, fact4 n i.1 (Ico_subset_Icc_self i.2) i.2.2 1 unitInterval.one_mem⟩ ∧ α.toFun '' (Icc a b) ⊆ (A j) := by 
    
    /-let I := unitInterval
    let D : (ι × @univ I) → Set I := fun (i, x) ↦ ?_
    have hC : ∀ (j : ι), IsOpen (C j) := by 
      intro j
      change IsOpen (α ⁻¹' A j)
      specialize hA j 
      refine IsOpen.preimage ?hf hA
      exact Path.continuous α
    have hC_cover : univ ⊆ ⋃ j, C j := by 

    have hC_sub: IsCompact (univ : Set I) := by 

    
    apply IsCompact.elim_finite_subcover at hC_sub 
    specialize hC_sub C hC hC_cover -/

    
      
    
    sorry

theorem van_kampen
  {X ι : Type*} [inst : TopologicalSpace X] {A B : Set X} {x₀ : X}
  (hA : IsOpen A) (hB : IsOpen B)
  (hA_path_connected : PathConnectedSpace A)
  (hB_path_connected : PathConnectedSpace B)
  (hAB_path_connected : PathConnectedSpace ↑(A ∩ B))
  (h_union : A ∪ B = X)
  (hx₀ : x₀ ∈ A ∩ B) :
  let π₁A := FundamentalGroup A ⟨x₀, hx₀.1⟩;
  let π₁B := FundamentalGroup B ⟨x₀, hx₀.2⟩;
  let π₁AB := FundamentalGroup ↑(A ∩ B) ⟨x₀, hx₀⟩;
  let π₁X := FundamentalGroup X x₀;
  let π₁AuB := FundamentalGroup ↑(A ∪ B) ⟨x₀, (@subset_union_left X A B) hx₀.1⟩;
  let   φ : FreeGroup (π₁A ⊕ π₁B) →* π₁X :=
        FreeGroup.lift (Sum.elim
          (induced_map_pi1 Subtype.val continuous_subtype_val ⟨x₀, hx₀.1⟩ x₀ rfl)
          (induced_map_pi1 Subtype.val continuous_subtype_val ⟨x₀, hx₀.2⟩ x₀ rfl));
  let j₁ : π₁A → FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inl;
  let j₂ : π₁B → FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inr;
  let i₁ : π₁AB → π₁A := induced_map_pi1 (inclusion (@inter_subset_left X A B)) (continuous_inclusion (@inter_subset_left X A B)) ⟨x₀, hx₀⟩ ⟨x₀, hx₀.1⟩ (inclusion_right (@inter_subset_left X A B) ⟨x₀, hx₀.1⟩ hx₀);
  let i₂ : π₁AB → π₁B := induced_map_pi1 (inclusion (@inter_subset_right X A B)) (continuous_inclusion (@inter_subset_right X A B)) ⟨x₀, hx₀⟩ ⟨x₀, hx₀.2⟩ (inclusion_right (@inter_subset_right X A B) ⟨x₀, hx₀.2⟩ hx₀);
  let f : π₁A → π₁X := induced_map_pi1 Subtype.val continuous_subtype_val ⟨x₀, hx₀.1⟩ x₀ rfl;
  let g : π₁B → π₁X := induced_map_pi1 Subtype.val continuous_subtype_val ⟨x₀, hx₀.2⟩ x₀ rfl;
  Function.Surjective φ ∧
  ∀ α : π₁AB, j₁ (i₁ α) * (j₂ (i₂ α))⁻¹ ∈ φ.ker := by
  
  set π₁A := FundamentalGroup A ⟨x₀, hx₀.1⟩;
  set π₁B := FundamentalGroup B ⟨x₀, hx₀.2⟩;
  set π₁AB := FundamentalGroup ↑(A ∩ B) ⟨x₀, hx₀⟩;
  set π₁X := FundamentalGroup X x₀;
  set π₁AuB := FundamentalGroup ↑(A ∪ B) ⟨x₀, (@subset_union_left X A B) hx₀.1⟩;
  set   φ : FreeGroup (π₁A ⊕ π₁B) →* π₁X :=
        FreeGroup.lift (Sum.elim
          (induced_map_pi1 Subtype.val continuous_subtype_val ⟨x₀, hx₀.1⟩ x₀ rfl)
          (induced_map_pi1 Subtype.val continuous_subtype_val ⟨x₀, hx₀.2⟩ x₀ rfl));
  set j₁ : π₁A → FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inl;
  set j₂ : π₁B → FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inr;
  set i₁ : π₁AB → π₁A := induced_map_pi1 (inclusion (@inter_subset_left X A B)) (continuous_inclusion (@inter_subset_left X A B)) ⟨x₀, hx₀⟩ ⟨x₀, hx₀.1⟩ (inclusion_right (@inter_subset_left X A B) ⟨x₀, hx₀.1⟩ hx₀);
  set i₂ : π₁AB → π₁B := induced_map_pi1 (inclusion (@inter_subset_right X A B)) (continuous_inclusion (@inter_subset_right X A B)) ⟨x₀, hx₀⟩ ⟨x₀, hx₀.2⟩ (inclusion_right (@inter_subset_right X A B) ⟨x₀, hx₀.2⟩ hx₀);
  set f : π₁A → π₁X := induced_map_pi1 Subtype.val continuous_subtype_val ⟨x₀, hx₀.1⟩ x₀ rfl;
  set g : π₁B → π₁X := induced_map_pi1 Subtype.val continuous_subtype_val ⟨x₀, hx₀.2⟩ x₀ rfl;
  set I := unitInterval

  constructor 
  · intro α 
    let C : Bool → Set X := fun
      | .false => A
      | .true => B
    have hC : ∀ (j : Bool), IsOpen (C j) := by 
      intro j 
      cases j with
      | false => exact hA 
      | true => exact hB
    have hC_cover : X = ⋃ j, C j := by
      rw [@coe_eq_subtype] 
      simp 
      exact id (Eq.symm h_union)
    let α_quot := @FundamentalGroup.toPath (TopCat.of X) x₀ α
    let α_path : Path x₀ x₀ := by 
      exact Quotient.out α_quot
    have : ∃ (n : ℕ+), ∀ (i : Ico 0 n.1), ∃ (j : Bool) (a : unitInterval) (b : unitInterval),
    a = ⟨(i : ℝ) / n, fact n ⟨i.1, Ico_subset_Icc_self i.2⟩⟩ ∧ 
    b = ⟨((i + 1) : ℝ) / n, fact4 n i.1 (Ico_subset_Icc_self i.2) i.2.2 1 unitInterval.one_mem⟩ ∧ α_path.toFun '' (Icc a b) ⊆ (C j):= path_open_covering C hC hC_cover x₀ x₀ α_path
    let n := this.choose 
    let N := this.choose_spec 
    change ∀ (i : Ico 0 n.1), ∃ (j : Bool) (a : unitInterval) (b : unitInterval),
    a = ⟨(i : ℝ) / n, fact n ⟨i.1, Ico_subset_Icc_self i.2⟩⟩ ∧ 
    b = ⟨((i + 1) : ℝ) / n, fact4 n i.1 (Ico_subset_Icc_self i.2) i.2.2 1 unitInterval.one_mem⟩ ∧ α_path.toFun '' (Icc a b) ⊆ (C j) at N
    let ψ : Icc 0 n.1 → X := by 
      intro i 
      have factfact := fact n i
      exact α_path.toFun ⟨(i : ℝ) / n, factfact⟩
    have fact2 : 0 ∈ Icc 0 n.1 ∧ n.1 ∈ Icc 0 n.1 ∧ (∀ (i : ℕ), (0 < i ∧ i ≤ n + 1) → i - 1 ∈ Icc 0 n.1):= by 
      constructor 
      · rw [mem_Icc] 
        refine ⟨zero_le 0, zero_le n.1⟩
      · constructor 
        · rw [mem_Icc]
          refine ⟨zero_le n.1, le_refl n⟩
        · intro _ temp
          simp 
          exact temp.2
    have in_end : ψ ⟨0, fact2.1⟩ = x₀ ∧ ψ ⟨n, fact2.2.1⟩ = x₀ := by simp [ψ]
    have fact3 (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : i < n) : ((i + 1) ∈ Icc 0 n.1) := by 
      simp
      exact h1
    let int_path (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : i < n) : Path (ψ ⟨i, h⟩) (ψ ⟨i + 1, fact3 i h h1⟩) := by
      let funfun : I → X := fun t ↦ α_path.toContinuousMap ⟨(i + ↑t) / n, fact4 n i h h1 ↑t t.2⟩
      have Cont : Continuous funfun := by 
        simp [funfun] 
        refine continuous_iff_continuousAt.mpr ?_ 
        intro t 
        refine ContinuousAt.comp' ?hg ?hf
        · exact map_continuousAt α_path ⟨(↑i + ↑t) / ↑n, fact4 n i h h1 (↑t) t.property⟩
        · rw [@Metric.continuousAt_iff] 
          intro ε hε
          use (ε * (n : ℝ))
          refine ⟨?_, ?_⟩
          · refine mul_pos hε ?h.refine_1.a
            simp
          · intro x hx 
            simp [dist] at hx ⊢
            rw [div_sub_div_same] 
            simp 
            rw [abs_div, (Nat.abs_cast ↑n)]
            have : 0 < (n : ℝ) := by simp
            rw [div_lt_iff this] 
            exact hx
            --...yes a polynomial function is continuous
      have source : funfun 0 = ψ ⟨i, h⟩ := by simp [funfun, ψ] 
      have target : funfun 1 = ψ ⟨i + 1, fact3 i h h1⟩ := by simp [funfun, ψ]
      exact Path.mk ⟨funfun, Cont⟩ source target
    have fact5 (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : i < n) : range (int_path i h h1).toFun = α_path.toFun '' Icc ⟨ i / n, fact n ⟨i, h⟩⟩ ⟨(i + 1) / n, fact4 n i h h1 1 unitInterval.one_mem⟩ := by 
      simp
      ext s 
      refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
      · simp at H ⊢
        let x := H.choose 
        let X := H.choose_spec.choose_spec
        let h_1 := H.choose_spec.choose
        use (↑i + ↑x) / ↑↑n 
        constructor 
        · constructor 
          · rw [@add_div] 
            refine le_add_of_nonneg_right ?h.left.left.h
            refine div_nonneg_iff.mpr ?h.left.left.h.a 
            left 
            refine ⟨h_1.1, Nat.cast_nonneg' ↑n⟩
          · rw [@add_div, @add_div] 
            refine
              OrderedAddCommGroup.add_le_add_left (x / ↑↑n) (1 / ↑↑n) ?h.left.right.a (↑i / ↑↑n)
            refine div_le_div_of_nonneg_right h_1.2 (Nat.cast_nonneg' ↑n)
        · have : 0 ≤ (↑i + x) / ↑↑n ∧ (↑i + x) / ↑↑n ≤ 1 := fact4 n i h h1 x h_1
          use this
      · simp at H ⊢
        let x := H.choose 
        let X := H.choose_spec 
        let y := H.choose_spec.2.choose
        let Y := H.choose_spec.2.choose_spec
        use x * ↑↑n - ↑i
        have : 0 ≤ x * ↑↑n - ↑i ∧ x * ↑↑n - ↑i ≤ 1 := by 
          constructor 
          · rw [@sub_nonneg]
            apply (div_le_iff₀ (Nat.cast_pos'.mpr n.2)).mp
            exact X.1.1
          · rw [@sub_le_iff_le_add] 
            have := X.1.2
            apply (le_div_iff₀ (Nat.cast_pos'.mpr n.2)).mp 
            rw [AddCommMonoidWithOne.add_comm (1 : ℝ) ↑i] 
            exact this
        use this 
        simp 
        exact Y
    have excl (i : ℕ) (h : i ∈ Icc 0 n.1) : ψ ⟨i, h⟩ ∉ A ∩ B → ψ ⟨i, h⟩ ∉ A → ψ ⟨i, h⟩ ∈ B := by sorry
    let beta_path_AB (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 0 < i ∧ i < n) (h2 : ψ ⟨i, h⟩ ∈ A ∩ B) : 
    @Path ↑(A ∩ B) instTopologicalSpaceSubtype ⟨ψ ⟨i, h⟩, h2⟩ ⟨x₀, hx₀⟩ := 
    @PathConnectedSpace.somePath ↑(A ∩ B) instTopologicalSpaceSubtype hAB_path_connected ⟨ψ ⟨i, h⟩, h2⟩ ⟨x₀, hx₀⟩
    have beta_path_AB_range (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 0 < i ∧ i < n) (h2 : ψ ⟨i, h⟩ ∈ A ∩ B) : 
    ∀ (x : unitInterval), ((beta_path_AB i h h1 h2) x).1 ∈ (A ∩ B) := by 
      intro x 
      exact Subtype.coe_prop ((beta_path_AB i h h1 h2) x)
    let beta_path_A (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 0 < i ∧ i < n) (h2 : ψ ⟨i, h⟩ ∈ A) : 
    @Path ↑A instTopologicalSpaceSubtype ⟨ψ ⟨i, h⟩, h2⟩ ⟨x₀, hx₀.1⟩ := 
    @PathConnectedSpace.somePath ↑A instTopologicalSpaceSubtype hA_path_connected ⟨ψ ⟨i, h⟩, h2⟩ ⟨x₀, hx₀.1⟩
    have beta_path_A_range (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 0 < i ∧ i < n) (h2 : ψ ⟨i, h⟩ ∈ A) : 
    ∀ (x : unitInterval), ((beta_path_A i h h1 h2) x).1 ∈ A:= by 
      intro x 
      exact Subtype.coe_prop ((beta_path_A i h h1 h2) x)
    let beta_path_B (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 0 < i ∧ i < n) (h2 : ψ ⟨i, h⟩ ∈ B) : 
    @Path B instTopologicalSpaceSubtype ⟨ψ ⟨i, h⟩, h2⟩ ⟨x₀, hx₀.2⟩ := 
    @PathConnectedSpace.somePath ↑B instTopologicalSpaceSubtype hB_path_connected ⟨ψ ⟨i, h⟩, h2⟩ ⟨x₀, hx₀.2⟩
    have beta_path_B_range (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 0 < i ∧ i < n) (h2 : ψ ⟨i, h⟩ ∈ B) : 
    ∀ (x : unitInterval), ((beta_path_B i h h1 h2) x).1 ∈ B := by 
      intro x 
      exact Subtype.coe_prop ((beta_path_B i h h1 h2) x)
    let beta₀ : Path (ψ ⟨0, fact2.1⟩) x₀ := by rw [in_end.1]
    let beta_n : Path (ψ ⟨n, fact2.2.1⟩) x₀ := by rw [in_end.2] 
    have r₀ : range ⇑beta₀ = {x₀} := by
      sorry
    have r₁ : range ⇑beta_n = {x₀} := by
      sorry
    have important_fact (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : i < n) : ∃ (j : Bool), range (int_path i h h1).toFun ⊆ C j := by 
      have : i ∈ Ico 0 n.1 := by 
        rw [mem_Ico] 
        refine ⟨h.1, h1⟩
      let y := (N ⟨i, this⟩).choose 
      let a := (N ⟨i, this⟩).choose_spec.choose 
      let b := (N ⟨i, this⟩).choose_spec.choose_spec.choose
      let Y := (N ⟨i, this⟩).choose_spec.choose_spec.choose_spec 
      --simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, exists_and_left,
        --Subtype.exists, mem_Icc, exists_eq_left] at Y
      rw [fact5 i h h1]
      use y
      have t1 := Y.2.2 
      have t2 := Y.1
      replace t2 : a = ⟨↑i / ↑↑n, fact n ⟨i, h⟩⟩ := t2
      have t3 := Y.2.1 
      replace t3 : b = ⟨(↑i + 1) / ↑↑n, fact4 n i h h1 1 unitInterval.one_mem⟩ := t3
      replace t1 : α_path.toFun '' Icc ⟨↑i / ↑↑n, fact n ⟨i, h⟩⟩ ⟨(↑i + 1) / ↑↑n, fact4 n i h h1 1 unitInterval.one_mem⟩ ⊆ C y := by 
        rw [← t2, ← t3]
        exact t1
      exact t1
    have trivialfact : 2 ≤ n.1 + 1 := Nat.le_add_of_sub_le n.2
    have end_n₁ (h : n.1 = 1) : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ = x₀ := by 
      sorry
    let beta_n₁ {h : n.1 = 1} : Path (ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩) x₀ := by rw [end_n₁ h] --this is beta_n if n = 1
    have rbn₁ {h : n.1 = 1} : range ⇑(@beta_n₁ h) = {x₀} := by
      sorry
    let gamma_path₁₁ {h : n.1 = 1} : Path x₀ x₀ := Path.trans (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) (@beta_n₁ h)
    --we define this path if n = 1, explicitly to cover that one case 
    let gamma₁₁ {h : n.1 = 1} : Path.Homotopic.Quotient x₀ x₀ := Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm beta₀⟧ ⟦int_path 0 fact2.1 n.2⟧) ⟦@beta_n₁ h⟧
    have gamma₁₁_fact {h : n.1 = 1} : ⟦@gamma_path₁₁ h⟧ = @gamma₁₁ h := by 
      simp [gamma_path₁₁, gamma₁₁]
      rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
      --Path.Homotopic.comp_lift (Path.Homotopic.comp_lift )
    let gamma_path₁ (h : 1 < n) : Path x₀ x₀ := by 
      by_cases h1 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ A ∩ B
      · exact Path.trans (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) (coe_subpath h1 hx₀ (beta_path_AB (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h1))
      · by_cases h2 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ A
        · exact Path.trans (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) (coe_subpath h2 hx₀.1 (beta_path_A (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h2))
        · replace h2 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ B := excl 1 (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) h1 h2 
          exact Path.trans (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) (coe_subpath h2 hx₀.2 (beta_path_B (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h2))
    let gamma₁ (h : 1 < n) : Path.Homotopic.Quotient x₀ x₀ := by 
      by_cases h1 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ A ∩ B
      · exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm beta₀⟧ ⟦int_path 0 fact2.1 n.2⟧) ⟦coe_subpath h1 hx₀ (beta_path_AB (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h1)⟧
      · by_cases h2 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ A
        · exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm beta₀⟧ ⟦int_path 0 fact2.1 n.2⟧) ⟦coe_subpath h2 hx₀.1 (beta_path_A (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h2)⟧
        · replace h2 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ B := excl 1 (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) h1 h2 
          exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm beta₀⟧ ⟦int_path 0 fact2.1 n.2⟧) ⟦coe_subpath h2 hx₀.2 (beta_path_B (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h2)⟧
    have gamma₁_fact (h : 1 < n) : ⟦gamma_path₁ h⟧ = gamma₁ h := by 
      simp [gamma_path₁, gamma₁]
      by_cases h1 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ A ∩ B
      · simp only [h1, ↓reduceDIte]
        rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
      · by_cases h2 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ A
        · simp only [h1, h2, ↓reduceDIte]
          rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
        · simp only [h1, h2, ↓reduceDIte]
          rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
    have gamma_path₁₁_range (h : n.1 = 1): ∃ (j : Bool), range (@gamma_path₁₁ h) ⊆ C j := by 
      simp only [gamma_path₁₁]
      rw [Path.trans_range (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) (@beta_n₁ h)] 
      rw [Path.trans_range (Path.symm beta₀) (int_path 0 fact2.1 n.2)] 
      rw [Path.symm_range] 
      have := important_fact 0 fact2.1 n.2 
      let t := this.choose 
      let T := this.choose_spec 
      use t
      simp only [union_subset_iff]
      refine ⟨⟨?_, T⟩, ?_⟩ 
      · rw [r₀, @singleton_subset_iff] 
        cases t with
        | false => exact hx₀.1
        | true => exact hx₀.2
      · rw [(@rbn₁ h), @singleton_subset_iff] 
        cases t with
        | false => exact hx₀.1
        | true => exact hx₀.2
    have gamma_path₁_range (h : 1 < n) : ∃ (j : Bool), range (gamma_path₁ h) ⊆ C j := by 
      have := important_fact 0 fact2.1 n.2 
      let t := this.choose 
      let T := this.choose_spec 
      use t
      by_cases h1 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ A ∩ B
      · simp only [gamma_path₁]
        simp only [h1, ↓reduceDIte]
        rw [Path.trans_range (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) (coe_subpath h1 hx₀ (beta_path_AB (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h1))] 
        rw [Path.trans_range (Path.symm beta₀) (int_path 0 fact2.1 n.2)] 
        rw [Path.symm_range]
        simp only [union_subset_iff]
        refine ⟨⟨?_, T⟩, ?_⟩
        · rw [r₀, @singleton_subset_iff] 
          cases t with
        | false => exact hx₀.1
        | true => exact hx₀.2
        · simp only [coe_subpath, coe_toContinuousMap, coe_mk_mk]
          rw [Set.range_subset_iff] 
          intro x
          have : ↑((beta_path_AB (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h1) x) ∈ (A ∩ B) := 
            by exact ((beta_path_AB (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h1) x).2
          have trivial : A ∩ B ⊆ C t := by 
            cases t with
            | false => exact inter_subset_left
            | true => exact inter_subset_right
          exact trivial this
      · by_cases h2 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ A
        · simp only [gamma_path₁, h1, h2, ↓reduceDIte] 
          rw [Path.trans_range (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) (coe_subpath h2 hx₀.1 (beta_path_A (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h2))] 
          rw [Path.trans_range (Path.symm beta₀) (int_path 0 fact2.1 n.2)] 
          rw [Path.symm_range]
          simp only [union_subset_iff]
          refine ⟨⟨?_, T⟩, ?_⟩
          · rw [r₀, @singleton_subset_iff] 
            cases t with
            | false => exact hx₀.1
            | true => exact hx₀.2
          · by_cases H : t = false
            · rw [H]
              simp only [coe_subpath, coe_toContinuousMap, coe_mk_mk]
              rw [Set.range_subset_iff] 
              intro x
              exact ((beta_path_A (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h2) x).2
            · rw [Bool.eq_true_eq_not_eq_false] at H
              exfalso 
              change range (int_path 0 fact2.1 n.2).toFun ⊆ C t at T 
              rw [H, Set.range_subset_iff] at T 
              specialize T 1
              have t1 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ B := by 
                have : (int_path 0 fact2.1 n.2).toFun 1 = ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ := (int_path 0 fact2.1 n.2).target'
                rw [← this]
                exact T 
              rw [propext (not_iff_false_intro ⟨h2, t1⟩)] at h1 
              exact h1
        · simp only [gamma_path₁, h1, h2, ↓reduceDIte]
          have h'2 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ B := excl 1 (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) h1 h2  
          rw [Path.trans_range (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) (coe_subpath h'2 hx₀.2 (beta_path_B (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h'2))] 
          rw [Path.trans_range (Path.symm beta₀) (int_path 0 fact2.1 n.2)] 
          rw [Path.symm_range]
          simp only [union_subset_iff]
          refine ⟨⟨?_, T⟩, ?_⟩
          · rw [r₀, @singleton_subset_iff] 
            cases t with
            | false => exact hx₀.1
            | true => exact hx₀.2
          · by_cases H : t = true
            · rw [H]
              simp only [coe_subpath, coe_toContinuousMap, coe_mk_mk]
              rw [Set.range_subset_iff] 
              intro x
              exact ((beta_path_B (0 + 1) (fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩) ⟨zero_lt_one, h⟩ h'2) x).2
            · rw [Bool.eq_false_eq_not_eq_true] at H
              exfalso 
              change range (int_path 0 fact2.1 n.2).toFun ⊆ C t at T 
              rw [H, Set.range_subset_iff] at T 
              specialize T 1
              have t1 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ ∈ A := by 
                have : (int_path 0 fact2.1 n.2).toFun 1 = ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, trivialfact⟩⟩ := (int_path 0 fact2.1 n.2).target'
                rw [← this]
                exact T 
              exact h2 t1
    have end_n₂ : ψ ⟨n - 1 + 1, fact3 (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt n.2)⟩ = x₀ := by 
      sorry
    let beta_n₂ : Path (ψ ⟨n - 1 + 1, fact3 (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt n.2)⟩) x₀ := by rw [end_n₂]
    have rbn₂ : range ⇑beta_n₂ = {x₀} := by sorry
    let gamma_path_n (h : 1 < n) : Path x₀ x₀ := by
      by_cases h1 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ A ∩ B 
      · exact Path.trans (Path.trans (Path.symm (coe_subpath h1 hx₀ (beta_path_AB (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h1))) 
        (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h))) (beta_n₂)
      · by_cases h2 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ A
        · exact Path.trans (Path.trans (Path.symm (coe_subpath h2 hx₀.1 (beta_path_A (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h2))) 
        (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h))) (beta_n₂)
        · replace h2 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ B := excl (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) h1 h2
          exact Path.trans (Path.trans (Path.symm (coe_subpath h2 hx₀.2 (beta_path_B (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h2))) 
        (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h))) (beta_n₂)
    let gamma_n (h : 1 < n) : Path.Homotopic.Quotient x₀ x₀ := by 
      by_cases h1 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ A ∩ B 
      · exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath h1 hx₀ (beta_path_AB (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h1))⟧ 
        ⟦int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)⟧) ⟦beta_n₂⟧
      · by_cases h2 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ A
        · exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath h2 hx₀.1 (beta_path_A (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h2))⟧
        ⟦int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)⟧) ⟦beta_n₂⟧
        · replace h2 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ B := excl (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) h1 h2
          exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath h2 hx₀.2 (beta_path_B (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h2))⟧ 
        ⟦int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)⟧) ⟦beta_n₂⟧
    have gamma_n_fact (h : 1 < n) : ⟦gamma_path_n h⟧ = gamma_n h := by 
      simp [gamma_path_n, gamma_n]
      by_cases h1 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ A ∩ B
      · simp only [h1, ↓reduceDIte]
        rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
      · by_cases h2 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ A
        · simp only [h1, h2, ↓reduceDIte]
          rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
        · simp only [h1, h2, ↓reduceDIte]
          rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
    have gamma_path_n_range (h : 1 < n) : ∃ (j : Bool), range (gamma_path_n h) ⊆ C j := by 
      have := important_fact (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)
      let t := this.choose 
      let T := this.choose_spec 
      use t
      by_cases h1 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ A ∩ B
      · simp only [gamma_path_n]
        simp only [h1, ↓reduceDIte]
        rw [Path.trans_range (Path.trans (Path.symm (coe_subpath h1 hx₀ (beta_path_AB (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h1))) 
        (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h))) (beta_n₂)] 
        rw [Path.trans_range (Path.symm (coe_subpath h1 hx₀ (beta_path_AB (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h1))) 
        (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h))] 
        simp only [union_subset_iff]
        refine ⟨⟨?_, T⟩, ?_⟩
        · simp only [coe_subpath, coe_toContinuousMap, coe_mk_mk]
          rw [Set.range_subset_iff] 
          intro x
          have : ↑((beta_path_AB (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h1).symm x) ∈ (A ∩ B) := by
            exact ((beta_path_AB (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h1).symm x).2
          have trivial : A ∩ B ⊆ C t := by 
            cases t with
            | false => exact inter_subset_left
            | true => exact inter_subset_right
          exact trivial this
        · rw [rbn₂, @singleton_subset_iff] 
          cases t with
          | false => exact hx₀.1
          | true => exact hx₀.2
      · by_cases h2 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ A
        · simp only [gamma_path_n, h1, h2, ↓reduceDIte] 
          rw [Path.trans_range (Path.trans (Path.symm (coe_subpath h2 hx₀.1 (beta_path_A (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h2))) 
          (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h))) (beta_n₂)] 
          rw [Path.trans_range (Path.symm (coe_subpath h2 hx₀.1 (beta_path_A (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h2))) 
          (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h))] 
          simp only [union_subset_iff]
          refine ⟨⟨?_, T⟩, ?_⟩
          · by_cases H : t = false
            · rw [H]
              simp only [coe_subpath, coe_toContinuousMap, coe_mk_mk]
              rw [Set.range_subset_iff] 
              intro x
              exact ((beta_path_A (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h2).symm x).2
            · rw [Bool.eq_true_eq_not_eq_false] at H
              exfalso 
              change range (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)).toFun ⊆ C t at T 
              rw [H, Set.range_subset_iff] at T 
              specialize T 0
              have t1 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ B := by 
                have : (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)).toFun 0 = ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ := 
                (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)).source'
                rw [← this]
                exact T 
              rw [propext (not_iff_false_intro ⟨h2, t1⟩)] at h1 
              exact h1
          · rw [rbn₂, @singleton_subset_iff] 
            cases t with
            | false => exact hx₀.1
            | true => exact hx₀.2
        · simp only [gamma_path_n, h1, h2, ↓reduceDIte]
          have h'2 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ B := excl (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) h1 h2  
          rw [Path.trans_range (Path.trans (Path.symm (coe_subpath h'2 hx₀.2 (beta_path_B (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h'2))) 
          (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h))) (beta_n₂)] 
          rw [Path.trans_range (Path.symm (coe_subpath h'2 hx₀.2 (beta_path_B (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h'2))) 
          (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h))]
          simp only [union_subset_iff]
          refine ⟨⟨?_, T⟩, ?_⟩
          · by_cases H : t = true
            · rw [H]
              simp only [coe_subpath, coe_toContinuousMap, coe_mk_mk]
              rw [Set.range_subset_iff] 
              intro x
              exact ((beta_path_B (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) ⟨Nat.zero_lt_sub_of_lt h, Nat.sub_one_lt_of_lt h⟩ h'2).symm x).2
            · rw [Bool.eq_false_eq_not_eq_true] at H
              exfalso 
              change range (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)).toFun ⊆ C t at T 
              rw [H, Set.range_subset_iff] at T 
              specialize T 0
              have t1 : ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ ∈ A := by 
                have : (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)).toFun 0 = 
                ψ ⟨n - 1, (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩)⟩ := 
                (int_path (n - 1) (fact2.2.2 n ⟨n.2, Nat.le_add_right (↑n) 1⟩) (Nat.sub_one_lt_of_lt h)).source'
                rw [← this]
                exact T 
              exact h2 t1
          · rw [rbn₂, @singleton_subset_iff] 
            cases t with
            | false => exact hx₀.1
            | true => exact hx₀.2
    have comeon (i : ℕ) (h : 0 < i) : i = i - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h).mp rfl
    have (i : ℕ) (h : 0 < i) (h1 : i < n.1) : i - 1 + 1 < n.1 := by 
      exact (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i h)) ↑n)).mp h1
    let gamma_path (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 1 < i ∧ i < n.1) (hn : 1 < n) : Path x₀ x₀ := by 
      by_cases H1 : ψ ⟨i - 1, (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩)⟩ ∈ A ∩ B
      · by_cases H'1 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A ∩ B 
        · 
          exact Path.trans (Path.trans (Path.symm (coe_subpath H1 hx₀ (beta_path_AB (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
          ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H1))) (int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2))) (coe_subpath H'1 hx₀ 
          (beta_path_AB (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
          (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'1))
        · by_cases H'2 :  ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A
          · 
            exact Path.trans (Path.trans (Path.symm (coe_subpath H1 hx₀ (beta_path_AB (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
            ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H1))) (int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2))) (coe_subpath H'2 hx₀.1 
            (beta_path_A (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
            (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2))
          · replace H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ B := excl (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) H'1 H'2
            
            exact Path.trans (Path.trans (Path.symm (coe_subpath H1 hx₀ (beta_path_AB (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
            ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H1))) (int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2))) (coe_subpath H'2 hx₀.2 
            (beta_path_B (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
            (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2))
      · by_cases H2 : ψ ⟨i - 1, (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩)⟩ ∈ A
        · by_cases H'1 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A ∩ B 
          · 
            exact Path.trans (Path.trans (Path.symm (coe_subpath H2 hx₀.1 (beta_path_A (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
            ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))) (int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2))) (coe_subpath H'1 hx₀ 
            (beta_path_AB (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
            (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'1))
          · by_cases H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A
            · 
              exact Path.trans (Path.trans (Path.symm (coe_subpath H2 hx₀.1 (beta_path_A (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
              ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))) (int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2))) (coe_subpath H'2 hx₀.1 
              (beta_path_A (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
              (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2))
            · replace H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ B := excl (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) H'1 H'2
              
              exact Path.trans (Path.trans (Path.symm (coe_subpath H2 hx₀.1 (beta_path_A (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
              ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))) (int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2))) (coe_subpath H'2 hx₀.2 
              (beta_path_B (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
              (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2))
        · replace H2 : ψ ⟨i - 1, (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩)⟩ ∈ B := excl (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) H1 H2 
          by_cases H'1 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A ∩ B 
          · 
            exact Path.trans (Path.trans (Path.symm (coe_subpath H2 hx₀.2 (beta_path_B (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
            ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))) (int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2))) (coe_subpath H'1 hx₀ 
            (beta_path_AB (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
            (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'1))
          · by_cases H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A
            · 
              exact Path.trans (Path.trans (Path.symm (coe_subpath H2 hx₀.2 (beta_path_B (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
              ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))) (int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2))) (coe_subpath H'2 hx₀.1 
              (beta_path_A (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
              (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2))
            · replace H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ B := excl (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) H'1 H'2
              
              exact Path.trans (Path.trans (Path.symm (coe_subpath H2 hx₀.2 (beta_path_B (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
              ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))) (int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2))) (coe_subpath H'2 hx₀.2 
              (beta_path_B (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
              (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2))
    
    let gamma (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 1 < i ∧ i < n.1) (hn : 1 < n) : Path.Homotopic.Quotient x₀ x₀ := by 
      by_cases H1 : ψ ⟨i - 1, (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩)⟩ ∈ A ∩ B
      · by_cases H'1 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A ∩ B 
        · 
          exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath H1 hx₀ (beta_path_AB (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
          ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H1))⟧ ⟦int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟧) ⟦coe_subpath H'1 hx₀ (beta_path_AB
          (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
          (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'1)⟧
        · by_cases H'2 :  ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A
          · 
            exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath H1 hx₀ (beta_path_AB (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
            ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H1))⟧ ⟦int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟧) ⟦coe_subpath H'2 hx₀.1 (beta_path_A
            (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
            (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2)⟧
          · replace H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ B := excl (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) H'1 H'2
            
            exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath H1 hx₀ (beta_path_AB (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
            ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H1))⟧ ⟦int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟧) ⟦coe_subpath H'2 hx₀.2 (beta_path_B
            (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
            (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2)⟧
      · by_cases H2 : ψ ⟨i - 1, (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩)⟩ ∈ A
        · by_cases H'1 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A ∩ B 
          · 
            exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath H2 hx₀.1 (beta_path_A (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
            ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))⟧ ⟦int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟧) ⟦coe_subpath H'1 hx₀ (beta_path_AB
            (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
            (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'1)⟧
          · by_cases H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A
            · 
              exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath H2 hx₀.1 (beta_path_A (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
              ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))⟧ ⟦int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟧) ⟦coe_subpath H'2 hx₀.1 (beta_path_A
              (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
              (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2)⟧
            · replace H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ B := excl (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) H'1 H'2
              
              exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath H2 hx₀.1 (beta_path_A (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
              ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))⟧ ⟦int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟧) ⟦coe_subpath H'2 hx₀.2 (beta_path_B
              (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
              (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2)⟧
        · replace H2 : ψ ⟨i - 1, (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩)⟩ ∈ B := excl (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) H1 H2 
          by_cases H'1 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A ∩ B 
          · 
            exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath H2 hx₀.2 (beta_path_B (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
            ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))⟧ ⟦int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟧) ⟦coe_subpath H'1 hx₀ (beta_path_AB
            (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
            (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'1)⟧
          · by_cases H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A
            · 
              exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath H2 hx₀.2 (beta_path_B (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
              ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))⟧ ⟦int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟧) ⟦coe_subpath H'2 hx₀.1 (beta_path_A
              (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
              (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2)⟧
            · replace H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ B := excl (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) H'1 H'2
              
              exact Homotopic.Quotient.comp (Homotopic.Quotient.comp ⟦Path.symm (coe_subpath H2 hx₀.2 (beta_path_B (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) 
              ⟨Nat.zero_lt_sub_of_lt h1.1, tsub_lt_of_lt h1.2⟩ H2))⟧ ⟦int_path (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟧) ⟦coe_subpath H'2 hx₀.2 (beta_path_B
              (i - 1 + 1) (fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)) ⟨(Nat.zero_lt_succ (i - 1)), 
              (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (comeon i (Nat.zero_lt_of_lt h1.1))) ↑n)).mp h1.2⟩ H'2)⟧
    
    have gamma_fact (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 1 < i ∧ i < n.1) (hn : 1 < n) : ⟦gamma_path i h h1 hn⟧ = gamma i h h1 hn := by 
      simp only [gamma_path, gamma]
      by_cases H1 : ψ ⟨i - 1, (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩)⟩ ∈ A ∩ B
      · by_cases H'1 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A ∩ B 
        · simp only [H1, H'1, ↓reduceDIte]
          rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
        · by_cases H'2 :  ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A
          · simp only [H1, H'1, H'2, ↓reduceDIte]
            rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
          · simp only [H1, H'1, H'2, ↓reduceDIte]
            rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
      · by_cases H2 : ψ ⟨i - 1, (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩)⟩ ∈ A
        · by_cases H'1 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A ∩ B 
          · simp only [H1, H2, H'1, ↓reduceDIte]
            rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
          · by_cases H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A
            · simp only [H1, H2, H'1, H'2, ↓reduceDIte]
              rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
            · simp only [H1, H2, H'1, H'2, ↓reduceDIte]
              rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
        · by_cases H'1 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A ∩ B 
          · simp only [H1, H2, H'1, ↓reduceDIte]
            rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
          · by_cases H'2 : ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩ ∈ A
            · simp only [H1, H2, H'1, H'2, ↓reduceDIte]
              rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
            · simp only [H1, H2, H'1, H'2, ↓reduceDIte]
              rw [Path.Homotopic.comp_lift₁, Path.Homotopic.comp_lift₁]
    
    have gamma_path_range (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 1 < i ∧ i < n.1) (hn : 1 < n) : ∃ (j : Bool), range (gamma_path i h h1 hn) ⊆ C j := by 
      sorry --it's the same strategy as before, literally the same strategy, but we have to divide cases for both 
      --ψ ⟨i - 1, (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩)⟩ and
      --ψ ⟨i - 1 + 1, fact3 (i - 1) (fact2.2.2 i ⟨(Nat.zero_lt_of_lt h1.1), le_trans' (Nat.le_add_right (↑n) 1) (le_of_lt h1.2)⟩) (tsub_lt_of_lt h1.2)⟩
      --so 9 more cases total
    by_cases M : n.1 = 1
    · have crucial_fact : α_path = @gamma_path₁₁ M := by 
        simp only [Nat.reduceAdd, eq_mpr_eq_cast, Nat.zero_eq, gamma_path₁₁, beta₀, beta_n₁]
        simp [int_path]
        apply Path.ext
        --rw [@Homotopy.trans_assoc_reparam]
        sorry
      sorry
    · replace M : 1 < n := by exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨(Nat.ne_zero_iff_zero_lt.mpr n.2), M⟩
      have temptrivial (i : Fin n) (h : i.1 ≠ 0) (h1 : i.1 ≠ n - 1) : i.1 + 1 ∈ Icc 0 n.1 ∧ (1 < i.1 + 1 ∧ i.1 + 1 < n) := by 
        constructor 
        · rw [mem_Icc] 
          have t1 := Fin.is_lt i 
          have t2 := Fin.zero_le' i 
          refine ⟨Nat.le_add_right_of_le t2, t1⟩
        · constructor 
          · have : 0 < i.1 := Nat.zero_lt_of_ne_zero h
            exact Nat.lt_add_of_pos_left this
          · rw [← @Nat.lt_sub_iff_add_lt]
            exact Nat.lt_of_le_of_ne (@Nat.le_sub_one_of_lt i n i.2) h1
      let P : Fin n → Path.Homotopic.Quotient x₀ x₀:= by 
        intro i 
        by_cases H : i.1 = 0
        · exact gamma₁ M
        · by_cases H' : i.1 = n - 1 
          · exact gamma_n M
          · exact gamma (i.1 + 1) (temptrivial i H H').1 (temptrivial i H H').2 M
      let Γ := List.ofFn P
      let concat_paths : Path.Homotopic.Quotient x₀ x₀ := List.foldr Path.Homotopic.Quotient.comp ⟦Path.refl x₀⟧ Γ
      let concat : FundamentalGroup X x₀ := @FundamentalGroup.fromPath (TopCat.of X) x₀ concat_paths
      have crucial_fact : α = concat := by 
        simp only [concat, concat_paths, Γ, P, gamma₁, gamma_n, gamma]
        /-rw [← crucial_fact]
        simp [α_path, α_quot]-/
        sorry
      rw [crucial_fact] 
      simp [concat, concat_paths, Γ, P] 
      /-have gen (j : Bool) : x₀ ∈ C j := by 
        
      have gamma₁_range : ∃ (j : Bool), @FundamentalGroup.fromPath (TopCat.of X) x₀ (gamma₁ M) ∈ FundamentalGroup ↑(C j) ⟨x₀, gen j⟩ := by
        -/
      /-let Pi1 (δ : Path x₀ x₀) (j : Bool) (h : range δ.toFun ⊆ C j) (h1 : x₀ ∈ C j) : FundamentalGroup ↑(C j) ⟨x₀, h1⟩:= by 
        rw [fg1]
        let ε : @Path (C j) instTopologicalSpaceSubtype ⟨x₀, h1⟩ ⟨x₀, h1⟩ := by 
          refine Path.mk ?_ ?_ ?_ 
          · have : C j ⊆ univ := by 
              exact fun ⦃a⦄ a ↦ trivial 
            let t1 : I → univ := fun i ↦ ⟨δ.toFun i, trivial⟩
            replace h : range t1 ⊆ range (inclusion this) := by 
              have : range δ.toFun = range t1 := by 
                simp [t1]
                
              
            let this: I → C j := by 
              exact ((@Set.range_subset_range_iff_exists_comp I (C j) univ t1 (inclusion this)).mp h).choose
            have cont : Continuous this := by 
              simp [this, t1] 
              
            
          · 
          · 
        --exact Quotient.mk (@f1 (C j) (instTopologicalSpaceSubtype) ⟨x₀, h1⟩) ?_
        -/
      let free_mult : FreeGroup (FundamentalGroup ↑A ⟨x₀, hx₀.1⟩ ⊕ FundamentalGroup ↑B ⟨x₀, hx₀.2⟩) := by 
        sorry
      use free_mult 
      simp [free_mult]

      sorry
  · intro α 
    change j₁ (i₁ α) * (j₂ (i₂ α))⁻¹ ∈ φ.ker
    have eqty : f ∘ i₁ = g ∘ i₂ := by 
      simp [f, i₁, g, i₂] 
      rw [induced_map_pi1_comp, induced_map_pi1_comp]
      exact rfl
    have univ₁ : f = φ ∘ j₁ := by 
      ext x
      simp [φ, j₁]
    have univ₂ : g = φ ∘ j₂ := by
      ext x
      simp [φ, j₂]
    have follows : φ (j₁ (i₁ α)) = φ (j₂ (i₂ α)) := by 
      change (φ ∘ j₁) (i₁ α) = (φ ∘ j₂) (i₂ α)
      rw [← univ₁, ← univ₂]
      change (f ∘ i₁) α = (g ∘ i₂) α
      rw [eqty]
    rw [MonoidHom.mem_ker, MonoidHom.map_mul_inv]
    exact mul_inv_eq_one.mpr follows
