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

inductive tri
| one : tri
| two : tri
| three : tri

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
      sorry
    have hC_sub: IsCompact (univ : Set I) := by 
      sorry
    
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
  let π₁X := FundamentalGroup ↑univ ⟨x₀, trivial⟩;
  let π₁AuB := FundamentalGroup ↑(A ∪ B) ⟨x₀, (@subset_union_left X A B) hx₀.1⟩;
  let   φ : FreeGroup (π₁A ⊕ π₁B) →* π₁X :=
        FreeGroup.lift (Sum.elim
          (induced_map_pi1 (inclusion (subset_univ A)) (continuous_inclusion (subset_univ A)) ⟨x₀, hx₀.1⟩ ⟨x₀, trivial⟩ (inclusion_right (subset_univ A) ⟨x₀, trivial⟩ hx₀.1))
          (induced_map_pi1 (inclusion (subset_univ B)) (continuous_inclusion (subset_univ B)) ⟨x₀, hx₀.2⟩ ⟨x₀, trivial⟩ (inclusion_right (subset_univ B) ⟨x₀, trivial⟩ hx₀.2)));
  let j₁ : π₁A → FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inl;
  let j₂ : π₁B → FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inr;
  let i₁ : π₁AB → π₁A := induced_map_pi1 (inclusion (@inter_subset_left X A B)) (continuous_inclusion (@inter_subset_left X A B)) ⟨x₀, hx₀⟩ ⟨x₀, hx₀.1⟩ (inclusion_right (@inter_subset_left X A B) ⟨x₀, hx₀.1⟩ hx₀);
  let i₂ : π₁AB → π₁B := induced_map_pi1 (inclusion (@inter_subset_right X A B)) (continuous_inclusion (@inter_subset_right X A B)) ⟨x₀, hx₀⟩ ⟨x₀, hx₀.2⟩ (inclusion_right (@inter_subset_right X A B) ⟨x₀, hx₀.2⟩ hx₀);
  let f : π₁A → π₁X := induced_map_pi1 (inclusion (subset_univ A)) (continuous_inclusion (subset_univ A)) ⟨x₀, hx₀.1⟩ ⟨x₀, trivial⟩ (inclusion_right (subset_univ A) ⟨x₀, trivial⟩ hx₀.1);
  let g : π₁B → π₁X := induced_map_pi1 (inclusion (subset_univ B)) (continuous_inclusion (subset_univ B)) ⟨x₀, hx₀.2⟩ ⟨x₀, trivial⟩ (inclusion_right (subset_univ B) ⟨x₀, trivial⟩ hx₀.2);
  Function.Surjective φ ∧
  ∀ α : π₁AB, j₁ (i₁ α) * j₂ (i₂ α)⁻¹ ∈ φ.ker := by
  
  let π₁A := FundamentalGroup A ⟨x₀, hx₀.1⟩;
  let π₁B := FundamentalGroup B ⟨x₀, hx₀.2⟩;
  let π₁AB := FundamentalGroup ↑(A ∩ B) ⟨x₀, hx₀⟩;
  let π₁X := FundamentalGroup ↑univ ⟨x₀, trivial⟩;
  let π₁AuB := FundamentalGroup ↑(A ∪ B) ⟨x₀, (@subset_union_left X A B) hx₀.1⟩;
  let   φ : FreeGroup (π₁A ⊕ π₁B) →* π₁X :=
        FreeGroup.lift (Sum.elim
          (induced_map_pi1 (inclusion (subset_univ A)) (continuous_inclusion (subset_univ A)) ⟨x₀, hx₀.1⟩ ⟨x₀, trivial⟩ (inclusion_right (subset_univ A) ⟨x₀, trivial⟩ hx₀.1))
          (induced_map_pi1 (inclusion (subset_univ B)) (continuous_inclusion (subset_univ B)) ⟨x₀, hx₀.2⟩ ⟨x₀, trivial⟩ (inclusion_right (subset_univ B) ⟨x₀, trivial⟩ hx₀.2)));
  let j₁ : π₁A → FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inl;
  let j₂ : π₁B → FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inr;
  let i₁ : π₁AB → π₁A := induced_map_pi1 (inclusion (@inter_subset_left X A B)) (continuous_inclusion (@inter_subset_left X A B)) ⟨x₀, hx₀⟩ ⟨x₀, hx₀.1⟩ (inclusion_right (@inter_subset_left X A B) ⟨x₀, hx₀.1⟩ hx₀);
  let i₂ : π₁AB → π₁B := induced_map_pi1 (inclusion (@inter_subset_right X A B)) (continuous_inclusion (@inter_subset_right X A B)) ⟨x₀, hx₀⟩ ⟨x₀, hx₀.2⟩ (inclusion_right (@inter_subset_right X A B) ⟨x₀, hx₀.2⟩ hx₀);
  let f : π₁A → π₁X := induced_map_pi1 (inclusion (subset_univ A)) (continuous_inclusion (subset_univ A)) ⟨x₀, hx₀.1⟩ ⟨x₀, trivial⟩ (inclusion_right (subset_univ A) ⟨x₀, trivial⟩ hx₀.1);
  let g : π₁B → π₁X := induced_map_pi1 (inclusion (subset_univ B)) (continuous_inclusion (subset_univ B)) ⟨x₀, hx₀.2⟩ ⟨x₀, trivial⟩ (inclusion_right (subset_univ B) ⟨x₀, trivial⟩ hx₀.2);
  let I := unitInterval
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
    have α_path : Path x₀ x₀ := by 
      rw [@fg1] at α
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
        · sorry --it's a polynomial function, so it's continuous
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
    let D : tri → Set X := fun x ↦ 
      match x with 
      | .one => A
      | .two => B
      | .three => A ∩ B
    let beta_path (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 0 < i ∧ i < n) : ∃ (j : tri), JoinedIn ↑(D j) (ψ ⟨i, h⟩) x₀ := by 
      by_cases H : ψ ⟨i, h⟩ ∈ A ∩ B 
      · have := @PathConnectedSpace.joined ↑(A ∩ B) instTopologicalSpaceSubtype hAB_path_connected ⟨ψ ⟨i, h⟩, H⟩ ⟨x₀, hx₀⟩ 
        rw [← @joinedIn_iff_joined] at this 
        use .three
      · by_cases H1 : ψ ⟨i, h⟩ ∈ A 
        · have := @PathConnectedSpace.joined ↑A instTopologicalSpaceSubtype hA_path_connected ⟨ψ ⟨i, h⟩, H1⟩ ⟨x₀, hx₀.1⟩ 
          rw [← @joinedIn_iff_joined] at this 
          use .one
        · replace H1 : ψ ⟨i, h⟩ ∈ B := by
            sorry
          have := @PathConnectedSpace.joined ↑B instTopologicalSpaceSubtype hB_path_connected ⟨ψ ⟨i, h⟩, H1⟩ ⟨x₀, hx₀.2⟩ 
          rw [← @joinedIn_iff_joined] at this 
          use .two
    let beta₀ : Path (ψ ⟨0, fact2.1⟩) x₀ := by rw [in_end.1]
    let beta_n : Path (ψ ⟨n, fact2.2.1⟩) x₀ := by rw [in_end.2] 
    have r₀ : range ⇑beta₀ = {x₀} := by
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
    let gamma_path : ∀ (i : ℕ) (h : i ∈ Icc 0 n.1) (h1 : 0 < i), ∃ γ : Path x₀ x₀, ∃ (j : Bool), range γ.toFun ⊆ C j := by 
      intro i h h1
      by_cases H : i = 1 
      · by_cases H1 : n.1 = 1 
        · have : 2 ≤ n.1 + 1 := by rw [H1]
          let beta_n : Path (ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, this⟩⟩) x₀ := by
            have : Path (ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, this⟩⟩) x₀ = Path (ψ ⟨n, fact2.2.1⟩) x₀:= by 
              sorry 
            rw [this]
            exact beta_n
          have r₁ : range ⇑beta_n = {x₀} := by 
            sorry
          let γ := Path.trans (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) beta_n
          use γ 
          simp only [Nat.reduceAdd, ContinuousMap.toFun_eq_coe, coe_toContinuousMap, γ] 
          have alfa := important_fact 0 fact2.1 n.2 
          let z := alfa.choose
          let Z := alfa.choose_spec 
          use z 
          rw [Path.trans_range (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) beta_n] 
          rw [Path.trans_range (Path.symm beta₀) (int_path 0 fact2.1 n.2)] 
          rw [Path.symm_range] 
          simp only [Nat.reduceAdd, union_subset_iff] 
          constructor 
          · refine ⟨?_, Z⟩
            rw [r₀] 
            cases z with
            | false => refine singleton_subset_iff.mpr ?h.left.false.a; exact hx₀.1
            | true => refine singleton_subset_iff.mpr ?h.left.true.a; exact hx₀.2
          · rw [r₁] 
            cases z with
            | false => refine singleton_subset_iff.mpr ?h.left.false.a
            | true => refine singleton_subset_iff.mpr ?h.left.true.a
        · push_neg at H1
          replace H1 : 2 ≤ n.1 := by 
            have : 0 ≠ n.1 := Ne.symm (Nat.not_eq_zero_of_lt n.2)
            apply (Nat.two_le_iff n).mpr 
            refine ⟨id (Ne.symm this), H1⟩  
          have : 2 ≤ n.1 + 1 := Nat.le_add_right_of_le H1
          let ex := (beta_path 1 (fact2.2.2 2 ⟨zero_lt_two, this⟩) ⟨zero_lt_one, H1⟩) 
          let k := ex.choose 
          let K := ex.choose_spec 
          change JoinedIn (D k) (ψ ⟨1, fact2.right.right 2 ⟨zero_lt_two, this⟩⟩) x₀ at K
          have alfa := important_fact 0 fact2.1 n.2 
          let z := alfa.choose
          let Z := alfa.choose_spec
          by_cases H3 : k = tri.three
          · rw [H3] at K
            let β := K.choose
            let γ := Path.trans (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) β 
            use γ 
            use z 
            simp only [Nat.reduceAdd, ContinuousMap.toFun_eq_coe, coe_toContinuousMap, γ]
            rw [Path.trans_range (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) β, 
            Path.trans_range (Path.symm beta₀) (int_path 0 fact2.1 n.2), Path.symm_range] 
            simp only [Nat.reduceAdd, union_subset_iff]
            constructor 
            · refine ⟨?_, Z⟩
              rw [r₀] 
              cases z with
              | false => refine singleton_subset_iff.mpr ?h.left.false.a
              | true => refine singleton_subset_iff.mpr ?h.left.true.a
            · have J := K.choose_spec 
              replace J : range β ⊆ D tri.three := by exact range_subset_iff.mpr J
              by_cases H4 : z = false 
              · rw [H4] 
                have : D tri.three ⊆ C false := inter_subset_left 
                exact fun ⦃a⦄ a_1 ↦ this (J a_1)
              · rw [Bool.eq_true_eq_not_eq_false] at H4 
                rw [H4] 
                have : D tri.three ⊆ C true := inter_subset_right 
                exact fun ⦃a⦄ a_1 ↦ this (J a_1)
          · by_cases H'3 : k = tri.one 
            · rw [H'3] at K
              let β := K.choose
              let γ := Path.trans (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) β 
              use γ 
              use z 
              simp only [Nat.reduceAdd, ContinuousMap.toFun_eq_coe, coe_toContinuousMap, γ]
              rw [Path.trans_range (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) β, 
              Path.trans_range (Path.symm beta₀) (int_path 0 fact2.1 n.2), Path.symm_range] 
              simp only [Nat.reduceAdd, union_subset_iff]
              constructor 
              · refine ⟨?_, Z⟩
                rw [r₀] 
                cases z with
                | false => refine singleton_subset_iff.mpr ?h.left.false.a
                | true => refine singleton_subset_iff.mpr ?h.left.true.a
              · have J := K.choose_spec 
                replace J : range β ⊆ D tri.one := by exact range_subset_iff.mpr J
                by_cases H4 : z = false 
                · rw [H4]
                  exact J
                · rw [Bool.eq_true_eq_not_eq_false] at H4  
                  change range (int_path 0 fact2.1 n.2).toFun ⊆ C z at Z
                  rw [H4] at Z
                  rw [Set.range_subset_iff] at Z J
                  exfalso 
                  have t1: ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, this⟩⟩ ∈ (B \ A) := by 
                    simp 
                    constructor 
                    · have : (int_path 0 fact2.1 n.2) 1 ∈ B := by 
                        specialize Z 1 
                        exact Z 
                      rw [← (int_path 0 fact2.1 n.2).target] 
                      exact this
                    ·  --if it were into A, then k would have been tri.three, and not tri.one
                      sorry
                  have t2 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, this⟩⟩ ∈ (A \ B) := by 
                    simp 
                    constructor 
                    · have : β 0 ∈ A := by 
                        specialize J 0
                        exact J 
                      rw [← β.source] 
                      exact this
                    · --if it were into B, then k would have been tri.three, and not tri.one
                      sorry
                  apply t1.2 
                  exact t2.1
            · replace H'3 : k = tri.two := by
                sorry
              rw [H'3] at K
              let β := K.choose
              let γ := Path.trans (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) β 
              use γ 
              use z 
              simp only [Nat.reduceAdd, ContinuousMap.toFun_eq_coe, coe_toContinuousMap, γ]
              rw [Path.trans_range (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) β, 
              Path.trans_range (Path.symm beta₀) (int_path 0 fact2.1 n.2), Path.symm_range] 
              simp only [Nat.reduceAdd, union_subset_iff]
              constructor 
              · refine ⟨?_, Z⟩
                rw [r₀] 
                cases z with
                | false => refine singleton_subset_iff.mpr ?h.left.false.a
                | true => refine singleton_subset_iff.mpr ?h.left.true.a
              · have J := K.choose_spec 
                replace J : range β ⊆ D tri.two := by exact range_subset_iff.mpr J
                by_cases H4 : z = true
                · rw [H4]
                  exact J
                · rw [Bool.eq_false_eq_not_eq_true] at H4  
                  change range (int_path 0 fact2.1 n.2).toFun ⊆ C z at Z
                  rw [H4] at Z
                  rw [Set.range_subset_iff] at Z J
                  exfalso 
                  have t1: ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, this⟩⟩ ∈ (A \ B) := by 
                    simp 
                    constructor 
                    · have : (int_path 0 fact2.1 n.2) 1 ∈ A := by 
                        specialize Z 1 
                        exact Z 
                      rw [← (int_path 0 fact2.1 n.2).target] 
                      exact this
                    ·  --if it were into A, then k would have been tri.three, and not tri.one
                      sorry
                  have t2 : ψ ⟨1, fact2.2.2 2 ⟨zero_lt_two, this⟩⟩ ∈ (B \ A) := by 
                    simp 
                    constructor 
                    · have : β 0 ∈ B := by 
                        specialize J 0
                        exact J 
                      rw [← β.source] 
                      exact this
                    · --if it were into B, then k would have been tri.three, and not tri.one
                      sorry
                  apply t1.2 
                  exact t2.1
            --exact Path.trans (Path.trans (Path.symm beta₀) (int_path 0 fact2.1 n.2)) (beta_path 1 (fact2.2.2 2 ⟨zero_lt_two, this⟩) ⟨zero_lt_one, H1⟩)
      · replace H : 1 < i := lt_of_le_of_ne h1 fun a ↦ H (id (Eq.symm a)) 
        have h2 : i - 1 ∈ Icc 0 n.1 ∧ 0 < i - 1:= by 
          refine ⟨?_, Nat.zero_lt_sub_of_lt H⟩
          rw [mem_Icc] at h ⊢
          refine ⟨(Nat.le_sub_one_iff_lt h1).mpr h1, ?_⟩
          have t2 : i - 1 ≤ i := Nat.sub_le i 1  
          exact Nat.le_trans t2 h.2
        have fact5 : 0 < i + 1 ∧ i + 1 ≤ n + 1 := by
          refine ⟨Nat.add_pos_left h1 1, ?_⟩
          rw [mem_Icc] at h
          exact Nat.add_le_add_right h.2 1
        by_cases H1 : n = i
        · have : i - 1 < n := by
            rw [propext (Nat.sub_lt_iff_lt_add' h1)]
            have : i < i + 1 := lt_add_one i
            exact Nat.lt_of_lt_of_eq this (congrFun (congrArg HAdd.hAdd (id (Eq.symm H1))) 1)
          let beta_n : Path (ψ ⟨i - 1 + 1, fact3 (i - 1) h2.left this⟩) x₀ := by  
            have : Path (ψ ⟨i - 1 + 1, fact3 (i - 1) h2.left this⟩) x₀ = Path (ψ ⟨n, fact2.2.1⟩) x₀ := by 
              sorry 
            rw [this] 
            exact beta_n
          have r₁ : range ⇑beta_n = {x₀} := by 
            sorry
          let k := (beta_path (i - 1) h2.1 ⟨h2.2, this⟩).choose
          let K := (beta_path (i - 1) h2.1 ⟨h2.2, this⟩).choose_spec
          change JoinedIn (D k) (ψ ⟨i - 1, h2.1⟩) x₀ at K
          by_cases H3 : k = tri.three 
          · rw [H3] at K
            let β := K.choose
            let temp := K.choose_spec 
            change ∀ (t : ↑unitInterval), β t ∈ D tri.three at temp
            let γ := Path.trans (Path.trans (Path.symm β) (int_path (i - 1) h2.1 this)) beta_n 
            use γ 
            let alfa := important_fact (i - 1) h2.1 this 
            let z := alfa.choose
            let Z := alfa.choose_spec 
            change range (int_path (i - 1) h2.1 this).toFun ⊆ C z at Z 
            use z
            simp only [Nat.reduceAdd, ContinuousMap.toFun_eq_coe, coe_toContinuousMap, γ]
            rw [Path.trans_range (Path.trans (Path.symm β) (int_path (i - 1) h2.1 this)) beta_n, 
              Path.trans_range (Path.symm β) (int_path (i - 1) h2.1 this), Path.symm_range]
            simp only [Nat.reduceAdd, union_subset_iff] 
            constructor 
            · refine ⟨?_, Z⟩ 
              replace temp : range β ⊆ D tri.three := by exact range_subset_iff.mpr temp
              cases z with
              | false => have : D tri.three ⊆ C false := inter_subset_left; exact fun ⦃a⦄ a_1 ↦ this (temp a_1)
              | true => have : D tri.three ⊆ C true := inter_subset_right; exact fun ⦃a⦄ a_1 ↦ this (temp a_1)
            · rw [r₁] 
              cases z with
              | false => refine singleton_subset_iff.mpr ?h.left.false.a
              | true => refine singleton_subset_iff.mpr ?h.left.true.a
          · let alfa := important_fact (i - 1) h2.1 this 
            let z := alfa.choose
            let Z := alfa.choose_spec 
            change range (int_path (i - 1) h2.1 this).toFun ⊆ C z at Z 
            by_cases H4 : k = tri.one 
            · rw [H4] at K
              let β := K.choose
              let temp := K.choose_spec 
              change ∀ (t : ↑unitInterval), β t ∈ D tri.one at temp
              let γ := Path.trans (Path.trans (Path.symm β) (int_path (i - 1) h2.1 this)) beta_n 
              use γ
              use z
              simp only [Nat.reduceAdd, ContinuousMap.toFun_eq_coe, coe_toContinuousMap, γ]
              rw [Path.trans_range (Path.trans (Path.symm β) (int_path (i - 1) h2.1 this)) beta_n, 
              Path.trans_range (Path.symm β) (int_path (i - 1) h2.1 this), Path.symm_range]
              simp only [Nat.reduceAdd, union_subset_iff]  
              constructor 
              · refine ⟨?_, Z⟩ 
                replace temp : range β ⊆ D tri.one := by exact range_subset_iff.mpr temp 
                by_cases H'4 : z = false 
                · have : D tri.one = (C false) := rfl 
                  rw [H'4]
                  exact temp
                · rw [Bool.eq_true_eq_not_eq_false] at H'4 
                  exfalso --this is literally the same as the previous case
                  sorry
              · rw [r₁] 
                cases z with
              |   false => refine singleton_subset_iff.mpr ?h.left.false.a
              |   true => refine singleton_subset_iff.mpr ?h.left.true.a
            · replace H4 : k = tri.two := by
                sorry
              rw [H4] at K
              let β := K.choose
              let temp := K.choose_spec
              change ∀ (t : ↑unitInterval), β t ∈ D tri.two at temp
              let γ := Path.trans (Path.trans (Path.symm β) (int_path (i - 1) h2.1 this)) beta_n
              use γ 
              use z 
              simp only [Nat.reduceAdd, ContinuousMap.toFun_eq_coe, coe_toContinuousMap, γ]
              rw [Path.trans_range (Path.trans (Path.symm β) (int_path (i - 1) h2.1 this)) beta_n, 
              Path.trans_range (Path.symm β) (int_path (i - 1) h2.1 this), Path.symm_range] 
              simp only [Nat.reduceAdd, union_subset_iff]
              constructor 
              · refine ⟨?_, Z⟩
                replace temp : range β ⊆ D tri.two := by exact range_subset_iff.mpr temp 
                by_cases H'4 : z = true
                · have : D tri.two = (C true) := rfl 
                  rw [H'4]
                  exact temp
                · rw [Bool.eq_false_eq_not_eq_true] at H'4 
                  exfalso --this is literally the same as the previous case
                  sorry
              · rw [r₁] 
                cases z with
              |   false => refine singleton_subset_iff.mpr ?h.left.false.a
              |   true => refine singleton_subset_iff.mpr ?h.left.true.a

        · replace H1 : i < n.1 := by
            rw [mem_Icc] at h
            exact Nat.lt_of_le_of_ne h.2 fun a ↦ H1 (id (Eq.symm a))
          have : i - 1 < n := by 
            rw [propext (Nat.sub_lt_iff_lt_add' h1)]
            exact Nat.lt_add_right (Nat.succ 0) H1
          let Beta_i : ∃ (j : tri), JoinedIn (D j) (ψ ⟨i - 1 + 1, fact3 (i - 1) h2.1 this⟩) x₀ := by 
            have (j : tri) : JoinedIn (D j) (ψ ⟨i - 1 + 1, fact3 (i - 1) h2.left this⟩) x₀ = JoinedIn (D j) (ψ ⟨i, h⟩) x₀ := by
              sorry
            have t2 : ∃ j, JoinedIn (D j) (ψ ⟨i, h⟩) x₀ := (beta_path i h ⟨h1, H1⟩) 
            let t := t2.choose
            let T := t2.choose_spec
            change JoinedIn (D t) (ψ ⟨i, h⟩) x₀ at T
            rw [← this t] at T 
            use t
          let γ := Path.trans (Path.trans (Path.symm (beta_path (i - 1) h2.1 ⟨h2.2, this⟩).choose_spec.choose) (int_path (i - 1) h2.1 this)) Beta_i.choose_spec.choose
          use γ
          sorry 
          --this would play out the same as the previous cases, but we would have to split in 9 cases 
          --(for each case for where range (beta_path (i - 1) h2.1 ⟨h2.2, this⟩).choose_spec.choose is we need to differentiate
          -- where range Beta_i is. This would be slightly painful to show, and it's again the same exact reasoning.)
    let P : Fin n → (∃ (δ : Path x₀ x₀) (j : Bool), range δ.toFun ⊆ C j):= by 
      intro i 
      have : i.1 + 1 ∈ Icc 0 n.1 ∧ 0 < i.1 + 1 := by 
        constructor 
        · rw [mem_Icc] 
          have t1 := Fin.is_lt i 
          have t2 := Fin.zero_le' i 
          refine ⟨Nat.le_add_right_of_le t2, t1⟩
        · have t2 := Fin.zero_le' i 
          have : i.1 < i.1 + 1 := lt_add_one i.1 
          exact Nat.zero_lt_succ ↑i
      let δ := (gamma_path (i + 1) this.1 this.2).choose  
      let Δ := (gamma_path (i + 1) this.1 this.2).choose_spec 
      use δ
    let γ : Fin n → Path x₀ x₀ := by exact fun i ↦ (P i).choose
    let Γ := List.ofFn γ
    let concat_paths : Path x₀ x₀ := List.foldr Path.trans (Path.refl x₀) Γ
    have crucial_fact : α_path = concat_paths := by 
      refine Path.ext ?_
      simp [concat_paths, Γ, γ, P]
      sorry
    let concat : FundamentalGroup ↑univ ⟨x₀, trivial⟩ := by 
      have : FundamentalGroup ↑univ ⟨x₀, trivial⟩ = FundamentalGroup X x₀ := by 
        sorry
      rw [this, fg1]
      exact Quotient.mk (f1 x₀) concat_paths
    have follows : α = concat := by 
      simp [concat] 
      rw [← crucial_fact] 
      apply Eq.symm
      apply cast_eq_iff_heq.mpr
      sorry
    rw [follows] 
    simp [concat] 
    let Pi1 (δ : Path x₀ x₀) (j : Bool) (h : range δ.toFun ⊆ C j) (h1 : x₀ ∈ C j) : FundamentalGroup ↑(C j) ⟨x₀, h1⟩:= by 
      rw [fg1]
      --exact Quotient.mk (@f1 (C j) (instTopologicalSpaceSubtype) ⟨x₀, h1⟩) ?_
      sorry
    let free_mult : FreeGroup (FundamentalGroup ↑A ⟨x₀, hx₀.1⟩ ⊕ FundamentalGroup ↑B ⟨x₀, hx₀.2⟩) := by 
      sorry
    sorry
  · 
    sorry
