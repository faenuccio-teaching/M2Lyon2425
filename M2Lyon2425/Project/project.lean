import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Path
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open TopologicalSpace FundamentalGroup Set FundamentalGroupoid Path


lemma homot_fun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
(f : X → Y) (h : Continuous f) (x₀ : X) (p₁ p₂ : Path x₀ x₀) : 
Homotopic p₁ p₂ → Homotopic (map p₁ h) (map p₂ h) := by 
  intro H
  exact Homotopic.map H ⟨f, h⟩

-- Induced map on fundamental group (loop homotopy classes)
def induced_map_pi1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] 
(f : X → Y) (h : Continuous f) (x₀ : X) (y₀ : Y) (hf₀ : f x₀ = y₀): FundamentalGroup X x₀ → FundamentalGroup Y y₀ :=
    Quotient.map (fun p ↦ map p h) (fun p₁ p₂ H ↦ homot_fun f h x₀ p₁ p₂ H)
    sorry

theorem van_kampen
  {X : Type*} [TopologicalSpace X] {A B : Set X} {x₀ : X}
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
  let   φ : FreeGroup (π₁A ⊕ π₁B) →* π₁X :=
        FreeGroup.lift (Sum.elim
          (induced_map_pi1 (inclusion (subset_union_left A B)))
          (induced_map_pi1 (inclusion (subset_union_right A B))));
  let j₁ : π₁A →* FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inl;
  let j₂ : π₁B →* FreeGroup (π₁A ⊕ π₁B) := FreeGroup.of ∘ Sum.inr;
  let i₁ : π₁AB →* π₁A := induced_map_pi1 (Set.inclusion (inter_subset_left A B));
  let i₂ : π₁AB →* π₁B := induced_map_pi1 (Set.inclusion (inter_subset_right A B));
  Function.Surjective φ ∧
  ∀ α : π₁AB, j₁ (i₁ α) * j₂ (i₂ α)⁻¹ ∈ φ.ker := by

  sorry


  lemma path_open_covering {X ι : Type*} [TopologicalSpace X] 
  (A : ι → Set X) (hA : ∀ (j : ι), IsOpen (A j)) (hA_cover : X = ⋃ j, A j) (x₀ x₁ : X)
  (α : Path x₀ x₁) : ∃ (n : ℕ), ∀ (i : Ico 0 n), ∃ (j : ι) (a : unitInterval) (b : unitInterval),
    a = (i : ℝ) / n ∧ b = ((i + 1) : ℝ) / n ∧ α.toFun '' (Icc a b) ⊆ (A j) := by 
    let I := unitInterval
    let C : ι → Set I := fun i ↦ α ⁻¹' (A i)
    have hC : ∀ (j : ι), IsOpen (C j) := by 
      intro j
      change IsOpen (α ⁻¹' A j)
      specialize hA j 
      refine IsOpen.preimage ?hf hA
      exact Path.continuous α
    have hC_cover : I ⊆ ⋃ j, C j := by 
      sorry
    have hC_sub: IsCompact I := by 
      sorry
    rw [isCompact_iff_finite_subcover] at hC_sub 
    specialize hC_sub C hC hC_cover 
