/-
  ## Calculus 1
  Credits.
  * Formalising Mathematics 2022 - 2024, K. Buzzard
  * Mathematics in Lean, J. Avigad, P. Massot
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Set Filter

open Topology Filter Classical Real

noncomputable section

open Real Set

/-
  # Derivatives
-/

/-- The sin function has derivative 1 at 0. -/
example : HasDerivAt sin 1 0 := by
  simpa using hasDerivAt_sin 0

example (x : ℝ) : DifferentiableAt ℝ sin x := by
  exact differentiableAt_sin

example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) : deriv f x = a := by
  exact HasDerivAt.deriv h

example {a : ℝ} : deriv sin a = cos a := by
  rw [Real.deriv_sin]

example {f : ℝ → ℝ} {x : ℝ} (h : ¬DifferentiableAt ℝ f x) : deriv f x = 0 := by
  exact deriv_zero_of_not_differentiableAt h

#check deriv_add

example {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x := by
  rw [Pi.add_def, deriv_add hf hg]

example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 := by
  exact IsLocalMin.deriv_eq_zero h

example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  exact exists_deriv_eq_zero hab hfc hfI

example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  exact exists_deriv_eq_slope f hab hf hf'

example : deriv (fun x : ℝ ↦ x ^ 5 + 1) 6 = 5 * 6 ^ 4 := by
  simp only [differentiableAt_id', DifferentiableAt.pow, differentiableAt_const, deriv_add,
    deriv_pow'', Nat.cast_ofNat, Nat.add_one_sub_one, deriv_id'', mul_one, deriv_const', add_zero]

example : deriv sin π = -1 := by
  simp only [Real.deriv_sin, cos_pi]

#check DifferentiableAt.mul

#check DifferentiableAt.comp

-- Try proving it by hand.
-- `Function.comp_def` might be useful here
example : Differentiable ℝ fun x => cos (sin x) * exp x := by
  intro x
  refine DifferentiableAt.mul ?_ ?_
  · rw [← Function.comp_def]
    refine differentiableAt_cos.comp x differentiableAt_sin
  · exact differentiableAt_exp

-- `Function.comp_def` might be useful here
example (x : ℝ) :
    deriv (fun x => cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  rw [deriv_mul, ← Function.comp_def, deriv.comp, Real.deriv_cos, Real.deriv_sin, Real.deriv_exp]
  · ring
  · exact differentiableAt_cos
  · exact differentiableAt_sin
  · rw [← Function.comp_def]
    refine differentiableAt_cos.comp x differentiableAt_sin
  · exact differentiableAt_exp

end

/-
  # Limits computation
-/

-- Some classical limits
example : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat 1

example : Tendsto (fun n : ℕ ↦ 1 / n) atTop (𝓝 0) := by
  sorry

example : Tendsto (fun n : ℕ ↦ n) atTop atTop := by
  exact fun ⦃U⦄ a ↦ a

#check Tendsto.congr'

#check Filter.eventually_ne_atTop

example : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) / n) atTop (𝓝 1) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat 1
  have h2 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h3 := Tendsto.add h1 h2
  rw [zero_add] at h3
  refine Tendsto.congr' ?_ h3
  rw [Filter.EventuallyEq]
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [add_div, div_self]
  · ring
  · rwa [Nat.cast_ne_zero]

theorem lemma1 : Tendsto (fun n : ℕ ↦ n ^ 2) atTop atTop := by
  sorry

theorem lemma2 : Tendsto (fun n : ℕ ↦ n ^ 2 + n) atTop atTop := by
  sorry

-- Squeeze theorem
#check tendsto_of_tendsto_of_tendsto_of_le_of_le

#check tendsto_of_tendsto_of_tendsto_of_le_of_le'

example : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ 2 + 4 * Real.sqrt n) / (n ^ 2)) atTop (𝓝 1) := by
  sorry

example (f : ℝ → ℝ) (g : ℝ → ℝ) (a l : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l)) (h : f = g) :
    Tendsto g (𝓝 a) (𝓝 l) := by
  exact Tendsto.congr (congrFun h) hf

-- Congruence for limits
example (f : ℝ → ℝ) (g : ℝ → ℝ) (a l : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l)) (h : f =ᶠ[𝓝 a] g) :
    Tendsto g (𝓝 a) (𝓝 l) := by
  exact (tendsto_congr' h).mp hf

-- Unicity of limits
example (f : ℝ → ℝ) (a l l' : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l))  (hf' : Tendsto f (𝓝 a) (𝓝 l')) :
    l = l' := by
  exact tendsto_nhds_unique hf hf'

-- L'Hôpital's rule
example : Tendsto (fun x ↦ (exp x - 1) / (sin x)) (𝓝[≠] 0) (𝓝 1) := by
  refine deriv.lhopital_zero_nhds ?_ ?_ ?_ ?_ ?_
  all_goals sorry

/-
  # Normed vector space
-/

section

variable {E : Type*} [NormedAddCommGroup E]

example (x : E) : 0 ≤ ‖x‖ := norm_nonneg x -- `\norm`

example {x : E} : ‖x‖ = 0 ↔ x = 0 := norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y

example : MetricSpace E := by infer_instance

example {X : Type*} [TopologicalSpace X] {f : X → E} (hf : Continuous f) :
    Continuous fun x ↦ ‖f x‖ := by
  exact Continuous.norm hf

variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ := norm_smul a x

example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance

example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F := f

example (f : E →L[𝕜] F) : Continuous f := f.cont

example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y := f.map_add x y

example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x := f.map_smul a x

variable (f : E →L[𝕜] F)

example (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x

example {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.opNorm_le_bound hMp hM

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Metric

example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n`
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- each of these sets is closed
  have hc : ∀ n : ℕ, IsClosed (e n) := by
    sorry
  -- the union is the entire space; this is where we use `h`
  have hU : (⋃ n : ℕ, e n) = univ := by
    sorry
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
       `e m` contains some `x` -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ‖k‖ := sorry
  -- show all elements in the ball have norm bounded by `m` after applying any `g i`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m := by
    sorry
  have εk_pos : 0 < ε / ‖k‖ := sorry
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hk ?_⟩
  sorry
  sorry

end

/-
  # Asymptotics
-/

section Asymptotics

open Asymptotics

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F] (c : ℝ)
    (l : Filter α) (f : α → E) (g : α → F) : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =O[l] g ↔ ∃ C, IsBigOWith C l f g :=
  isBigO_iff_isBigOWith

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =o[l] g ↔ ∀ C > 0, IsBigOWith C l f g :=
  isLittleO_iff_forall_isBigOWith

example {α : Type*} {E : Type*} [NormedAddCommGroup E] (l : Filter α) (f g : α → E) :
    f ~[l] g ↔ (f - g) =o[l] g :=
  Iff.rfl

#check Filter.eventually_ne_atTop

#check Filter.eventually_gt_atTop

#check lt_sub_iff_add_lt'

#check lt_div_iff

lemma result1 (a : ℕ → ℝ) (h1 : ∀ n, 0 ≤ a n) (h2 : a ~[atTop] fun n ↦ n) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (1 - ε) * n < a n ∧ a n < (1 + ε) * n := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one] at h2
  · rw [Metric.tendsto_nhds] at h2
    simp_rw [dist_eq_norm, Real.norm_eq_abs] at h2
    specialize h2 ε hε
    filter_upwards [h2, eventually_gt_atTop 0] with n hn hn'
    rw [abs_lt] at hn
    constructor
    · replace hn := hn.1
      dsimp at hn
      rwa [lt_sub_iff_add_lt', ← sub_eq_add_neg, lt_div_iff] at hn
      rwa [Nat.cast_pos]
    · replace hn := hn.2
      sorry
  · filter_upwards [eventually_ne_atTop 0] with n hn
    rwa [Nat.cast_ne_zero]

end Asymptotics

/-
  # Unconditionally convergent series
-/

section Series

open Asymptotics

example (x : ℝ) :
    cos x = ∑' (n : ℕ), (-1 : ℝ) ^ n * x ^ (2 * n) /(2 * n).factorial := by
  exact cos_eq_tsum x

example : ∑' (n : ℕ), n = 0 := sorry

example {α β : Type*} [AddCommGroup β] [TopologicalSpace β] (f : α → β) (hf : ¬ Summable f) :
    ∑' x, f x = 0 := tsum_eq_zero_of_not_summable hf

example {α β : Type*} [AddCommGroup β] [TopologicalSpace β] [T2Space β] (f : α → β) (b : β)
    (hr : HasSum f b) :
    ∑' x, f x = b := by
  exact HasSum.tsum_eq hr

example {α β : Type*} [AddCommGroup β] [TopologicalSpace β] (f : α → β) (hf : Summable f) :
    HasSum f (∑' x, f x) := by
  exact Summable.hasSum hf

example {α β : Type*} [AddCommGroup β] [TopologicalSpace β] (f : α → β) (b : β) :
    HasSum f b ↔ Filter.Tendsto (fun (s : Finset α) => ∑ x ∈ s, f x) Filter.atTop (nhds b) := Iff.rfl

example (z : ℂ) :
    HasSum (fun n ↦ (-1 : ℂ) ^ n * z ^ (2 * n) /(2 * n).factorial) (Complex.cos z) :=
  Complex.hasSum_cos z

-- Assume the following results (it exists in your version of Mathlib but on another form)
theorem zeta_residue :
    Tendsto (fun (s : ℝ) => (s - 1) * ∑' (n : ℕ), (n : ℝ) ^ (- s)) (𝓝[>] 1) (𝓝 1) := sorry

variable (a : ℕ → ℝ) (h1 : ∀ n, 0 ≤ a n) (h2 : a ~[atTop] fun n ↦ n)

-- We want to prove that `Tendsto (fun (s : ℝ) => (s - 1) * ∑' (n : ℕ), a n ^ (- s)) (𝓝[>] 1) (𝓝 1)`

#check summable_of_isBigO_nat'

#check Real.rpow_le_rpow_iff_of_neg

include h1 h2 in
lemma result2 {s : ℝ} (hs : 1 < s) : Summable (fun n ↦ a n ^ (- s)) := by
  have h_sum : Summable (fun n : ℕ ↦ (n : ℝ) ^ (- s)) := by
    rw [summable_nat_rpow]
    apply neg_lt_neg
    exact hs
  refine summable_of_isBigO_nat' h_sum ?_
  have h_bdd := result1 a h1 h2 1 zero_lt_one
  rw [Asymptotics.isBigO_iff]
  use (1 + 1) ^ (- s)
  filter_upwards [h_bdd] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg, abs_of_nonneg, ← Real.mul_rpow]
  · sorry
  · sorry
  · replace hn := hn.2
    sorry

#check tendsto_finset_sum

#check Real.continuousAt_const_rpow'

#check Tendsto.congr'

lemma result3 (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n) (T : Finset ℕ) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑ n ∈ T, v n ^ (- s)) (𝓝[>] 1) (𝓝 0) := by
  have h_single : ∀ n, Tendsto (fun s : ℝ ↦ (s - 1) * v n ^ (- s)) (𝓝[>] 1) (𝓝 0) := by
    intro n
    have lim1 : Tendsto (fun s : ℝ ↦ (s - 1)) (𝓝 1) (𝓝 0) := by
      have h_sub_cont := continuous_sub_right (1 : ℝ)
      have := Continuous.tendsto h_sub_cont 1
      rwa [sub_self] at this
    have lim2 : Tendsto (fun s : ℝ ↦ v n ^ (- s)) (𝓝 1) (𝓝 ((v n) ⁻¹)) := by
      by_cases h : v n = 0
      · simp_rw [h, inv_zero]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ne_nhds one_ne_zero] with s hs
        rw [Real.zero_rpow]
        rwa [neg_ne_zero]
      · simp_rw [Real.rpow_neg (hv _)]
        refine Filter.Tendsto.inv₀ ?_ h
        have := Real.continuousAt_const_rpow' (a := v n) (b := 1) one_ne_zero
        have := this.tendsto
        rwa [Real.rpow_one] at this
    convert tendsto_nhdsWithin_of_tendsto_nhds (Tendsto.mul lim1 lim2)
    rw [zero_mul]
  convert tendsto_finset_sum T (fun n _ ↦ h_single n)
  · rw [Finset.mul_sum]
  · rw [Finset.sum_const_zero]

#check sum_add_tsum_compl

#check eventually_mem_nhdsWithin

lemma result4 (T : Finset ℕ) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), (n : ℝ) ^ (- s)) (𝓝[>] 1) (𝓝 1) := by
  have h_sum : (fun s ↦ (s - 1) * ∑' n : ℕ, (n : ℝ) ^ (- s) - (s - 1) * ∑ n ∈ T, (n : ℝ) ^ (- s))
      =ᶠ[𝓝[>] 1] (fun s : ℝ ↦ (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), (n : ℝ) ^ (- s)) := by
    filter_upwards with s
    rw [sub_eq_iff_eq_add', ← mul_add, sum_add_tsum_compl]
    sorry -- You might have to change some lines above too
  refine Tendsto.congr' h_sum ?_
  have lim1 := zeta_residue
  have lim2 := result3 (fun n ↦ n) (fun n ↦ Nat.cast_nonneg n) T
  convert Tendsto.sub lim1 lim2
  rw [sub_zero]

lemma result1' (a : ℕ → ℝ) (h1 : ∀ n, 0 ≤ a n) (h2 : a ~[atTop] fun n ↦ n) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1 - ε) * (n : ℝ)⁻¹ < (a n)⁻¹ ∧ (a n)⁻¹ < (1 + ε) * (n : ℝ)⁻¹ := by
  sorry

#check tsum_strict_mono

#check Pi.lt_def

#check Real.rpow_neg

#check Real.inv_rpow

#check Real.rpow_le_rpow

include h1 h2 in
lemma result5 {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) :
    ∃ T : Finset ℕ, ∀ s, 1 < s →
      (s - 1) * ∑ n ∈ T, a n ^ (- s) +
        (1 - ε) ^ s * (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), (n : ℝ) ^ (- s) <
          (s - 1) * ∑' n, a n ^ (- s) ∧
          (s - 1) * ∑' n, a n ^ (- s) <
        (s - 1) * ∑ n ∈ T, a n ^ (- s) +
      (1 + ε) ^ s * (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), (n : ℝ) ^ (- s) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (result1' a h1 h2 ε hε)
  set T := Finset.range N
  refine ⟨T, fun s hs ↦ ?_⟩
  constructor
  · sorry
  · calc
      _ = (s - 1) * ∑ n ∈ T, a n ^ (- s) + (s - 1) * ∑' (n : ↑(T : Set ℕ)ᶜ), a n ^ (- s) := ?_
      _ < (s - 1) * ∑ n ∈ T, a n ^ (- s) +
        (s - 1) * ∑' (n : ↑(T : Set ℕ)ᶜ), (1 + ε) ^ s * (n : ℝ) ^ (- s) := ?_
      _ = (s - 1) * ∑ n ∈ T, a n ^ (-s) +
          (1 + ε) ^ s * (s - 1) * ∑' (n : ↑(T : Set ℕ)ᶜ), (n : ℝ) ^ (- s) := ?_
    · rw [← mul_add, sum_add_tsum_compl]
      exact result2 a h1 h2 hs
    · gcongr
      · sorry
      · sorry
    · rw [tsum_mul_left]
      ring

include h1 h2 in
lemma result6 :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' n, a n ^ (- s)) (𝓝[>] 1) (𝓝 1) := by
  refine Metric.tendsto_nhdsWithin_nhds.mpr fun ε' hε' ↦ ?_
  let ε := min 1 ε'
  have hε_pos : 0 < ε := by aesop
  have hε3_pos : 0 < ε / 3 := by positivity
  have hε3_lt : ε / 3 < 1 := lt_of_lt_of_le (div_lt_self hε_pos (by norm_num)) (min_le_left 1 ε')
  obtain ⟨T, hT⟩ := result5 a h1 h2 hε3_pos hε3_lt
  sorry

end Series
