
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

import Mathlib

def T1 (g : ℕ → ℝ)(N : ℕ) : Set ℕ := {c |  ∃ x < N, x = c }

lemma T1_finite (g : ℕ → ℝ)(N : ℕ) : (T1 g N).Finite := by
  rw[T1]
  apply BddAbove.finite
  unfold BddAbove upperBounds Set.Nonempty
  use N
  simp only [exists_eq_right, Set.mem_setOf_eq]
  intros x hx
  linarith

lemma T1_image(g : ℕ → ℝ)(N : ℕ) :  g '' (T1 g N) = {c| ∃ x < N , g x = c }:= by
  ext y
  constructor
  intro hy
  simp only [Set.mem_image] at hy
  obtain ⟨x, hx, hgx⟩ := hy
  simp only [Set.mem_setOf_eq]
  rw[T1] at hx
  simp at hx
  use x
  intro hy
  simp only [Set.mem_setOf_eq] at hy
  obtain ⟨x,hx, hgx⟩ := hy
  rw[T1]
  simp only [exists_eq_right, Set.mem_image, Set.mem_setOf_eq]
  use x


lemma S_Finite (g : ℕ → ℝ)(N : ℕ) : {c| ∃ x < N , g x = c }.Finite := by
  rw[← T1_image]
  apply Set.Finite.image
  apply T1_finite
