import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common

open Set Classical

open scoped Set

def Intervals : ℕ → Set ℤ := by
  exact fun (n : ℕ) ↦ (fun m ↦ (-n : ℤ) ≤ m ∧ m ≤ n) --this defines the interval [-n,n]

example : ⋂ n : ℕ, Intervals n = {0} := by
  ext s
  constructor
  · intro h
    rw [mem_iInter] at h
    specialize h 0
    replace h := h.out
    exact Eq.symm ((fun {x y} ↦ Int.eq_iff_le_and_ge.mpr) h)
  · intro h
    rw [mem_iInter]
    intro i
    rw [h,mem_def]
    have H := Int.ofNat_nonneg i
    have : -1 ≤ 0 := by
      trivial
    have H1 : (-i : ℤ) ≤ 0 := by
      have e := Int.mul_nonpos_of_nonneg_of_nonpos H this
      rw [Int.mul_neg_one] at e
      exact e
    constructor
    · exact H1
    · exact H


example : ⋃ n , Intervals n = univ := by
  ext s
  constructor
  · intro _
    trivial
  · intro _
    rw [mem_iUnion]
    let S := Int.natAbs s
    use S
    constructor
    · have := Int.natAbs_eq s
      cases this with
      | inl h =>
        rw [h]
        exact Lean.Omega.Int.neg_le_natAbs
      | inr h => rw [h]
    · exact Int.le_natAbs
