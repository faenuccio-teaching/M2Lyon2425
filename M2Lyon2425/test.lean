import Mathlib

def premierFermat (p : Nat.Primes) := 
  ∃ n : Nat, (p : Int) = (2^n) +1

lemma neg_un_pow_paire_eq_un {n : Nat} : n ≠ 0 →  1 = (-1)^2^n := by
  cases n with
  | zero =>
    intro absu 
    exfalso
    omega
  | succ m => 
    have hm : 2 ^ (m+1) = 2 * (2^m) := by omega
    rw [hm]
    simp

lemma fermat_hardImp {p : Nat.Primes} (hFPp : premierFermat p)
  : ∃ m : Nat, (p : Int) = 2^2^m + 1 := by

  change ∃ n, (p : Int) = 2^n +1 at hFPp
  by_cases decompn : ∃ m, (p : Int) = 2 ^ 2 ^ m + 1
  · exact decompn
  · simp at decompn
    
    sorry

example p : premierFermat p ↔ (p : Int) = 2 ∨ ∃ m, (p : Int) = 2^2^m + 1 := by
  constructor
  · intro hFP
    change ∃ k, (p : Int) = (2^k)+1 at hFP
--    exact fermat_hardImp hFP
    by_cases hp2 : (p : Int) = 2
    · left 
      exact hp2
    · right
      exact fermat_hardImp hFP
  · intro hE 
    cases hE with
    | inl h => 
      use 0
      omega
    | inr h => 
      let  k := h.choose
      use 2 ^ k
      exact h.choose_spec

