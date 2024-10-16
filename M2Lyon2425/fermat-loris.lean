import Mathlib.Tactic.Common
import Mathlib
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.Multiplicity


def premierfermat (p : Nat) :=
  (Nat.Prime p) ∧ (∃ n : ℕ, p=2^(2^n)+1)


theorem div_power_2 (p n : Nat) : (2^p+1 ∣ 2^n+1) ↔ (p ∣ n) := by
constructor
· intro h1
  change (∃ k, 2^n+1=(2^p+1)*k) at h1
  let k := h1.choose
  let hk := Exists.choose_spec h1
  change(∃u, n=p*u)
  sorry
· intro h1
  change (∃ k, n=p*k) at h1
  let k:=h1.choose
  let hk:= Exists.choose_spec h1
  let S : Set ℕ := {i | i<k}
  let factor := Int.natAbs (∑ i∈S, (2^p)^i*(-1)^(k-i-1))
  change (∃ u, 2^n+1 = (2^p+1)*u)
  use factor
  sorry

theorem premierfermat_equ (p : Nat) : (premierfermat p) ↔ ((Nat.Prime p) ∧ (∃ m : ℕ, m>0 ∧ p=2^m+1)) := by
constructor
· intro hf
  cases hf with
  | intro left right =>
    constructor
    · exact left
    · let n := right.choose
      let hn := Exists.choose_spec right
      let m := 2^n
      use m
      constructor
      · change 2^n>0
        simp
      · exact hn
· intro h1
  cases h1 with
  | intro left right =>
    constructor
    · exact left
    · obtain ⟨m, nm⟩ := right
      let ⟨nml, nmr⟩ := nm
      let l : Nat := padicValNat 2 m
      let ⟨z, pz⟩ := pow_padicValNat_dvd (p := 2) (n := m)
      let facteur : ℕ := 2^(2^l)+1
      have hyp := (div_power_2 (2^(padicValNat 2 m)) m).mpr
      --rw [←nnr] at hyp2

      sorry
