import Mathlib.Tactic.Common
import Mathlib
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.Multiplicity


--TENTATIVE DE PREUVE DE GAUSS-WANTZEl--

-- Le p^α gone régulier (p premier) est constructible à la règle et au compas (définition de Wantzel) si et
-- seulement si p=2 ou alpha=1 et p est de Fermat.


-- définiton d'un nombre premier de Fermat
def premierfermat (p : ℕ) :=
  (Nat.Prime p) ∧ (∃ n : ℕ, p=2^(2^n)+1)


--Lemme : si n est strictement positif, alors n=2^v2(n) * z implique z impair
theorem oddz (n z : Nat) : (n>0 ∧ n = 2^(padicValNat 2 n)*z) → (Odd z):= by
intro h
have h1:=h.right
have h2:= h.left
change (0<n) at h2
rw[Nat.pos_iff_ne_zero] at h2
by_contra h3
simp at h3
rw[Nat.even_iff] at h3
have h4 : 2 ∣ z := by
  by_contra H
  rw[Nat.two_dvd_ne_zero,h3] at H
  contradiction
change (∃ k, z= 2*k)at h4
have hh4 := h4.choose
have hh4H:= h4.choose_spec
rw[hh4H,<-Nat.mul_assoc,Nat.mul_comm,<-Nat.pow_add_one,Nat.eq_iff_prime_padicValNat_eq] at h1
· specialize h1 2
  rw[padicValNat.mul] at h1
  · simp at h1
    have h11:= h1 Nat.prime_two
    simp at h11
    rw[<-Nat.add_left_comm] at h11
    simp at h11
  · by_contra h21
    rw[h21] at hh4H
    simp at hh4H
    have h22:=h.right
    rw[hh4H] at h22
    simp at h22
    have h23:=h.left
    change (0 < n) at h23
    rw[Nat.pos_iff_ne_zero] at h23
    contradiction
  · by_contra h32
    rw[Nat.pow_add_one,Nat.mul_eq_zero] at h32
    cases h32 with
    | inl hh32 => rw[hh32] at h
                  simp at h
                  have hh33 := h.right
                  contradiction
    | inr hh32 => contradiction
· have h23:=h.left
  change (0 < n) at h23
  rw[Nat.pos_iff_ne_zero] at h23
  exact h23
· by_contra h31
  rw[h31] at h1
  have _:=h.left
  contradiction


--Lemme : Tout premier de la forme 2^m+1 est de Fermat et réciproquement.
theorem premierfermat_equ (p : ℕ) : (premierfermat p) ↔ ((Nat.Prime p) ∧ (∃ m : ℕ, m>0 ∧ p=2^m+1)) := by
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
    · obtain ⟨n, nn⟩ := right
      obtain ⟨z, hz⟩ := pow_padicValNat_dvd (p := 2) (n := n)
      let hyp1 := Odd.nat_add_dvd_pow_add_pow (2^(2^(padicValNat 2 n))) 1 (oddz n z ⟨nn.left, hz⟩)
      simp at hyp1
      rw[<-Nat.pow_mul, <-hz, <-nn.right,Nat.dvd_prime left] at hyp1
      simp at hyp1
      use padicValNat 2 n
      exact hyp1.symm

theorem zeroinfn : 1<↑n → 0<n := by
  intro h
  have h3 : 0<1 := by
    exact Nat.zero_lt_one
  exact Nat.lt_trans h3 h

def nombre_constructible (a : Complex) :=
  ∃ n : {n : ℕ // 1 < n},
   ∃ K : Fin n → Type, ∃ _ : (i : Fin n) → Semiring (K i),
  (i : Fin n) → IsField (K i) ∧
  ∃ f : (i : Fin n) → ((K i) →+* (K (i.add ⟨1, n.2⟩))), (i : Fin n) → Function.Injective (f i) ∧
   K ⟨0,zeroinfn n.2⟩ = ℚ
  --∧ a ∈ (K ⟨n,n.2⟩)


--Lemme : si p est premier de Fermat, Gal(Q(w)/Q) ≅ (Z/pZ)*
--CyclotomicField p ℚ "Corps cyclotomique"


--Lemme : si p est premier de Fermat, alors Φₚ(X) est irréductible sur ℚ.
theorem poly_cyclo_p_irre (p : ℕ) : premierfermat p → Irreducible (Polynomial.cyclotomic p ℚ) :=by
intro hp
have hpp : p>0 := by
  cases hp with
  | intro left right =>
    apply Nat.Prime.pos
    exact left
exact Polynomial.cyclotomic.irreducible_rat hpp

--Lemme : ℚ(w)/ℚ est galoisienne
theorem Qw_est_galois (p : ℕ+) : premierfermat p → IsGalois ℚ (CyclotomicField p ℚ) := by
  intro _
  have h1 := IsCyclotomicExtension.isGalois p ℚ (CyclotomicField p ℚ)
  exact h1



--theorem groupe_galois_Qw_ZpZ {p : ℕ} (hp : 0 < (p : Nat)) : premierfermat p → galCyclotomicEquivUnitsZMod (Polynomial.cyclotomic.irreducible_rat hp):= by

-- Lemme : si p est de Fermat, alors Gal(ℚ(w)/ℚ)≅(ℤ/pℤ)*
--theorem groupe_galois_Qw_ZpZ (p : ℕ+) (h : Irreducible (Polynomial.cyclotomic ↑p ℚ)) : premierfermat ↑p → galXPowEquivUnitsZMod h :=by

--theorem groupe_galois_Qw_ZpZ (p : ℕ+): premierfermat p → ∃ m, (Polynomial.Gal (Polynomial.cyclotomic p ℚ)) ≃* (ZMod (2^m)) := by
--sorry

theorem Z2mZ_resoluble (m : Nat) : IsSolvable (ZMod (2^m))ˣ := by
  have h : ∀ (a b : (ZMod (2^m))ˣ), ↑a * ↑b = ↑b * ↑a := by
    intro a b
    rw[Units.instCommGroupUnits.proof_1]
  exact isSolvable_of_comm h





--(Polynomial.Gal (Polynomial.cyclotomic p ℚ) ≅ (ZMod p)ˣ)
