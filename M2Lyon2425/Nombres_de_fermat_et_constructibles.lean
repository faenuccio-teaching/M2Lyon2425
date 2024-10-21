import Mathlib.Tactic.Common
import Mathlib
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.Multiplicity


--TENTATIVE DE PREUVE DE GAUSS-WANTZEl--

-- Le p^α gone régulier (p premier) est constructible à la règle et au compas (définition de Wantzel) si et
-- seulement si p=2 ou alpha=1 et p est de Fermat.

--On désignera par w le nombre Complex.exp (2*↑Real.pi*Complex.I/p)

-- Définiton d'un nombre premier de Fermat
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

theorem zeroinfn (k : ℕ+) (n : Fin k) (hn : 1 < ↑n) : ↑0 <n := by
  have h3 : 0<1 := by
    exact  Fin.zero_lt_one
  exact Nat.lt_trans

--Définition : un nombre a est constructible s'il existe une tour quadratique de ℚ vers ℚ(a).
def nombre_constructible (a : Complex) :=
  ∃ n : {n : ℕ+ // 1 < n}, ∃ K : Fin n → Type, ∃ _ : (i : Fin n) → Semiring (K i),
  (i : Fin n) → IsField (K i) ∧
  ∃ f : (i : Fin n) → ((K i) →+* (K (i.add ⟨1, n.2⟩))), (i : Fin n) → Function.Injective (f i)
   ∧ K ⟨0, Fin.size_pos'⟩ = ℚ
   ∧ a ∈ (K ⟨n-1, ⟩)


def Wantzel1 (a : Complex) : nombre_constructible a → ∃n, finite_dimensional ℚ (Algebra.adjoin ℚ {a}) = 2^n := by
sorry

--Lemme : si p est premier de Fermat, Gal(Q(w)/Q) ≅ (Z/pZ)*

--Lemme : si p est premier de Fermat, alors Φₚ(X) est irréductible sur ℚ.
theorem poly_cyclo_p_irre (p : ℕ) : premierfermat p → Irreducible (Polynomial.cyclotomic (↑p) ℚ) :=by
intro hp
have hpp : p>0 := by
  cases hp with
  | intro left right =>
    apply Nat.Prime.pos
    exact left
exact Polynomial.cyclotomic.irreducible_rat hpp

--Lemme : L'extension ℚ(w) est galoisienne
theorem Qw_est_galois (p : ℕ+) : premierfermat p → IsGalois ℚ (CyclotomicField p ℚ) := by
  intro _
  have h1 := IsCyclotomicExtension.isGalois p ℚ (CyclotomicField p ℚ)
  exact h1

--Lemme : ℤ/(2^m)ℤ est un groupe résoluble
theorem Z2mZ_resoluble (m : Nat) : IsSolvable (ZMod (2^(2^m)))ˣ := by
  have h : ∀ (a b : (ZMod (2^(2^m)))ˣ), a * b = b * a := by
    intro a b
    rw[Units.instCommGroupUnits.proof_1]
  exact isSolvable_of_comm h

--Lemme : w est une racine primitive p-ième de l'unité.
theorem racine_prim_unite (p : ℕ+) : IsPrimitiveRoot (Complex.exp (2*↑Real.pi*Complex.I/p)) p :=by
  rw[IsPrimitiveRoot.iff_def]
  constructor
  · rw[<-Complex.exp_nat_mul,IsField.mul_comm]
    simp
    apply Field.toIsField
  · intro l
    intro h1
    rw[<-Complex.exp_nat_mul,Complex.exp_eq_one_iff,CommRing.toNonUnitalCommRing.proof_11,
    <-Complex.commRing.proof_6,<-mul_div_assoc,<-div_mul_eq_mul_div₀,] at h1
    let n:=h1.choose
    have hn := h1.choose_spec
    simp at hn
    cases hn with
    | inl h =>
      change (∃k, l= ↑p *k)
      sorry
    | inr h =>
      have hpi := Real.pi_ne_zero
      exfalso
      contradiction

--Lemme : w est algébrique sur ℚ
theorem algebrique_sur_Q (p : ℕ+) : premierfermat p →  IsAlgebraic ℚ (Complex.exp (2*↑Real.pi*Complex.I/p)) := by
  intro h1
  cases h1 with
  | intro left right =>
    constructor
    · have h2 := Complex.isPrimitiveRoot_exp p (Nat.Prime.ne_zero left)
      constructor
      · exact Polynomial.cyclotomic_ne_zero p ℚ
      · have h3 := Polynomial.cyclotomic_eq_minpoly_rat h2 (PNat.pos p)
        rw[h3]
        have h4 := minpoly.aeval ℚ (Complex.exp (2 * ↑Real.pi * Complex.I / ↑↑p))
        exact h4

--Lemme Gal(ℚ(w)/ℚ) iso ℤ/2^mℤ

/- PLAN DE LA PREUVE
I) premier de fermat implique constructible
OK  1) w est une racine de l'unité
    2) ℚ(w)/ℚ est l'extension cyclotomique p ℚ et est galoisienne
    3) deg(extension cyclotomique p ℚ) = p-1 =2^m
    4) Gal (ℚ(w)/ℚ) ≅ (ℤ/pℤ)ˣ≅ ℤ/(p-1)ℤ
    5) De 4, on a Gal(ℚ(w)/Q) isomorphe à un groupe cyclique donc est cyclique.
      En particulier, ∃ ζ un générateur d'ordre maximal (ie p-1=2^m) et Gal(ℚ(w)/ℚ)
      est résoluble.
    6) La suite G_i = ⟨ ζ^(2^i) ⟩ est une suite résoluble vérifiant [G_i,G_(i+1)]=2,
      G_0= Gal(ℚ(w)/ℚ) et G_m=⟨1⟩
    7) Par correspondance de Galois, K_i:= ℚ(w)^(G_i) est une tour de corps vérifiant
      K_0=ℚ, K_m=ℚ(w) et [K_(i+1):K_i]=2.

II) Constructible implique premier de fermat
1) w constructible implique tour quadratique
2) multiplicativite des degres implique deg (ℚ(w)/ℚ)=2^m pour un certains m
3) Or, deg(ℚ(w)/ℚ)=deg μ(w,ℚ)=deg Φ(p^α)=(p-1)p^(α-1)
4) donc 2^m=(p-1)p^(α-1)
5) D'où p=2 ou α=1 et p=2^m+1 qui implique permier de fermat
-/






--(Polynomial.Gal (Polynomial.cyclotomic p ℚ) ≅ (ZMod p)ˣ)
theorem Gauss_Wantzel_1 (p : ℕ+) (α : Nat) : nombre_constructible (Complex.exp (2*Complex.I*↑Real.pi/↑(p^α))) ↔ premierfermat p ∧ α =1 :=by
constructor
· sorry
· intro h
  cases h with
  | intro left1 right1 =>
    rw[right1,pow_one]
    have QwGalois := Qw_est_galois p left1
    have Phi_p_irre := poly_cyclo_p_irre p left1
    --rw [galCyclotomicEquivUnitsZMod] at Phi_p_irre
    let Gp_galois := (Polynomial.cyclotomic (↑p) ℚ).Gal
    have h3:= galCyclotomicEquivUnitsZMod Phi_p_irre


theorem Gauss_Wantzel (n : Nat) : nombre_constructible (Complex.exp (2*Complex.I*↑Real.pi/↑n)) ↔ ∀ (p : Nat.Primes), p ∣ n → (premierfermat p ∧ padicValNat p n = 1):= by
sorry

--Lemme : bijection corps intermédiaires/sous-groupes IsGalois.intermediateFieldEquivSubgroup
--theorem groupe_galois_Qw_ZpZ {p : ℕ} (hp : 0 < (p : Nat)) : premierfermat p → galCyclotomicEquivUnitsZMod (Polynomial.cyclotomic.irreducible_rat hp):= by
-- Lemme : si p est de Fermat, alors Gal(ℚ(w)/ℚ)≅(ℤ/pℤ)*
--theorem groupe_galois_Qw_ZpZ (p : ℕ+) (h : Irreducible (Polynomial.cyclotomic ↑p ℚ)) : premierfermat ↑p → galXPowEquivUnitsZMod h :=by
--theorem groupe_galois_Qw_ZpZ (p : ℕ+): premierfermat p → ∃ m, (Polynomial.Gal (Polynomial.cyclotomic p ℚ)) ≃* (ZMod (2^m)) := by
-- IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree
