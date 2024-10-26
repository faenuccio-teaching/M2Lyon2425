import Mathlib.Tactic.Common
import Mathlib
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.Multiplicity


--TENTATIVE DE PREUVE DU THEOREME DE  GAUSS-WANTZEl--

-- Le p^α gone régulier (p premier) est constructible à la règle et au compas (définition de Wantzel) si et
-- seulement si [p=2] ou [α=1 et p est de Fermat].

--On désignera par w le nombre Complex.exp (2*↑Real.pi*Complex.I/p)

-- Définiton d'un nombre premier de Fermat
def premierfermat (p : ℕ) :=
  (Nat.Prime p) ∧ (∃ n : ℕ, p=2^(2^n)+1)

--Lemme : si n est strictement positif, alors n=2^v₂(n) * z implique z impair
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
theorem premierfermat_eq (p : ℕ) : (premierfermat p) ↔ ((Nat.Prime p) ∧ (∃ m : ℕ, m>0 ∧ p=2^m+1)) := by
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

--noncomputable section

--Definition de la structure d'une tour de corps.
structure TowerOfFields where
  K : ℕ → Type*
  instField : ∀ i, Field (K i)
  instAlgebra : ∀ i, Algebra (K i) (K (i + 1))

--Definition d'être une tour de corps
def TQ : TowerOfFields := by
  refine ⟨fun _ ↦ ℚ , fun _ ↦ inferInstance, fun _ ↦ Algebra.id ℚ⟩

--Definition d'être une tour de corps de dimension finie
def TowerOfFields.isFiniteDimensional (T : TowerOfFields) : Prop :=
  ∀ i,  letI := T.instField i
        letI := T.instField (i + 1)
        letI := T.instAlgebra i
        FiniteDimensional (T.K i) (T.K (i + 1))

example : TQ.isFiniteDimensional := by
  intro _
  exact Module.Finite.self ℚ

--Definiton d'une tour de corps (Kᵢ)ᵢ telle que [Ki+1:Ki]≤ 2
def TowerOfFields.rankLessTwo (T : TowerOfFields) : Prop :=
  ∀ i,  letI := T.instField i
        letI := T.instField (i + 1)
        letI := T.instAlgebra i
        FiniteDimensional.finrank (T.K i) (T.K (i + 1)) ≤ 2

example : TQ.rankLessTwo := by
  intro _
  rw [TQ, FiniteDimensional.finrank_self]
  exact one_le_two

--Définition : un nombre a est constructible s'il existe une tour quadratique de ℚ vers ℚ(a).

def nombre_constructible (a : ℂ) : Prop :=
  ∃ (T : TowerOfFields) (n : ℕ), T.isFiniteDimensional ∧ T.rankLessTwo ∧ T.K 0 = ℚ ∧
    T.K n = Algebra.adjoin ℚ { a }

--Théorème (Wantzel) : si a est constructible, ℚ(a) est de degré 2^m sur ℚ pour un certains m.
theorem Wantzel1 (a : ℂ ) : nombre_constructible a → ∃ (m : ℕ), (FiniteDimensional.finrank ℚ (Algebra.adjoin ℚ { a })) = 2^m := by
 intro h
 cases h with
 | intro w h =>
   let n := h.choose
   let hn := h.choose_spec
   cases hn with
   | intro left right =>
      cases right with
      | intro left right =>
        sorry
      --rw[<-Module.finrank_mul_finrank] at left


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
theorem Z2mZ_resoluble (m : Nat) : IsSolvable (ZMod (2^m))ˣ := by
  have h : ∀ (a b : (ZMod (2^m))ˣ), a * b = b * a := by
    intro a b
    rw[Units.instCommGroupUnits.proof_1]
  exact isSolvable_of_comm h


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

--Lemme : le polynôme minimal de w_α est Phi p^α
theorem poly_min_w_sur_Q (p : ℕ+) (α : ℕ) : premierfermat p → 0 < α → minpoly ℚ (Complex.exp (2*↑Real.pi*Complex.I/(p^α))) = (Polynomial.cyclotomic (↑p^α) ℚ) := by
  intro h _
  cases h with
  | intro left right =>
    have h1 := Complex.isPrimitiveRoot_exp (p^α) (pos_iff_ne_zero.mp (@Nat.pow_pos p α (Nat.Prime.pos left)))
    have h2 := (Polynomial.cyclotomic_eq_minpoly_rat h1 (@Nat.pow_pos p α (Nat.Prime.pos left))).symm
    simp at h2
    exact h2



theorem degQw (α : ℕ) (p : Nat) : Nat.Prime p ∧ α > 0 → FiniteDimensional.finrank ℚ (Algebra.adjoin ℚ { Complex.exp (2*Complex.I*↑Real.pi/(p^α)) }) = p^(α-1)*(p-1) := by
  intro h
  cases h with
  | intro left right =>
    sorry

-- La valuation p-adique de p-1 est 0
theorem valplone (p : Nat) : Nat.Prime p → padicValNat p (p-1) = 0 := by
  intro hp
  by_contra h
  push_neg at h
  rw[<-neZero_iff] at h
  apply NeZero.one_le at h
  apply dvd_of_one_le_padicValNat at h
  have h2 : 0 < p-1 := by
    apply Nat.Prime.one_lt at hp
    apply Nat.sub_ne_zero_of_lt at hp
    apply Nat.zero_lt_of_ne_zero at hp
    exact hp
  apply (Nat.le_of_dvd h2) at h
  rw[<-Nat.pred_eq_sub_one] at h
  have h3 := Nat.pred_lt_self (Nat.Prime.pos hp)
  rw[le_iff_eq_or_lt] at h
  cases h with
  | inl h => apply Nat.ne_of_lt at h3; have h:= h.symm; contradiction
  | inr h => apply le_of_lt at h; apply Nat.not_lt.mpr at h; contradiction


-- Sens direct du théorème. Ajout du paramètre "Fact" pour utiliser les théorèmes sur les valutations.
theorem Gauss_Wantzel_p_sens_direct (p : Nat) (α : Nat) : Nat.Prime p ∧ 0 < α ∧ nombre_constructible (Complex.exp (2*Complex.I*↑Real.pi/(p^α))) → ((premierfermat p ∧ α =1) ∨ p=2) :=by
 intro h
 cases h with
 | intro left right =>
   cases right with
   | intro left1 right1 =>
     apply Wantzel1 at right1
     have h2 := (degQw α p)
     have h3 : FiniteDimensional.finrank ℚ ↥(Algebra.adjoin ℚ {Complex.exp (2 * Complex.I * ↑Real.pi / ↑p ^ α)}) =
       p ^ (α - 1) * (p - 1) :=by
       apply h2
       constructor
       · exact left
       · exact left1
     have h1 := Eq.trans right1.choose_spec.symm h3
     by_cases hp : p=2
     · right
       exact hp
     · have hodd := Nat.Prime.odd_of_ne_two left hp
       have ha : α = 1 := by
         by_contra hna
         push_neg at hna hp
         have twone : 2^right1.choose ≠ 0 := by
          exact Nat.not_eq_zero_of_lt (Nat.pos_pow_of_pos right1.choose (Nat.two_pos))
         have neprod : p^(α-1)*(p-1) ≠ 0 := by
          apply Nat.mul_ne_zero
          · by_contra h45
            rw[h45] at h1
            simp at h1
          · exact Nat.sub_ne_zero_of_lt (Nat.Prime.one_lt left)
         apply (Nat.eq_iff_prime_padicValNat_eq (2^right1.choose) (p^(α-1)*(p-1)) twone neprod).mp at h1
         specialize h1 p left
         have factp := jacobiSym.proof_1 p left
         rw[padicValNat.mul,padicValNat.prime_pow] at h1
         · have hvalplone := valplone p left
           rw[hvalplone] at h1
           simp at h1
           rw[padicValNat_prime_prime_pow] at h1
           have hf := h1.symm
           have h33 := (Nat.one_le_iff_ne_zero).mpr ((Nat.ne_zero_iff_zero_lt).mpr left1)
           rw[Nat.sub_eq_iff_eq_add'] at hf
           simp at hf
           contradiction
           exact h33; exact hp
         · by_contra h34
           rw [h34, Nat.zero_mul] at neprod
           contradiction
         · by_contra h34
           rw [h34, Nat.mul_zero] at neprod
           contradiction
       rw[Nat.mul_sub] at h1
       simp at h1
       rw[<-ha, Nat.sub_self,Nat.pow_zero] at h1
       simp at h1
       have h12 := Nat.eq_add_of_sub_eq (Nat.Prime.one_le left) h1.symm
       have h13 := (premierfermat_eq p).mpr
       left
       constructor
       · apply h13
         constructor
         · exact left
         · use right1.choose
           constructor
           · by_contra h14
             push_neg at h14
             have h15 := Nat.eq_zero_of_le_zero h14
             rw[h15] at h12
             simp at h12
             contradiction
           · exact h12
       · exact ha



theorem Gauss_Wantzel (n : Nat) : nombre_constructible (Complex.exp (2*Complex.I*↑Real.pi/↑n)) ↔ ∀ (p : Nat.Primes), p ∣ n → (premierfermat p ∧ padicValNat p n = 1):= by
sorry

--Lemme : bijection corps intermédiaires/sous-groupes IsGalois.intermediateFieldEquivSubgroup
--theorem groupe_galois_Qw_ZpZ {p : ℕ} (hp : 0 < (p : Nat)) : premierfermat p → galCyclotomicEquivUnitsZMod (Polynomial.cyclotomic.irreducible_rat hp):= by
-- Lemme : si p est de Fermat, alors Gal(ℚ(w)/ℚ)≅(ℤ/pℤ)*
--theorem groupe_galois_Qw_ZpZ (p : ℕ+) (h : Irreducible (Polynomial.cyclotomic ↑p ℚ)) : premierfermat ↑p → galXPowEquivUnitsZMod h :=by
--theorem groupe_galois_Qw_ZpZ (p : ℕ+): premierfermat p → ∃ m, (Polynomial.Gal (Polynomial.cyclotomic p ℚ)) ≃* (ZMod (2^m)) := by
-- IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree
