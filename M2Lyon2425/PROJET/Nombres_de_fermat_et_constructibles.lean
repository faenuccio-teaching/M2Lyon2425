import Mathlib.Tactic.Common
import Mathlib
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.Multiplicity

open Complex

--TENTATIVE DE PREUVE DU THEOREME DE GAUSS-WANTZEl--

-- Le p^α gone régulier (p premier) est constructible à la règle et au compas (définition de Wantzel) si et
-- seulement si [p=2] ou [α=1 et p est de Fermat].

--On désignera par w le nombre Complex.exp (2*↑Real.pi*Complex.I/p)

--extra lemmes venant d'une autre version de mathlib.

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
  instChar : ∀ i, CharZero (K i)
  instAlgebra : ∀ i, Algebra (K i) (K (i + 1))

--Definition d'être une tour de corps
def TQ : TowerOfFields := by
  refine ⟨fun _ ↦ ℚ , fun _ ↦ inferInstance, sorry,fun _ ↦ Algebra.id ℚ⟩
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
        FiniteDimensional.finrank (T.K i) (T.K (i + 1)) ≤ 2 ∧ FiniteDimensional.finrank (T.K i) (T.K (i+1)) > 0

--Définition : un nombre a est constructible s'il existe une tour quadratique de ℚ vers ℚ(a).

def nombre_constructible (a : ℂ) : Prop :=
  ∃ (T : TowerOfFields) (n : ℕ)
    (_ : letI := T.instField 0; letI := T.instChar 0; T.K 0 ≃ₐ[ℚ] ℚ)
    (_ : letI := T.instField n; letI := T.instChar n; T.K n ≃ₐ[ℚ] (Algebra.adjoin ℚ { a })),
    T.isFiniteDimensional ∧ T.rankLessTwo ∧ T.K 0 = ℚ

--Théorème : multiplicativité des degrés
theorem multiplicativity_degree (m n : ℕ+) (R S T : Type*) [i1 : Field R] [i2 : Field S] [i3 : Field T] [i4 : Algebra R S] [i5 : Algebra S T] [i6 : Algebra R T] : FiniteDimensional.finrank R S = m ∧ FiniteDimensional.finrank S T = n → (FiniteDimensional.finrank R T = m*n) := by
intro h1
cases h1 with
| intro left right => have h1 : 0 < FiniteDimensional.finrank R S := by
                        rw[left]
                        exact PNat.pos m
                      have h2 : 0 < FiniteDimensional.finrank S T :=by
                        rw[right]
                        exact PNat.pos n
                      apply Module.finite_of_finrank_pos at h2
                      apply Module.finite_of_finrank_pos at h1
                      let hRS := FiniteDimensional.finBasis R S
                      rw[left] at hRS
                      let hST := FiniteDimensional.finBasis S T
                      rw[right] at hST
                      have scalartow : IsScalarTower R S T :=by
                        constructor
                        intro xR yS zT
                        sorry
                      have hRT := Basis.smulTower hRS hST
                      have hf := FiniteDimensional.finrank_eq_card_basis hRT
                      rw[hf]
                      have hff : Fintype.card (Fin ↑m × Fin ↑n) = Fintype.card (Fin ↑(m * n)):=by
                        have hfin : Fin m × Fin n ≃ Fin (m * n) :=by
                          exact finProdFinEquiv
                        exact Fintype.card_congr hfin
                      rw[hff]
                      exact Fintype.card_fin ↑(m * n)

--Théorème (Wantzel) : si a est constructible, ℚ(a) est de degré 2^m sur ℚ pour un certains m.
theorem Wantzel1 (a : ℂ ) : nombre_constructible a → ∃ (m : ℕ), (FiniteDimensional.finrank ℚ (Algebra.adjoin ℚ { a })) = 2^m := by
  intro nb_consa
  obtain ⟨⟨K, K1, K2, K3⟩, h1, base, top, h2, h3, h4⟩ := nb_consa
  dsimp at base top
  have algebra_n : ∀ (n :ℕ), Algebra (K 0) (K n) :=by
    intro n
    induction n with
    | zero => exact Algebra.id (K 0)
    | succ n ih => have halgebran1 := K3 n
                   apply RingHom.toAlgebra
                   apply algebraMap at ih
                   apply algebraMap at halgebran1
                   exact halgebran1.comp ih
  have hyp : ∀ (n : ℕ), ∃ (m : ℕ), FiniteDimensional.finrank (K 0) (K n) = 2^m :=by
    intro n
    induction n with
    | zero => use 0
              simp
              have hhh := @FiniteDimensional.finrank_self (K 0) _ _
              rw[<-hhh]
              congr
              sorry
    | succ n ih => obtain ⟨m,hm⟩ := ih
                   by_cases his2 : FiniteDimensional.finrank (K n) (K (n + 1)) = 2
                   · use (m+1)
                     have hmul := multiplicativity_degree (2^m) 2 (K 0) (K n) (K (n+1))
                     apply hmul
                     constructor
                     · exact hm
                     · exact his2
                   · use m
                     have hmul := multiplicativity_degree (2^m) 1 (K 0) (K n) (K (n+1))
                     simp at hmul
                     apply hmul
                     · exact hm
                     · push_neg at his2
                       have hh1 := h3 n
                       dsimp at hh1
                       cases hh1 with
                       | intro left right => apply Nat.one_le_of_lt at right
                                             apply Ne.le_iff_lt at his2
                                             apply his2.mp at left
                                             apply Nat.le_sub_one_of_lt at left
                                             simp at left
                                             exact Eq.symm (Nat.le_antisymm right left)
  specialize hyp h1
  obtain ⟨mhyp, hmyp⟩:= hyp
  use mhyp
  rw[<-hmyp]
  rw [← top.toLinearEquiv.finrank_eq]
  sorry


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
  exact IsCyclotomicExtension.isGalois p ℚ (CyclotomicField p ℚ)

--Lemme : ℤ/(2^m)ℤ est un groupe résoluble
theorem Z2mZ_resoluble (m : Nat) : IsSolvable (ZMod (2^m))ˣ := by
  have h : ∀ (a b : (ZMod (2^m))ˣ), a * b = b * a := by
    intro a b
    rw[Units.instCommGroupUnits.proof_1]
  exact isSolvable_of_comm h

--Lemme : le polynôme minimal de w_α est Phi p^α
theorem poly_min_w_sur_Q (p : ℕ) (α : ℕ) : Nat.Prime p → 0 < α → minpoly ℚ (Complex.exp (2*↑Real.pi*Complex.I/(p^α))) = (Polynomial.cyclotomic (↑p^α) ℚ) := by
  intro h _
  have h1 := Complex.isPrimitiveRoot_exp (p^α) (pos_iff_ne_zero.mp (@Nat.pow_pos p α (Nat.Prime.pos h)))
  have h2 := (Polynomial.cyclotomic_eq_minpoly_rat h1 (@Nat.pow_pos p α (Nat.Prime.pos h))).symm
  simp at h2
  exact h2

--Lemme : w_α est algébrique sur ℚ
theorem wa_algebrique_sur_Q (p α : ℕ) : Nat.Prime p → 0 < α →  IsAlgebraic ℚ (Complex.exp (2*↑Real.pi*Complex.I/(p^α))) := by
  intro h a
  have h1 : minpoly ℚ (Complex.exp (2*↑Real.pi*Complex.I/(p^α))) = (Polynomial.cyclotomic (↑p^α) ℚ) := by
    exact poly_min_w_sur_Q p α  h a
  constructor
  · constructor
    · exact Polynomial.cyclotomic_ne_zero (p^α) ℚ
    · rw[h1.symm]
      simp

--Lemme : ℚ(w) est intégrale
theorem adjoin_is_integral (α : ℕ) (p : ℕ) : Nat.Prime p ∧ 0 < α → IsIntegral ℚ (Complex.exp (2*↑Real.pi*Complex.I/(p^α))) := by
  intro h
  apply IsAlgebraic.isIntegral
  apply wa_algebrique_sur_Q
  · exact h.left
  · exact h.right

--Lemme : dim (ℚ(w)/ℚ)=p^(α-1)*(p-1)
theorem degQw (α : ℕ) (p : Nat) : Nat.Prime p ∧ 0 < α → FiniteDimensional.finrank ℚ (Algebra.adjoin ℚ { Complex.exp (2*↑Real.pi*Complex.I/(p^α)) }) = p^(α-1)*(p-1) := by
  intro h
  have h1 := IntermediateField.adjoin.finrank ((adjoin_is_integral α p) h)
  have h2 := IntermediateField.adjoin_simple_toSubalgebra_of_integral ((adjoin_is_integral α p) h)
  let S := {z : ℂ | z = Complex.exp (2*↑Real.pi*Complex.I/(p^α)) }
  have h4 : ∀ z ∈ S, IsAlgebraic ℚ z :=by
    intro z
    intro hz
    change (z = Complex.exp (2*↑Real.pi*Complex.I/(p^α))) at hz
    rw[hz]
    exact (wa_algebrique_sur_Q p α h.left h.right)
  have h3 := IntermediateField.adjoin_algebraic_toSubalgebra h4
  cases h with
  | intro left right =>
    rw[poly_min_w_sur_Q p α left right, Polynomial.natDegree_cyclotomic,Nat.totient_prime_pow] at h1
    rw[h1.symm]
    · have := congr_arg Subalgebra.toSubmodule h2
      let e := LinearEquiv.ofEq _ _ this
      have := congr_arg Cardinal.toNat e.rank_eq
      exact this.symm
    · exact left
    · exact right

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
theorem Gauss_Wantzel_p_sens_direct (p : Nat) (α : Nat) : Nat.Prime p ∧ 0 < α ∧ nombre_constructible (Complex.exp (2*↑Real.pi*Complex.I/(p^α))) → ((premierfermat p ∧ α =1) ∨ p=2) :=by
 intro h
 cases h with
 | intro left right =>
   cases right with
   | intro left1 right1 =>
     apply Wantzel1 at right1
     have h2 := (degQw α p)
     have h3 : (FiniteDimensional.finrank ℚ ↥(Algebra.adjoin ℚ {Complex.exp (2 * ↑Real.pi * Complex.I/ ↑p ^ α)})) =
       p ^ (α - 1) * (p - 1) := by
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

--Lemme : (Z/pZ)ˣ est cyclique
theorem ZModx_cyclic (p : ℕ) : Nat.Prime p → IsCyclic (ZMod p)ˣ := by
--preuve dans Perrin, à voir si j'implémente modulo le temps restant.
  sorry

--theorem tower_normal (m : ℕ) (G : Type*) [inst1 : Group G] [inst2 : IsCyclic G] : G ≃* ZMod (2^m) → ∃ (ζ : G), ((Subgroup.zpowers ζ = G) ∧ (Subgroup.zpowers (ζ^(2^m))=IsSubgroup.trivial G) ∧ (∀ k < m, @IsNormalSubgroup (Subgroup.zpowers (ζ^(2^k))) ) := by
/-
theorem adjoin_is_cyclo (p : ℕ+) (α : ℕ): Nat.Prime p ∧ 0 < α  → IsCyclotomicExtension {p^α} ℚ (Algebra.adjoin ℚ {Complex.exp (2 * ↑Real.pi * Complex.I/ ↑(p^α))}) := by
intro h
rw[IsCyclotomicExtension.iff_singleton]
constructor
· let ζ := (Complex.exp (2 * ↑Real.pi * Complex.I/ ↑(p^α)))
  use ⟨ζ, Algebra.self_mem_adjoin_singleton ℚ ζ⟩
  have h3 := Complex.isPrimitiveRoot_exp (p^α) (pos_iff_ne_zero.mp (@Nat.pow_pos p α (Nat.Prime.pos h.left)))
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h3
· intro x
  have hh : {Complex.exp (2 * ↑Real.pi * Complex.I/ ↑(p^α))} ⊆ {b | b ^ ↑↑(p ^ α) = 1} := by
    intro xx hx
    simp at hx
    have hxx := Complex.isPrimitiveRoot_exp (p^α) (Nat.pos_iff_ne_zero.mp (@Nat.pow_pos p α (Nat.Prime.pos h.left)))
    dsimp
    rw[IsPrimitiveRoot.iff_def] at hxx
    have hxx := hxx.left
    rw[hx]
    simp at hxx
    exact hxx
  apply @Algebra.adjoin_mono ℚ at hh
  simp at hh
  obtain ⟨x, bx⟩ := x
  have cx : x ∈ Algebra.adjoin ℚ {b | b ^ ↑↑(p ^ α) = 1} := by
    apply hh
    simp at bx
    exact bx
  by_contra hf
  sorry
-/
theorem adjoin_is_cyclo (p : ℕ+) (α : ℕ) (_: Nat.Prime p) (_ : 0 < α) :
  IsCyclotomicExtension {p^α} ℚ (Algebra.adjoin ℚ
    {exp (2 * ↑Real.pi * Complex.I/ ↑(p^α))}) :=
IsPrimitiveRoot.adjoin_isCyclotomicExtension _ (isPrimitiveRoot_exp _ (PNat.ne_zero (p ^ α)))

theorem cyclic_iso (G H : Type*) [inst1 : Group G] [inst2 : Group H] : (G ≃* H) → (IsCyclic H) → (IsCyclic G) := by
intro h h1
obtain ⟨ φ, phi1⟩ := h
obtain ⟨ ϕ, hphi, left_inv, right_inv⟩ := φ
dsimp at phi1
apply IsCyclic.exists_generator at h1
obtain ⟨ Hgen, hypHgen ⟩ := h1
apply IsCyclic.mk
use (hphi Hgen)
intro g
dsimp
have h_rec : ∀ (x y : H), hphi (x * y) = (hphi x) * (hphi y) := by
  intro x y
  have h111 : (hphi x) * (hphi y) = (hphi ∘ ϕ) ((hphi x) * (hphi y)):= by
    have h1111 : (hphi ∘ ϕ) ((hphi x) * (hphi y))= id ((hphi x) * (hphi y)) := by
      apply left_inv
    rw[h1111]
    trivial
  rw[Function.comp_apply, phi1,] at h111
  change (hphi x * hphi y = hphi ( ((ϕ ∘ hphi) x) * ((ϕ ∘ hphi) y))) at h111
  have hinutile : ∀ (x : H), (ϕ ∘ hphi) x = x:= by
    apply right_inv
  rw[hinutile, hinutile] at h111
  exact h111.symm
have hh : ∀ n, hphi  Hgen ^ n = hphi (Hgen ^ n) :=by
  intro n
  induction n with
  | zero => simp
            have hhh := h_rec 1 1
            simp at hhh
            exact hhh.symm
  | succ n ih => have hh1 := npow_add n 1 Hgen
                 apply (congr_arg hphi) at hh1
                 rw[h_rec] at hh1
                 simp at hh1
                 rw[<-ih] at hh1
                 have hh2 : hphi Hgen ^ n * hphi Hgen = hphi Hgen ^ (n+1):= by
                  group
                 rw[hh2] at hh1
                 exact hh1.symm
have hhmieux : ∀ (n : ℤ), hphi  Hgen ^ n = hphi (Hgen ^ n) :=by
  intro n
  cases Int.nonneg_or_nonneg_neg n with
  | inl h => apply (Int.nonneg_def).mp at h
             obtain ⟨ npos, hnpos ⟩ := h
             have hbis := hh ↑npos
             rw[hnpos]
             simp
             exact hbis
  | inr h => apply (Int.nonneg_def).mp at h
             obtain ⟨ npos, hnpos ⟩ := h
             have hbis := hh npos
             rw[<-@Int.neg_neg n, hnpos]
             simp
             rw[hbis]
             refine Eq.symm (eq_inv_of_mul_eq_one_left ?inr.intro.h)
             rw[<-h_rec]
             simp
             have hhh := h_rec 1 1
             simp at hhh
             exact hhh
let phig := ϕ g
have hphig : ϕ g = phig := by rfl
specialize hypHgen phig
let o := hypHgen.choose
have ho := hypHgen.choose_spec
dsimp at ho
use o
have hg : (hphi ∘ ϕ) g = g := by
  apply left_inv
rw [Function.comp_apply,hphig,<-ho,<-hhmieux] at hg
exact hg

theorem finite_iso (G H : Type*) [inst1 : Group G] [inst2 : Group H] : (G ≃* H) → (Finite H) → (Finite G):= by
intro phi cardh
obtain ⟨phii, _⟩ := phi
have h := Equiv.finite_iff phii
apply h.mpr
exact cardh

structure TowerOfGroup2 {G : Type*} [Group G] where
  H : ℕ → Subgroup G
  inclusion : ∀ i, H (i + 1) ≤ H i
  normalSubGroup : ∀ i, @IsNormalSubgroup (H i) _ (Subgroup.inclusion (inclusion i)).range


theorem Gauss_Wantzel_p_sens_reciproque (p : ℕ+) (α : Nat) : (premierfermat p ∧ α =1) → (Nat.Prime p ∧ 0 < α ∧ nombre_constructible (Complex.exp (2*Complex.I*↑Real.pi/(p^α)))) := by
intro h
cases h with
| intro hp ha =>
    constructor
    · exact hp.left
    · constructor
      · rw[ha]; exact Nat.one_pos
      · have Gp_Galois := Polynomial.Gal.instGroup (Polynomial.cyclotomic (↑p) ℚ)
        have Gp_Galois_iso := (Polynomial.cyclotomic.irreducible_rat (Nat.Prime.pos hp.left))
        apply galCyclotomicEquivUnitsZMod at Gp_Galois_iso
        have zmodcycl := ZModx_cyclic p hp.left
        have Gp_Galois_cycl : IsCyclic (Polynomial.cyclotomic ↑p ℚ).Gal :=by
          have hh := cyclic_iso ((Polynomial.cyclotomic ↑p ℚ).Gal) ((ZMod ↑p)ˣ) (Gp_Galois_iso) zmodcycl
          exact hh
        have exist_gen := @IsCyclic.exists_generator (Polynomial.cyclotomic (↑p) ℚ).Gal Gp_Galois Gp_Galois_cycl
        let ζ := exist_gen.choose
        have hz := exist_gen.choose_spec
        --have hsub := @IsGalois.intermediateFieldEquivSubgroup ℚ Rat.instField (Algebra.adjoin ℚ { (Complex.exp (2*Complex.I*↑Real.pi/(p))) }) (sorry) (sorry) (sorry) (sorry) (sorry)
        sorry
        sorry
        sorry
        sorry
        sorry
--Lemme : bijection corps intermédiaires/sous-groupes IsGalois.intermediateFieldEquivSubgroup
--theorem groupe_galois_Qw_ZpZ {p : ℕ} (hp : 0 < (p : Nat)) : premierfermat p → galCyclotomicEquivUnitsZMod (Polynomial.cyclotomic.irreducible_rat hp):= by
-- Lemme : si p est de Fermat, alors Gal(ℚ(w)/ℚ)≅(ℤ/pℤ)*
--theorem groupe_galois_Qw_ZpZ (p : ℕ+) (h : Irreducible (Polynomial.cyclotomic ↑p ℚ)) : premierfermat ↑p → galXPowEquivUnitsZMod h :=by
--theorem groupe_galois_Qw_ZpZ (p : ℕ+): premierfermat p → ∃ m, (Polynomial.Gal (Polynomial.cyclotomic p ℚ)) ≃* (ZMod (2^m)) := by
-- IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree

  --instNormalSubgroup: ∀ i, IsNormalSubgroup (G i)
--Definition d'être une tour de corps de dimension fin
--have algebraicRS := @Algebra.IsAlgebraic.of_finite R S
