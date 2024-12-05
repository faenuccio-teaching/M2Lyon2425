/-
  ## Rings, fields, polynomials and linear algebra 2
  Credits.
  * Formalising Mathematics 2022 - 2024, K. Buzzard
  * Mathematics in Lean, J. Avigad, P. Massot
-/
import Mathlib.Tactic.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.LinearAlgebra.Dimension.Finrank

/-
  # Chinese Remainder Theorem
  We prove a general version of the CRT to practice working with ideals
-/

section CRT

variable {ι R : Type*} [CommRing R]

open Ideal Quotient Function

#check Pi.ringHom

#check ker_Pi_Quotient_mk

/-- The homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i`` featured in the Chinese
  Remainder Theorem. -/
def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
  sorry

lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x :=
  sorry

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x :=
  sorry

#check injective_lift_iff

lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
  sorry

#check IsCoprime

#check isCoprime_iff_add

#check isCoprime_iff_exists

#check isCoprime_iff_sup_eq

#check isCoprime_iff_codisjoint

#check Finset.mem_insert_of_mem

#check Finset.mem_insert_self

theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
        1 = I + K                  := sorry
        _ = I + K * (I + J i)      := sorry
        _ = (1 + K) * I + K * J i  := sorry
        _ ≤ I + K ⊓ J i            := sorry

lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
    (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  intro g
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      sorry
    sorry
  choose e he using key
  use mk _ (∑ i, f i * e i)
  sorry

noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
    chineseMap f with }

end CRT

/-
  # Algebras and polynomials
  We now look at algebras by focusing on polynomials algebra
-/

noncomputable section Algebras

-- Define `A` to be an `R`-algebra
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

-- It comes with a `RingHom` called `algebraMap R A` that encodes the action of `R` over `A` and thus
-- gives the scalar multiplication of `A` by `R` denote `•` (use `\smul` to write `•`).
example (r : R) (a : A) : r • a = algebraMap R A r * a := Algebra.smul_def r a

example (r r' : R) (a : A) : (r + r') • a = r • a + r' • a := by
  sorry

example (r r' : R) (a : A) : (r * r') • a = r • r' • a := by
  sorry

-- The type of `A` and `B` are two `R`-algebras, the type of R-algebra morphism is `AlgHom R A B` with
-- the notation `A →ₐ[R] B` and `A ≃ₐ[R] B` for `AlgEquiv R A B`.

-- Assume that `R ⊆ S ⊆ T` is a tower of `CommRing`, so `S` is a `R`-algebra and `T` is a `S`-algebra and also
-- a `R`-algebra. The fact that the three scalar multiplications are compatible is given by the mixin
-- `IsScalarTower`.
variable (S T : Type*) [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]

-- This fails
example (r : R) (s : S) (t : T) : (r • s) • t = r • (s • t) := by
  exact?

example [IsScalarTower R S T] (r : R) (s : S) (t : T) : (r • s) • t = r • (s • t) := by
  sorry

-- The algebra of polynomials with coefficients in `R` is `Polynomial R` with the notation `R[X]` available
-- in the namespace `Polynomial`. The indeterminate is denote `X` and we use the notation `C` to denote the
-- constant polynomial

open Polynomial

-- We need to give the type so that Lean knows which ring to use
example : R[X] := X - C 1

-- `C` is defined as a ring homomorphism

example (r : R) : (X + C r) * (X - C r) = X ^ 2 - C (r ^ 2) := by
  ring -- this is not enough
  sorry

-- The coefficients of a polynomial can be accessed using `Polynomial.coeff`

example : (X ^ 3 - 2 * X + C 1 : R[X]).coeff 1 = - 2 := by
  rw [coeff_add, coeff_sub, coeff_X_pow]
  rw [if_neg (by linarith), zero_sub]
  rw [coeff_C, if_neg one_ne_zero, add_zero]
  rw [coeff_ofNat_mul, coeff_X_one, mul_one]

-- It is trickier to define the degree of polynomials because of the `0` polynomial. Usually, the degree of
-- the `0` polynomial is set to be `-∞` but that it is not a `Nat`. Thus, we use instead `WithBot ℕ` which
-- is the type of `ℕ` with an additional element -- the bottom --, denote `⊥` (use `\bot` to write `⊥`) which
-- is smaller than any other other element of `Nat`.

example (a : ℕ) : ⊥ < (a : WithBot ℕ) := WithBot.bot_lt_coe a

example (a : ℕ) : ⊥ + (a : WithBot ℕ) = ⊥ := rfl

-- Note that `a * ⊥ = ⊥` if `a` is nonzero but `0 * ⊥ = 0`.

example (a : ℕ) (ha : (a : WithBot ℕ) ≠ 0) : (a : WithBot ℕ) * ⊥ = ⊥ := WithBot.bot_mul ha

example : (0 : WithBot ℕ) * ⊥ = 0 := rfl

-- In `Mathlib`, the corresponding function is called `Polynomial.degree`.

example : (0 : R[X]).degree = ⊥ := rfl

-- It satisfies the mathematical properties expected, for example:

example [IsDomain R] (P Q : R[X]) : (P * Q).degree = P.degree + Q.degree := degree_mul

-- However, it is quite inconvenient to work in `WithBot ℕ`, so there also the function `Polynomial.natDegree`
-- that sets the degree of the `0` polynomial to be `0`. Of course, both functions agree on nonzero polynomials.

example (P : R[X]) (h : P ≠ 0) : P.degree = P.natDegree := degree_eq_natDegree h

-- Computing the degree of a polynomial can be a difficult task, but there is a tactic to help!

example : ((X + 1 : R[X]) * (2 * X + 1)).natDegree = 2 := by
  compute_degree
  · sorry
  · simp

-- Every polynomial gives rise to a polynomial function `Polynomial.eval`.

example (r : R) :  (X + C r).eval r = 2 * r := by
  rw [eval_add, eval_X, eval_C, two_mul]

-- Note that, in the last example, we didn't need to give the type of the polynomial. Why?

-- Sometimes, we want to evaluate at a value that is not the coefficient ring `R`, but in a `R`-algebra `A`.
-- For this, there is `Polynomial.aeval` that sends `a : A` to the corresponding evaluation map which is
-- of type `R[X] →ₐ[R] A`.

example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp

-- In the same way, the roots of a polynomial are not necessarily in its coefficient ring, also
-- they come with multiplicities so there is the need for several notions of roots. As always, the
-- `0` polynomial is also causing difficulties.

-- If `r : R` then `r` is a root of `P` iff `P(r) = 0`.

example (r : R) (P : R[X]) : IsRoot P r ↔ P.eval r = 0 := Iff.rfl

-- `Polynomial.roots` is the set of roots in its coefficient ring `R` with multiplicities. It is a `multiset`.
-- For the `0` polynomial, it returns the empty (multi)set.

example [IsDomain R] (r : R) : (X - C r).roots = {r} := by
  sorry

example [IsDomain R] (r : R) (n : ℕ) : ((X - C r) ^ n).roots = n • {r} := by
  rw [roots_pow, roots_X_sub_C]

-- For the roots in a `R`-algebra `A`, we use `Polynomial.aroots`. It returns a multiset of `A` with the
-- same convention for the `0` polynomial.

open Complex Polynomial

#check root_mul

example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by
    rw [aroots_def]
    rwa [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    have key : (C I * C I : ℂ[X]) = -1 := by
      rw [← C_mul, I_mul_I, map_neg, map_one]
    rw [C_neg]
    linear_combination key
  -- The result then follows from `roots_mul`
  rw [factored, roots_mul, roots_X_sub_C, roots_X_sub_C]
  · simp
  · by_contra! h
    apply_fun eval 0 at h
    simp [eval] at h

end Algebras

/-
  # Linear algebra
  Vector spaces in Mathlib are defined as modules over a field.
-/

noncomputable section Vectorspaces

variable {K : Type*} (V : Type*) [Field K] [AddCommGroup V] [Module K V]

-- we have the usual axioms

example (k : K) (u v : V) : k • (u + v) = k • u + k • v := by
  sorry

example (k l : K) (u : V) : (k + l) • u = k • u + l • u := by
  sorry

example (k l : K) (u : V) : k • l • u = (k * l) • u := by
  sorry


-- The type of linear maps is denoted `V →ₗ[K] W` with an `l` in subscript for linear. The type of
-- linear isomorphism is `V ≃ₗ[K] W`.

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

example (a : K) (v : V) : φ (a • v) = a • φ v := map_smul φ a v

example (v w : V) : φ (v + w) = φ v + φ w := map_add φ v w

-- Of course, `V →ₗ[K] W` is also a vector space

#synth Module K (V →ₗ[K] W)

-- Every element `k : K` defines a linear map: the multiplication by `k`. Let's define it

def mul_by (x : K) : V →ₗ[K] V where
  toFun := fun v ↦ x • v
  map_add' := sorry
  map_smul' := sorry

-- Some API
theorem mul_by_apply (x : K) (v : V) : mul_by V x v = x • v := rfl

-- Since the set of linear map on `V` is a vector space, we can add these maps

theorem mul_by_add (x y : K) : mul_by V (x + y) = mul_by V x + mul_by V y := by
  ext
  simp_rw [mul_by_apply]
  rw [LinearMap.add_apply]
  simp_rw [mul_by_apply]
  sorry

-- And look at the scalar multiplication

theorem smul_mul_by (k x : K) : mul_by V (k * x) = k • mul_by V x := by
  sorry

-- Hum, can we use these properties to prove that the set `mul_by` is a subvector-space?

variable (K) in -- See below for an explanation of this
def ImageMulBy : Submodule K (V →ₗ[K] V) where
  carrier := Set.range (mul_by V)
  zero_mem' := by
    dsimp only
    use 0
    sorry
  add_mem' := by
    intro φ ψ hφ hψ
    obtain ⟨x, rfl⟩ := hφ
    obtain ⟨y, rfl⟩ := hψ
    sorry
  smul_mem' := sorry

-- We need to tell Lean what `K` is here since `V` could be a vector space for several fields, think for
-- example of `ℂ`-vector spaces, they are also `ℝ`-vector spaces.

-- Since `ImageMulBy` is a submodule, Lean can infer that it is also a module

#synth Module K (ImageMulBy K V)

-- and the map `x ↦ MulBy V x` is linear by the above. Let's first rebundle `mul_by` into a linear map.

def LinearMulBy' : K →ₗ[K] (V →ₗ[K] V) where
  toFun := fun x ↦ mul_by V x
  map_add' := mul_by_add V
  map_smul' := smul_mul_by V

-- We want now to restrict the codomain to `ImageMulBy` and there is a function for that

def LinearMulBy : K →ₗ[K] ImageMulBy K V := by
  refine LinearMap.codRestrict (ImageMulBy K V) (LinearMulBy' V) ?_
  sorry

-- In fact, this map should be a linear equiv so let's construct it.

#check LinearEquiv.ofBijective

def EquivMulBy : K ≃ₗ[K] ImageMulBy K V := by
  refine .ofBijective (LinearMulBy V) ⟨?_, ?_⟩
  · sorry
  · sorry

-- Linear maps come also with their range and kernel, but also with the corresponding pushing and pulling
-- on subspaces (and then range and kernel are just special cases).

#where

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)

example : LinearMap.range φ = Submodule.map φ ⊤ := by
  sorry

example : LinearMap.ker φ = Submodule.comap φ ⊥ := by
  sorry

example : LinearMap.ker φ = ⊥ ↔ Function.Injective φ := by
  sorry

example : LinearMap.range φ = ⊤ ↔ Function.Surjective φ := by
  sorry

-- # Bases.
-- In Mathlib, a basis on the `K`-vector space `V` is defined as an linear equiv between `V` and `K ^ ι`
-- for some type `ι`. The vector space `K ^ ι` is defined as the set `ι →₀ K` with a `K`-module structure
-- where `ι →₀ K` is the type of finitely supported functions from `ι` to `K` (that is equal to `0` except for
-- a finite subset of `ι`). When `ι` is finite, then this is equivalent to `ι → K`.

variable {ι : Type*}

example [Finite ι] : (ι →₀ K) ≃ (ι → K) := Finsupp.equivFunOnFinite

variable (B : Basis ι K V) -- A `K`-basis of `V`

example (i : ι) : V := B i -- The `i-th` vector of the basis

example : V ≃ₗ[K] (ι →₀ K) := B.repr -- The isomorphism

example (v : V) (i : ι) : K := B.repr v i -- The coefficient of `v` on the basis vector `B i`

-- To construct a basis for a family `b` of vectors that are linearly independent and span the whole
-- vector space, we have `Basis.mk`.

def my_basis (b : ι → V) (h_indep : LinearIndependent K b) (h_span : Submodule.span K (Set.range b) = ⊤) :
    Basis ι K V := by
  apply Basis.mk
  · exact h_indep
  · rw [h_span]

example (b : ι → V) (h_indep : LinearIndependent K b) (h_span : Submodule.span K (Set.range b) = ⊤) (i : ι) :
    my_basis V b h_indep h_span i = b i := by
  rw [my_basis, Basis.mk_apply]

-- The vector space  `ι →₀ K` comes with its standard basis formed on the vectors `Finsupp.singe i 1` with
-- `i : ι`. In the case `ι` is finite though, there is the simpler `Pi.basisFun`.

example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by rfl

-- There are several equivalent definition of `LinearlyIndependent`, perhaps the one that is the more
-- natural is the following

example (b : ι → V) :
    LinearIndependent K b ↔ ∀ (s : Finset ι) (c : ι → K),
      ∑ i in s, c i • b i = 0 → ∀ i ∈ s, c i = 0 := linearIndependent_iff'

-- Now, we would like to express the fact that a vector `v : V` is the sum `c i • B i` where the
-- `c i` are its coefficients on the basis `B`. Of course, this makes sense only because all but finitely
-- many `c i`'s are equal to zero. Let's start with finite case where things are much simpler.

example [Fintype ι] (v : V) :
    ∑ i, B.repr v i • B i = v := Basis.sum_equivFun B v

-- In the general case, we need to use `Finsupp.total`
-- Note that `Finsupp.total` has been renamed to `Finsupp.linearCombination` in more recent versions of Mathlib.

#check Finsupp.total

example (v : V) :
    Finsupp.total ι V K B (B.repr v) = v := Basis.total_repr B v

-- Let `W` be another `K`-vector space. Any linear map `V →ₗ[K] W` is fully determined by its value on
-- the elements of the basis `B` and thus gives a linea equiv between `ι → W` and `V →ₗ[K] W`.

#check Basis.constr

example {W : Type*} [AddCommGroup W] [Module K W] (im : ι → W) :
    V →ₗ[K] W := Basis.constr B K im

example {W : Type*} [AddCommGroup W] [Module K W] (im : ι → W) (i : ι) :
    Basis.constr B K im (B i) = im i := by
  sorry

-- In the same way, two linear maps from `V` to `W` are equal iff they are equal on the basis `B`.

example {W : Type*} [AddCommGroup W] [Module K W] (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) :
    φ = ψ := Basis.ext B h

-- So we now have all the tools to prove the following

example {W : Type*} [AddCommGroup W] [Module K W] (im : ι → W) :
    ∃! φ : V →ₗ[K] W, ∀ i, φ (B i) = im i := by
  refine ⟨?_, ?_, ?_⟩
  · sorry -- Define φ
  · sorry -- Proves that it satisfies the required property
  · sorry -- Proves that it is unique

-- # Dimension
-- We will only talk about dimension in the finite dimensional case. In this case, it is
-- given by `FiniteDimensional.finrank K V` with the convention that it is equal to `0` if `V` is not
-- of finite dimension over `K`.
-- Note that `FiniteDimensional.finrank` has been renamed to `Module.finrank`
-- in more recent versions of Mathlib

open FiniteDimensional

-- The prototype of a `K`-vector space of dimension `n` is `K ^ n` a.k.a. `Fin n → K`

example (n : ℕ) : finrank K (Fin n → K) = n := finrank_fin_fun K

example : finrank K K = 1 := finrank_self K

-- Mathlib knows about some classical cases

example : finrank ℝ ℂ = 2 := Complex.finrank_real_complex

-- If `finrank K V = 0`, then it could be that `V` is the trivial vector space or that it is not
-- of finite dimension over `K`. In order to know in which case we are, there is the
-- `FiniteDimensional` typeclass.

example [FiniteDimensional K V] : 0 < finrank K V ↔ Nontrivial V := by
  sorry

-- If `V` admits a basis indexed by a `Finite` type, then it is of course finite dimensional
-- (Recall that `B : Basis ι K V`)

example [Finite ι] : FiniteDimensional K V := by
  sorry

-- and it is of course also true in the other direction!

example [FiniteDimensional K V] : Finite ι := (FiniteDimensional.fintypeBasisIndex B).finite

-- In this case, the dimension of the vector space is equal to the cardinality of the basis

example [Fintype ι] : finrank K V = Fintype.card ι := finrank_eq_card_basis B

-- Let's assume from now that `V` is finite dimensional over `K`

variable [FiniteDimensional K V]

-- Thus, of course, any submodule of `V` is also finite dimensional

variable (M : Submodule K V) in
#synth FiniteDimensional K M

example (M N : Submodule K V) :
    finrank K (M + N : Submodule K V) + finrank K (M ⊓ N : Submodule K V) =
      finrank K M + finrank K N :=
  Submodule.finrank_sup_add_finrank_inf_eq M N

example (M N : Submodule K V) (h : M ≤ N) :
    finrank K M ≤ finrank K N :=
  Submodule.finrank_le_finrank_of_le h

-- Note in passing the lattice structure on the submodules

example (M N : Submodule K V) : M ⊔ N = M + N := rfl

example (M N : Submodule K V) : M ⊓ N = (M ∩ N : Set V) := rfl

example (M N : Submodule K V) : M ≤ N ↔ (M : Set V) ⊆ N := Iff.rfl

-- To conclude a little exercise:

example  (M N : Submodule K V) (h : finrank K V < finrank K M + finrank K N) :
    Nontrivial (M ⊓ N : Submodule K V) := by
  sorry

end Vectorspaces

-- Vector spaces

-- Bases and dimensions
