import Mathlib.Tactic.Common

import «Project».AbstractRewritingSystem
/-!
# Definition

In this file, we define the set of λ-terms, as well as the computation of the λ-calculus,
called β-reduction. -/

/-!
## The set of λ-terms

We define the minimal version of λ-calculus as an inductive grammar:
  M, N ::= x | λ x. M | M N
where `x` is a variable.

Here, we choose to define a variable as an integer ─ we use De Bruijn's indices to avoid
dealing with free variables. -/
inductive Lambda
| Var : ℕ → Lambda
| Lam : Lambda → Lambda
| App : Lambda → Lambda → Lambda

notation "Λ" => Lambda

/-!
## Substitution on λ-terms

As we use De Bruijn's indices, we cannot directly define the substitution.
Instead, we first have to define a "lifting" operation (lift j i M) by induction on M:
  ∙ If M = Var n, then (↑ j i M) = n if n < i, n + j otherwise
  ∙ If M = (λ M'), then (↑ j i M) = λ (↑ j (i + 1) M')
  ∙ If M = N P, then (↑ j i M) = (↑ j i N) (↑ j i P).
 -/
def lift (j i : ℕ) (M : Λ) : Λ :=
  match M with
  | Lambda.Var n => if n < i then Lambda.Var n else Lambda.Var (n + j)
  | Lambda.Lam M => Lambda.Lam (lift j (i + 1) M)
  | Lambda.App M N => Lambda.App (lift j i M) (lift j i N)

/-! We can simplify the result of two liftings:
       ↑ m ℓ (↑ i j M) = ↑ (m + i) j M
    and:
      ↑ m j (↑ i j M) = ↑ m (i + j) (↑ i j M)
    for j ≤ ℓ ≤ i + j. -/
lemma double_lift :
  ∀ (i j ℓ m : ℕ) (M : Λ), j ≤ ℓ ∧ ℓ ≤ i + j → lift m ℓ (lift i j M) = lift (m + i) j M := by
  intro i j ℓ m M ⟨ hle₁, hle₂ ⟩; revert m ℓ j i; induction M with
  | Var n => 
    intros i j ℓ m hle₁ hle₂
    change lift m ℓ (if n < j then Lambda.Var n else Lambda.Var (n + i)) = lift (m + i) j (Lambda.Var n); split
    · have : n < ℓ := by omega
      unfold lift; split <;> rfl
    · have : n + i >= ℓ := by omega
      unfold lift; split
      · omega
      · have : n + i + m = n + (m + i) := by omega
        rw [this]
  | Lam M ih => 
    intros i j ℓ m hle₁ hle₂
    change lift m ℓ (Lambda.Lam (lift i (j + 1) M)) = Lambda.Lam (lift (m + i) (j + 1) M)
    change Lambda.Lam (lift m (ℓ + 1) (lift i (j + 1) M)) = Lambda.Lam (lift (m + i) (j + 1) M)
    rw [ih] <;> omega
  | App M N ihM ihN =>
    intros i j ℓ m hle₁ hle₂
    change Lambda.App (lift m ℓ (lift i j M)) (lift m ℓ (lift i j N)) =
             Lambda.App (lift (m + i) j M) (lift (m + i) j N)
    rw [ihM, ihN] <;> omega

lemma double_lift' :
  ∀ (i j ℓ m : ℕ) (M : Λ), j ≤ ℓ ∧ ℓ ≤ i + j 
    → lift m j (lift i j M) = lift m (i + j) (lift i j M) := by
  intro i j ℓ m M ⟨ Hle₁, Hle₂ ⟩; revert m ℓ j i; induction M with
  | Var n => 
    intros i j ℓ m _ _
    change (lift m j (if n < j then Lambda.Var n else Lambda.Var (n + i))) = 
                 (lift m (i + j) (if n < j then Lambda.Var n else Lambda.Var (n + i)))
    split
    · have : n < i + j := by omega
      unfold lift; split <;> rfl
    · have : n + i ≥ i + j := by omega
      unfold lift; split
      · omega
      · split; omega; rfl
  | Lam M ih => 
    intros i j ℓ m hle₁ hle₂
    change Lambda.Lam (lift m (j + 1) (lift i (j + 1) M)) = 
             Lambda.Lam (lift m (i + j + 1) (lift i (j + 1) M))
    rw [ih i (j + 1) (ℓ + 1) m, Nat.add_assoc] <;> omega
  | App M N ihM ihN => 
    intros i j ℓ m hle₁ hle₂
    change Lambda.App (lift m j (lift i j M)) (lift m j (lift i j N)) =
             Lambda.App (lift m (i + j) (lift i j M)) (lift m (i + j) (lift i j N))
    rw [ihM i j ℓ m, ihN i j ℓ m] <;> omega

/-! If i ≥ ℓ, we can show that ↑ k ℓ (↑ j i M) = ↑ j (i + k) (↑ k ℓ M). -/
lemma double_lift'' :
  ∀ (i j k ℓ : ℕ) (M : Λ), i ≥ ℓ → lift k ℓ (lift j i M) = lift j (i + k) (lift k ℓ M) := by
  intro i j k ℓ M hle; revert ℓ k j i; induction M with
  | Var n =>
    intro i j k ℓ hle
    conv_lhs => change lift k ℓ (if n < i then Lambda.Var n else Lambda.Var (n + j)); rfl
    conv_rhs => change lift j (i + k) (if n < ℓ then Lambda.Var n else Lambda.Var (n + k)); rfl
    split
    · split
      · unfold lift; split; split; rfl; omega; split; rfl; omega
      · unfold lift; split; omega; split; rfl; omega
    · split
      · omega
      · unfold lift; split; omega; split; omega; rw [Nat.add_right_comm]
  | Lam M ih =>
    intro i j k ℓ hle 
    conv_lhs => change Lambda.Lam (lift k (ℓ + 1) (lift j (i + 1) M)); rfl
    conv_rhs => change Lambda.Lam (lift j (i + k + 1) (lift k (ℓ + 1) M)); rfl
    rw [ih]; rw [Nat.add_right_comm]; omega
  | App M N ihM ihN =>
    intro i j k ℓ hle
    conv_lhs => change Lambda.App (lift k ℓ (lift j i M)) (lift k ℓ (lift j i N)); rfl
    conv_rhs => change Lambda.App (lift j (i + k) (lift k ℓ M)) (lift j (i + k) (lift k ℓ N))
                rfl
    rw [ihM, ihN] <;> trivial

/-! Then, we can define substitution as follows: M[N/k] is defined by induction on M:
    ∙ n[N/k] = n if n < k, lift k 0 N if n = k and n - 1 if n > k
    ∙ (λ.M)[N/k] = λ.M[N/k+1]
    ∙ (M P)[N/k] = M[N/k] P[N/k] -/
def substitute (M N : Λ) (k : ℕ) : Λ :=
  match M with
  | Lambda.Var n => if n < k then Lambda.Var n
                    else if n = k then lift k 0 N
                      else Lambda.Var (n - 1)
  | Lambda.Lam M => Lambda.Lam (substitute M N (k + 1))
  | Lambda.App M P => Lambda.App (substitute M N k) (substitute P N k)

notation M "[" N "⧸" k "]" => substitute M N k

/-! Now, we wish to show the substitution lemma, i.e., that:
         M[N/k][P/ℓ] = M[P/ℓ + 1][N[P/ℓ - k]/k]
    with k ≤ ℓ.

    We start by showing that if i + m ≤ j, then (↑ m i M)[N/j] = ↑ m i (M[N/j - m]). -/
lemma substitution_lemma_aux₁ :
  ∀ (M N : Λ) (i j m : ℕ), i + m ≤ j →
    (lift m i M)[N⧸j] = lift m i (M[N⧸(j - m)]) := by
  intro M N; induction M with
  | Var n => 
    intro i j m hle
    change (if n < i then Lambda.Var n else Lambda.Var (n + m))[N⧸j] =
             lift m i (if n < j - m then Lambda.Var n else if n = j - m then lift (j - m) 0 N else Lambda.Var (n - 1))
    split
    · have : n < j - m := by omega
      have : n < j := by omega
      unfold substitute; split <;> unfold lift <;> split <;> rfl
    · split
      · have : n + m < j := by omega
        unfold substitute; split <;> unfold lift <;> split
        · omega
        · rfl
        · omega
        · rfl
      · split
        · have : n + m = j := by omega
          have : m + (j - m) = j := by omega
          unfold substitute; split; omega; rw [double_lift, this]
          constructor <;> omega
        · unfold substitute; split; omega; split; omega
          unfold lift; split; omega
          have : n + m - 1 = n - 1 + m := by omega
          rw [this]
  | Lam M ih =>
    intro i j m hle
    change Lambda.Lam ((lift m (i + 1) M)[N⧸(j + 1)]) = 
            (Lambda.Lam (lift m (i + 1) (M[N⧸(j - m + 1)])))
    have : j + 1 - m = j - m + 1 := by omega
    rw [ih, this]; omega    
  | App M P ihM ihP =>
    intro i j m hle
    change Lambda.App ((lift m i M)[N⧸j]) ((lift m i P)[N⧸j]) =
             Lambda.App (lift m i (M[N⧸j - m])) (lift m i (P[N⧸j - m]))
    rw [ihM, ihP] <;> omega

/-- The last step before showing the substitution lemma is to show that:
      if i ≤ j < m + i, then (↑ m i M)[N⧸j] = ↑ (m - 1) i M. -/
lemma substitution_lemma_aux₂ :
  ∀ (M N : Λ) (i j m : ℕ), i ≤ j → j < m + i →
    (lift m i M)[N⧸j] = lift (m - 1) i M := by
  intro M N; induction M with
  | Var n =>
    intro i j m hij hj
    change (if n < i then Lambda.Var n else Lambda.Var (n + m))[N⧸j] = 
             lift (m - 1) i (Lambda.Var n)
    split
    · unfold substitute; split; unfold lift; split; rfl; rfl; omega
    · unfold substitute; split; omega; split; omega
      have : n + m - 1 = n + (m - 1) := by omega
      unfold lift; split; omega; rw [this]
  | Lam M ih =>
    intro i j m hij hj
    change Lambda.Lam ((lift m (i + 1) M)[N⧸j + 1]) =
             Lambda.Lam (lift (m - 1) (i + 1) M)
    rw [ih] <;> omega
  | App M P ihM ihP =>
    intro i j m hij hj
    change Lambda.App ((lift m i M)[N⧸j]) ((lift m i P)[N⧸j]) =
             Lambda.App (lift (m - 1) i M) (lift (m - 1) i P)
    rw [ihM, ihP] <;> omega

/-- We can now show the substitution lemma. --/
lemma substitution_lemma :
  ∀ (M N P : Λ) (k ℓ : ℕ), k ≤ ℓ →
    M[N⧸k][P⧸ℓ] = M[P⧸ℓ+1][N[P⧸ℓ-k]⧸k] := by
  intro M N P; induction M with
  | Var n => 
    intro k ℓ hle
    change (if n < k then Lambda.Var n else 
               if n = k then lift k 0 N else Lambda.Var (n - 1))[P⧸ℓ] =
           (if n < ℓ + 1 then Lambda.Var n else
               if n = ℓ + 1 then lift (ℓ + 1) 0 P else Lambda.Var (n - 1))[N[P⧸ℓ-k]⧸k]
    split
    · have : n < ℓ := by omega /- Case n < k -/ 
      split
      · unfold substitute; split <;> rfl
      · omega
    · split
      · have : n < ℓ + 1 := by omega /- Case n = k -/
        split
        · conv_rhs => unfold substitute; rfl
          split; omega
          rw [substitution_lemma_aux₁]; omega
        · omega
      · conv_lhs => unfold substitute; rfl  /- Case n > k -/
        split
        · have : n < ℓ + 1 := by omega      /- Case n - 1 < ℓ -/
          split; unfold substitute; split; omega; rfl; omega
        · split
          · have : n = ℓ + 1 := by omega /- Case n - 1 = ℓ -/
            split; omega; rw [substitution_lemma_aux₂, Nat.add_sub_cancel_right] <;> omega
          · have : n > ℓ + 1 := by omega /- Case n - 1 > ℓ -/
            split; omega; split; omega; unfold substitute; split; omega; split
            omega; rfl
  | Lam M ih =>
    intro k ℓ hle
    change Lambda.Lam (M[N⧸k+1][P⧸ℓ+1]) =
             Lambda.Lam (M[P⧸ℓ+2][N[P⧸ℓ-k]⧸k+1])
    rw [ih]; rw [Nat.add_sub_add_right]; omega
  | App M M' ihM ihM' =>
    intro k ℓ hle
    change Lambda.App (M[N⧸k][P⧸ℓ]) (M'[N⧸k][P⧸ℓ]) =
             Lambda.App (M[P⧸ℓ+1][N[P⧸ℓ-k]⧸k]) (M'[P⧸ℓ+1][N[P⧸ℓ-k]⧸k])
    rw [ihM, ihM'] <;> trivial

/-- Another interesting situation in substitutions is upon lifting inside a substitution. -/
lemma lift_substitute :
  ∀ (i j k : ℕ) (M N : Λ), 
    (lift j (i + k + 1) M)[lift j i N⧸k] = lift j (i + k) (M[N⧸k]) := by
  intro i j k M N; revert k j i; induction M with
  | Var n =>
    intro i j k
    conv_lhs => change (if n < i + k + 1 then Lambda.Var n else Lambda.Var (n + j))[lift j i N⧸k]; rfl
    split
    · unfold substitute; split
      · unfold lift; split; rfl; omega
      · split
        · rw [double_lift'']; omega
        · unfold lift; split; rfl; omega
    · unfold substitute; split; omega; split; omega; split; omega; split; omega
      unfold lift; split; omega
      have : n - 1 + j = n + j - 1 := by omega
      rw [this]
  | Lam M ih => 
    intro i j k
    conv_lhs => change Lambda.Lam ((lift j (i + (k + 1) + 1) M)[lift j i N⧸k + 1]); rfl
    conv_rhs => change Lambda.Lam (lift j (i + k + 1) (M[N⧸k + 1])); rfl
    rw [ih i j (k + 1)]; rfl
  | App M P ihM ihP =>
    intro i j k
    conv_lhs => change Lambda.App ((lift j (i + k + 1) M)[lift j i N⧸k]) 
                                  ((lift j (i + k + 1) P)[lift j i N⧸k]); rfl
    conv_rhs => change Lambda.App (lift j (i + k) (M[N⧸k])) (lift j (i + k) (P[N⧸k])); rfl
    rw [ihM, ihP]

/-!
## β-reduction

We now define the relation of β-reduction between λ-terms, defined as the least binary
relation that contains the following rule:
  (λx. M)N →β M[N/x] -/
inductive βreduction : Λ → Λ → Prop :=
  | β : ∀ M N, βreduction (Lambda.App (Lambda.Lam M) N) (M[N⧸0])
  | context₀ : ∀ M N, βreduction M N → βreduction (Lambda.Lam M) (Lambda.Lam N)
  | context₁ : ∀ M N P, βreduction N P → βreduction (Lambda.App M N) (Lambda.App M P)
  | context₂ : ∀ M N P, βreduction M P → βreduction (Lambda.App M N) (Lambda.App P N)

infixl:75 " →β " => βreduction
infixl:75 " →β⁺ " => βreduction⁺
infixl:75 " →β⋆ " => βreduction⋆
infixl:75 " ≡β " => βreduction≡ 

/-! ## Context of closures -/

lemma context₀_trans : 
  ∀ M M', M →β⁺ M' → (Lambda.Lam M) →β⁺ (Lambda.Lam M') := by
  intro M M' h; induction' h with M M' h M M' M'' h _ ih
  · left; constructor; trivial
  · right; constructor; trivial; trivial

lemma context₁_trans :
  ∀ M N N', N →β⁺ N' → Lambda.App M N →β⁺ Lambda.App M N' := by
  intro M N N' h; induction' h with N N' h N N' N'' h _ ih
  · left; constructor; trivial
  · right; constructor; trivial; trivial

lemma context₂_trans :
  ∀ M M' N, M →β⁺ M' → Lambda.App M N →β⁺ Lambda.App M' N := by
  intro M M' N h; induction' h with M M' h M M' M'' h _ ih
  · left; constructor; trivial
  · right; apply βreduction.context₂; trivial; trivial

lemma context₀_trans_refl :
  ∀ M M', M →β⋆ M' → (Lambda.Lam M) →β⋆ (Lambda.Lam M') := by
  intro M M' h; cases h with
  | inl h => left; apply context₀_trans; trivial
  | inr e => right; rw [e]

lemma context₁_trans_refl :
  ∀ M N N', N →β⋆ N' → (Lambda.App M N) →β⋆ (Lambda.App M N') := by
  intro M N N' h; cases h with
  | inl h => left; apply context₁_trans; trivial
  | inr e => right; rw [e]

lemma context₂_trans_refl :
  ∀ M M' N, M →β⋆ M' → (Lambda.App M N) →β⋆ (Lambda.App M' N) := by
  intro M M' N h; cases h with
  | inl h => left; apply context₂_trans; trivial
  | inr e => right; rw [e]
