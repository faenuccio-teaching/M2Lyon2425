import Mathlib.Tactic.Common

import «Project».AbstractRewritingSystem
import «Project».Definition
import «Project».SimpleTypes

/-!
# Strong Normalization

In the [SimpleTypes] file, we have defined a type system à la Curry for our λ-calculus.
Here, we are going to show that this type system does what we want it to do: we show that 
every term that can be typed derives finitely in a normal form.

## References

* [S. Mimram. PROGRAM=PROOF. 2022][Mim22] 
Note that the structure of this file roughly follows Samuel Mimram's proof, but that the lemmas
needed are a bit more difficult as we use De Bruijn's indices. Anyway, everything that we show
is explained. -/

/-! One naive proof that we could try is to proceed by induction on the typing relation.
Then, the cases of variable and λ-abstraction are trivial. But the case of application is
not true: a reduction in M N is not always a reduction in M or a reduction in N: if M is 
a λ-abstraction, then it is M[N/x] and we cannot conclude anything with the induction 
hypotheses.

Hence, the naive proof fails. We thus use a fairly common device in the literature: 
reducibility candidates. Strictly speaking, in the simply-typed λ-calculus, this approach
is only a "patch" of the naive proof: it makes it so that if M and N are reducibility 
candidates, then M N is also a reducibility candidate, bypassing the previous problem.

Then, we need to show two things: (i) that every reducibility candidate is strongly 
normalizing and (ii) that every typable term is a reducibility candidate. 
We manage (i) by crafting these reducibility candidates to do just that: the 
reducibility candidates of a type variable X are all the strongly normalizing terms of X,
and the reducibility candidates of a type A → B are all the M : A → B such that for N a 
reducibility candidate of A, M N is a reducibility candidate of B. -/
def Red (M : Λ) (A : Ty) : Prop :=
  match A with
  | Ty.Var _ => is_strongly_normalizing βreduction M
  | Ty.Fun A B => ∀ (N : Λ), Red N A → Red (Lambda.App M N) B 

/-!
Now, we are able to successfully dodge the last problem. But it's not obvious that every
reducibility candidate of A → B is strongly normalizing. We start by focusing on proving
that.

To do so, we need to strenghten the induction hypotheses, and we show the 3 properties
of reducibility candidates.
  ∙ (CR1) If M is a reducibility candidate for A, then M is strongly normalizing.
  ∙ (CR2) If M is a reducibility candidate for A and M →β N, then so is N.
  ∙ (CR3) If M is neutral and (N is a reducibility candidate for A whenever M →β N), then
          M is a reducibility candidate for A.

First, we define what a neutral is. Intuitively, we want neutrals to be "everything not
immediatly of type A → B", i.e., everything except a λ-abstraction. We will see why a bit 
later. -/
inductive Neutral : Λ → Prop :=
  | Var : ∀ (x : ℕ), Neutral (Lambda.Var x)
  | App : ∀ (M N : Λ), Neutral (Lambda.App M N)

/-! Let us show the 3 CR properties. We shall do them all at once, as we need all of them 
together during the induction. We proceed by induction on A. -/
lemma cr_aux :
  ∀ (A : Ty) (M : Λ), 
      (Red M A → is_strongly_normalizing βreduction M) ∧
      (∀ (N : Λ), Red M A → M →β N → Red N A) ∧
      (Neutral M → (∀ (N : Λ), M →β N → Red N A) → Red M A) := by
  intro A; induction' A with X A B ihA ihB
  · intro M; constructor 
    · tauto 
    · constructor
      · intro N hred h; induction hred with
        | intro P hacc _ => apply hacc; assumption
      · intro _ h; constructor; assumption
  · intro M; constructor
    · intro hred
      have : Red (Lambda.Var 0) A := by 
        apply (ihA (Lambda.Var 0)).right.right
        constructor; intro N h; cases h
      have : Red (Lambda.App M (Lambda.Var 0)) B := by
        exact hred (Lambda.Var 0) this
      have : is_strongly_normalizing βreduction (Lambda.App M (Lambda.Var 0)) := by
        exact (ihB (Lambda.App M (Lambda.Var 0))).left this
      generalize e : Lambda.App M (Lambda.Var 0) = N
      rw [e] at this; revert M; induction' this with P _ ih
      intro M hred hred' e; constructor; intro Q hqm; apply ih
      rw [←e]; apply βreduction.context₂; exact hqm
      intro Q' hred''; apply (ihB (Lambda.App M Q')).right.left; apply hred; assumption
      constructor; assumption
      apply (ihB (Lambda.App M (Lambda.Var 0))).right.left; assumption
      constructor; assumption; rfl
    · constructor
      · intro N hred h P hredP
        specialize hred P hredP
        apply (ihB (M.App P)).right.left
        assumption
        constructor; assumption
      · intro hneut h N hred
        have : is_strongly_normalizing βreduction N := by
          exact (ihA N).left hred 
        induction' this with P _ ih
        apply (ihB (Lambda.App M P)).right.right
        constructor; intro N hpn; cases hpn with
        | β M => cases hneut
        | context₁ _ _ Q hpq => apply ih; assumption; apply (ihA P).right.left
                                assumption; assumption
        | context₂ _ _ Q hmq => apply h; assumption; assumption

/-! We add some shortcuts. -/
lemma CR1 : 
  ∀ (A : Ty) (M : Λ), 
    Red M A → is_strongly_normalizing βreduction M := by
  intro A M; apply (cr_aux A M).left

lemma CR2 : 
  ∀ (A : Ty) (M N : Λ), 
    Red M A → M →β N → Red N A := by
  intro A M; apply (cr_aux A M).right.left

lemma CR3 :
  ∀ (A : Ty) (M : Λ),
    Neutral M → (∀ (N : Λ), M →β N → Red N A) → Red M A := by
  intro A M; apply (cr_aux A M).right.right

/-! Now, we can show (ii), i.e., we wish to show that if Γ ⊢ M : A, then Red M A.
    
    What we actually want to do is to show the following key lemma: if a term is typable under
    a context composed of (xᵢ, Aᵢ), then for every Mᵢ such that Red Mᵢ Aᵢ, the *simultaneous* 
    substitution of every xᵢ by every Mᵢ is a reducibility candidate. 

    First, we need to have a definition of simultaneous substitution. Intuitively, this 
    notion is the same as substituting once, except that the term loses |Γ| free variables
    instead of 1. -/
def simultaneous_substitution (n : ℕ) (M : Λ) (Γ : List Λ) : Λ :=
  match M with
  | Lambda.Var x =>
    if n ≤ x then
      match Γ[x - n]? with
      | some N => lift n 0 N
      | none => Lambda.Var (x - Γ.length)
    else Lambda.Var x
  | Lambda.Lam M => Lambda.Lam (simultaneous_substitution (n + 1) M Γ)
  | Lambda.App M N => Lambda.App (simultaneous_substitution n M Γ) 
                                 (simultaneous_substitution n N Γ)

/-! This definition allows us to show the following lemma: if we substitute at n the
    result of a simultaneous substitution at rank (n + 1), then it's the same as adding 
    the term substituted at the head of the simultaneous substitution at rank n. -/
lemma simultaneous_substitution_lemma :
  ∀ (M N : Λ) (Mᵢ : List Λ) (n : ℕ), 
    (simultaneous_substitution (n + 1) M Mᵢ)[N⧸n] = 
      simultaneous_substitution n M (N::Mᵢ) := by
  intro M; induction' M with x M ihM M P ihM ihP <;> intro N Mᵢ n
  · unfold simultaneous_substitution; split; aesop -- this aesop is a shortcut to unfold ifs
                                                   -- and matches
    · rw [substitution_lemma_aux₂, Nat.add_sub_cancel_right]
      have e : N_1 = N_2 := by 
        rw [getElem?_cons] at heq_1; split at heq_1; omega
        rw [Nat.sub_add_eq] at heq; rw [heq_1] at heq; injection heq; symm; assumption
      rw [e]; omega; omega
    · have : Mᵢ.length ≤ x - (n + 1) := by omega
      have : Mᵢ[x - (n + 1)]? = none := List.getElem?_eq_none_iff.mpr this
      rw [this] at heq; contradiction
    · omega 
    · have : (N :: Mᵢ).length ≤ x - n := by simp; omega
      have : (N :: Mᵢ)[x - n]? = none := List.getElem?_eq_none_iff.mpr this
      rw [this] at heq_1; contradiction
    · unfold substitute; split; omega; split; omega; rfl        
    · omega
    · split; aesop -- this aesop is a shortcut to unfold the match
      · have : n = x := by omega
        rw [this]; unfold substitute; split; omega; split
        rw [this, Nat.sub_eq_zero_of_le Nat.le.refl, List.getElem?_cons_zero] at heq
        injection heq with e; rw [e]; omega
      · unfold substitute; split; omega; split; omega
        have : n = x := by omega
        omega
      unfold substitute; split; rfl; split; omega; omega
  · unfold simultaneous_substitution; unfold substitute; rw [ihM]
  · unfold simultaneous_substitution; unfold substitute; rw [ihM, ihP]

/-! Actually, in the previous lemma, we used [n] to be able to have a nice induction
    hypothesis. We will use it with n = 0, for λ-abstractions. Indeed, we have the
    following fact: -/
lemma sn_substitution_lemma :
  ∀ (M : Λ) (A B : Ty), 
    (∀ (N : Λ), Red N A → Red (M[N⧸0]) B)
    → Red (Lambda.Lam M) (Ty.Fun A B) := by
  intro M A B h N hred
  have hN : is_strongly_normalizing βreduction N := by
    apply CR1; assumption
  have hM : is_strongly_normalizing βreduction M := by
    have hM : is_strongly_normalizing βreduction (M[N⧸0]) := by
      apply CR1; apply h; assumption
    generalize e : M[N⧸0] = P; 
    rw [e] at hM; revert M; induction' hM with P _ ihP; intro M h e
    constructor; intro M' hM'; apply ihP; rw[←e]; apply context_subst; assumption
    intro N hred; apply CR2; apply h; assumption; apply context_subst; assumption
    rfl
  induction' hN with N _ ihN; induction' hM with M _ ihM
  apply CR3; constructor; intro P hP; cases hP with
  | β _ _ => apply h; assumption
  | context₁ _ _ N' hN' => apply ihN; exact hN'; apply CR2; exact hred; exact hN'
  | context₂ _ _ M' hM' => cases hM' with
    | context₀ _ M' hM' => apply ihM; exact hM'; intro P hP; apply CR2
                           apply h; exact hP; apply context_subst; exact hM'
                           intro P hP hredP; apply CR2; apply ihN; exact hP; exact hredP
                           constructor; constructor; exact hM'

lemma getElem?_eq {α : Type} (l : List α) (i : Nat) :
    l[i]? = if h : i < l.length then some l[i] else none :=
  getElem?_def _ _

/-! Combining these two things allows us to show the key lemma: -/
lemma key_lemma :
  ∀ (M : Λ) (Γ : List Ty) (A : Ty) (Mᵢ : List Λ),
    (Γ ⊢ M : A) → (List.length Γ = List.length Mᵢ) →
    (∀ (x : ℕ) (Aᵢ : Ty) (N : Λ), Γ[x]? = some Aᵢ → Mᵢ[x]? = some N → Red N Aᵢ) →
    Red (simultaneous_substitution 0 M Mᵢ) A := by
  intro M Γ A Mᵢ hty; revert Mᵢ
  induction' hty with Γ x A e' Γ M A B _ ih Γ M N _ B _ _ ihM ihN 
    <;> intro Mᵢ e hred
  · unfold simultaneous_substitution
    obtain ⟨ N, h ⟩ : ∃ N, Mᵢ[x]? = some N := by
      rw [getElem?_eq]; split
      · use Mᵢ[x]
      · have : List.get? Γ x = none := by rw [List.get?_eq_none, e]; omega
        rw [e'] at this; contradiction
    split; rw [Nat.sub_zero, h]; simp; rw [lift_zero]; apply hred; rw [← e']; simp; rfl
    assumption; omega
  · apply sn_substitution_lemma; intro N h; rw [simultaneous_substitution_lemma];
    apply ih; simp; assumption; intro x Aᵢ Nᵢ e₀ e₁; rw [getElem?_cons] at e₀
    rw [getElem?_cons] at e₁; split at e₀; split at e₁; injection e₀ with e₀
    injection e₁ with e₁; rw [←e₀, ←e₁]; assumption; contradiction
    split at e₁; contradiction; apply hred; assumption; assumption
  · unfold simultaneous_substitution; apply ihM; assumption; assumption
    apply ihN; assumption; assumption

/-! Now, our goal is to substitute all the free variables of (Γ ⊢) M by... themselves!
    Indeed, Red x Aᵢ for every x and Aᵢ by CR3 (x is neutral and does not reduce). 
    Then, we'll have shown that if a term is typable, it is a reducibility candidate.
    By CR1, it will mean that it is strongly normalizing.

    First, we should show that simultaneously substituting every variable by themselves 
    yields the same λ-term. To do so, we need to be sure that no free-variable is forgotten.
    This check is done by defining a predicate by induction on a λ-term. -/
def all_fv_within' (M : Λ) (k n : ℕ) :=
  match M with
  | Lambda.Var x => if x < k then True else x - k < n
  | Lambda.Lam M => all_fv_within' M (k + 1) n
  | Lambda.App M N => all_fv_within' M k n ∧ all_fv_within' N k n

def all_fv_within (M : Λ) (n : ℕ) := all_fv_within' M 0 n
  
/-! And indeed, we can show that if everything is in order, then substituting everything
    by itself yields the very same λ-term: -/
lemma simultaneous_substitution_id' : 
  ∀ (M : Λ) (n k : ℕ), 
    all_fv_within' M k n →
    simultaneous_substitution k M (List.map (λx => Lambda.Var x) (List.range n)) = M := by
  intro M; induction' M with x M ihM M N ihM ihN <;> intro n k h
  · unfold simultaneous_substitution; aesop -- deals with ifs & matches
    have : (List.range n)[x - k]? = some (x - k) := by 
      rw [List.getElem?_range]; unfold all_fv_within' at h
      simp at h; apply h; assumption
    rw [this] at left; injection left with e; rw [←e]; unfold lift; simp
    rw [Nat.sub_add_cancel a]; unfold all_fv_within' at h
    simp at h; omega
  · unfold simultaneous_substitution; rw [ihM]; unfold all_fv_within' at h; assumption
  · unfold simultaneous_substitution; unfold all_fv_within' at h; rw [ihM, ihN]
    exact h.right; exact h.left

/-! We now show that if a term is typable, then all its free variable are in the context. 

    For this, we need a small lemma to permute the arguments in all_fv_within': -/
lemma all_fv_within'_permute : 
  ∀ (M : Λ) (m n k : ℕ),
    all_fv_within' M m (n + k)
      → all_fv_within' M (m + k) n := by
  intro M; induction' M with x M ihM M N ihM ihN <;> intro m n k h
  · unfold all_fv_within'; unfold all_fv_within' at h; simp at h; split
    trivial; omega
  · unfold all_fv_within'; unfold all_fv_within' at h; rw [Nat.add_right_comm]
    apply ihM; assumption
  · unfold all_fv_within'; unfold all_fv_within' at h; constructor
    apply ihM; exact h.left; apply ihN; exact h.right

/-! And then, we can show the desired lemma: -/
lemma is_typable_all_fv_within :
  ∀ (M : Λ) (Γ : Con) (A : Ty),
    (Γ ⊢ M : A) → all_fv_within M (List.length Γ) := by
  intro M Γ A h; induction h with
  | Var Γ x A e => unfold all_fv_within; unfold all_fv_within'; simp
                   by_contra
                   have : List.get? Γ x = none := by rw [List.get?_eq_none]; omega
                   rw [this] at e; contradiction
  | Fun Γ M A B h ih => unfold all_fv_within; unfold all_fv_within'; simp
                        unfold all_fv_within at ih; simp at ih; 
                        apply all_fv_within'_permute M 0 (List.length Γ) 1; assumption
  | App Γ M N A B hM hN ihM ihN => unfold all_fv_within; unfold all_fv_within'; constructor
                                   unfold all_fv_within at ihM; assumption
                                   unfold all_fv_within at ihN; assumption

/-! We can get more friendly statement for the lemma about the simultaneous substitution: -/
lemma simultaneous_substitution_id : 
  ∀ (M : Λ) (Γ : Con) (A : Ty),
    (Γ ⊢ M : A) →
    simultaneous_substitution 0 M 
      (List.map (λx => Lambda.Var x) (List.range (List.length Γ))) = M := by
  intro M Γ A h; apply simultaneous_substitution_id'; apply is_typable_all_fv_within
  assumption

/-! And we can finally prove that, if Γ ⊢ M : A, then Red M A. -/
lemma adequacy :
  ∀ (M : Λ) (Γ : Con) (A : Ty),
    (Γ ⊢ M : A) → Red M A := by
  intro M Γ A h
  have e : simultaneous_substitution 0 M 
             (List.map (λx => Lambda.Var x) (List.range (List.length Γ))) = M := by 
         apply simultaneous_substitution_id; assumption
  rw [←e]; apply key_lemma; assumption; rw [List.length_map, List.length_range]
  intro x Aᵢ N _ e'; simp at e'; cases e' with
    | intro y h => apply CR3
                   · rw [←h.right]; constructor
                   · rw [←h.right]; intro _ contra; cases contra

/-! By CR1, it means that every typable term is strongly normalizing. -/
theorem strong_normalization :
  ∀ {M : Λ} {Γ : Con} {A : Ty},
    (Γ ⊢ M : A) → is_strongly_normalizing βreduction M := by
  intro M Γ A h; apply CR1; apply adequacy; assumption

/- Note that we cannot say that βreduction is an instance of IsStronglyNormalizing:
   it is the case only if the considered term can be typed (we could say so if we had defined
   the λ-calculus à la Church). -/
