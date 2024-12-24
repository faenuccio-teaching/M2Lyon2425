import Mathlib.Tactic.Common

import «Project».Definition

/-!
# Simple Types

We have defined the λ-calculus and the computing steps of this model of computation, the 
β-reduction. In the file [Confluency], we have shown that the β-reduction defines a confluent
rewriting system; which is good as it means that if a term has normal form, then it is unique.
That is, we have some kind of [canonicity] and thus, we can define encodings that will
actually work. For instance, consider the following encoding of natural numbers, also called
[Church Numerals]:
  ∙ church 0 := λfλx.x
  ∙ church (n + 1) := λfλx. f (church n f x) (or λfλx. church n f (f x)).
By the confluency of β-reduction, as church numerals are normal form, we can define functions
from church numerals to church numerals:
  ∙ add n m := λfλx. n f (m f x)
  ∙ mul n m := λfλx. n (m f) x
  ∙ etc

But λ-calculus is also Turing-complete, which means that there exists λ-terms which loop
infinitely. The λ-term Ω is one such term:
  Ω := (λx.xx)(λx.xx) → (λx.xx)(λx.xx) → …

However, this kind of term is strange: what does one such thing mean? And there comes the
notion of types. A type can be thought of as a label put on terms which describe their 
behaviour. One famous quote from Robin Milner is:
  "A well-typed program cannot go wrong".

Here, going wrong means "loop infinitely". Our goal with simply-typed λ-calculus is thus to
label the terms so that, if a term is typed, then it always reduces to a normal form.

Note that, in the litterature, there are two ways to define simply-typed λ-calculus:
  ∙ typing à la Church, and
  ∙ typing à la Curry.
In the first case, typing comes built-in with the terms, i.e., a term can only be built
if it is well-typed. Conversely, we will implement typing à la Curry: we first build a λ-term,
and then we can check whether it can be typed or not. 

Simply-typed λ-calculus à la Church has some advantages, such as unicity of type and other 
structural niceties, but both styles lead to the same strong normalization proof. Here, we
prefer using λ-calculus à la Curry, so that we can prove things on λ-calculus in general,
not only on typed λ-calculus.

## References

* [S. Mimram. PROGRAM=PROOF. 2022][Mim22] 
Note that the book has been taken as reference, but most of the proofs in this file are "new",
in the sense that they use De Bruijn's indices and it's difficult to find proofs of such things
in the litterature. -/

/-!
## The set of types

The set of simple type is ─ as its name suggests ─ simple. It is composed of only two
types: a type variable and a function type. The set of types is defined inductively as follows:
  A, B ::= X | A → B
where `X` is a type variable, say [nat], [int], [monoid] or [group]. Here, we choose to 
represent a type variable as a string of characters, so that it's closer to the intuition. -/
inductive Ty
| Var : String → Ty
| Fun : Ty → Ty → Ty

/-!
## Typing a λ-term

Now that our types are defined, it's time that we type a term. Of course, there are
only two possible types for a term: a type variable, or a function. Our grammar reflects that:
we have (i) variables (ii) λ-abstractions (i.e., functions) and (iii) application. It's clear
that (i) can have any type, and (ii) is a function type. The question is: how do we type 
(iii)? In simply-typed λ-calculus, we say that an application (MN) is well-typed if 
M has type A → B and N has type A: M is a function which takes N as an argument.

The predicate [M is well-typed] can be defined by induction. Note that, if we let λx. M have 
type A → B, it means that x should have type A, and M[N/x] should have type B. But here, we see
that we need another element: what happens with a non-bound variable? How to type this?

As we also consider open terms, we need to have a [typing context], called [Con] here. -/
def Con : Type := List Ty

/-!
Then, we can finally define judgments of the form Γ ⊢ M : A to say that, under the context 
(Con) Γ, the λ-term M can be given the type A.
We must define 3 rules:
                                 Γ, x : A ⊢ M : B
   _________ (x, A) ∈ Γ          _________________
   Γ ⊢ x : A                     Γ ⊢ λx. M : A → B

           Γ ⊢ M : A → B    Γ ⊢ N : A
           __________________________
                 Γ ⊢ M N : B

Note that, as we are using De Bruijn's indices, we add things in the context at the start:
a variable has index 0 if it is bound to the last quantifier found. -/
inductive Typable : Con → Λ → Ty → Prop :=
  | Var : ∀ (Γ : Con) (x : ℕ) (A : Ty), Γ.get? x = some A → Typable Γ (Lambda.Var x) A
  | Fun : ∀ (Γ : Con) (M : Λ) (A B : Ty),
            Typable (A :: Γ) M B → Typable Γ (Lambda.Lam M) (Ty.Fun A B)
  | App : ∀ (Γ : Con) (M N : Λ) (A B : Ty),
            Typable Γ M (Ty.Fun A B) → Typable Γ N A → Typable Γ (Lambda.App M N) B

/- And we introduce the promised notation. -/
notation Γ " ⊢ " M " : " A => Typable Γ M A
notation "⊢ " M " : " A => Typable List.nil M A

/- Some examples -/
example : (⊢ (Lambda.Lam (Lambda.Var 0)) : Ty.Fun (Ty.Var "int") (Ty.Var "int")) := by
  apply Typable.Fun; apply Typable.Var; simp

example : 
  [Ty.Var "int"] ⊢ (Lambda.App (Lambda.Lam (Lambda.Var 0)) (Lambda.Var 0)) : 
    Ty.Var "int" := by 
  apply Typable.App (A := Ty.Var "int"); apply Typable.Fun; apply Typable.Var; simp
  apply Typable.Var; simp

/-!
## Subject reduction

We show a nice lemma stating that "computing" a λ-term preserves its type. First, we will
want to show a small substitution lemma, stating that if Γ, x : A ⊢ M : B and Γ ⊢ N : A, then
we can type M[N/x] aswell. We need to generalize this statement a bit to put A anywhere in
the context, otherwise the induction doesn't work for the λ-abstraction.

We thus start by defining the operation to "put A anywhere": -/
def liftΓ (Γ : Con) (k : ℕ) (A : Ty) : Con :=
  match k with
  | 0 => A :: Γ
  | n + 1 => match Γ with
    | [] => []
    | B :: Γ => B :: liftΓ Γ n A

/-! Then, we can show some soundness properties for liftΓ. -/
/-! First, we show that getting an element before the insertion is the same as not 
    inserting. -/
lemma liftΓ_get_lower :
  ∀ (Γ : Con) (n k : ℕ) (A : Ty), 
    k ≤ List.length Γ → n < k → List.get? (liftΓ Γ k A) n = List.get? Γ n := by
  intro Γ; induction' Γ with B Γ ihΓ <;> intro n k A h h'
  · simp at h; rw [h] at h'; contradiction
  · cases' k with k
    · contradiction
    · simp; unfold liftΓ; split; contradiction; cases' n with n
      simp; aesop; simp; simp at ihΓ; aesop

/-! Then, we show that getting at the index of the inserted element is getting the inserted 
    element. -/
lemma liftΓ_get_eq :
  ∀ (Γ : Con) (k : ℕ) (A : Ty), 
    k ≤ List.length Γ → List.get? (liftΓ Γ k A) k = A := by
  intro Γ; induction' Γ with B Γ ihΓ <;> intro k A h
  · simp at h; simp; rw [h]; unfold liftΓ; simp
  · cases' k with k
    · simp; unfold liftΓ; simp
    · simp; unfold liftΓ; split; contradiction; simp at ihΓ; aesop

lemma getElem?_cons : 
  ∀ {α : Type} (a : α) (l : List α) (i : ℕ), 
    (a :: l)[i]? = if i = 0 then some a else l[i-1]? := by
  intro α a l i; cases i <;> simp

/-! Finally, we show that getting at a greater index is the same as getting it but one index 
    higher. -/
lemma liftΓ_get_greater :
  ∀ (Γ : Con) (n k : ℕ) (A : Ty),
    k ≤ List.length Γ → k < n → List.get? (liftΓ Γ k A) n = List.get? Γ (n - 1) := by
  intro Γ; induction' Γ with B Γ ihΓ <;> intro n k A h h'
  · simp; cases' k with k; unfold liftΓ; simp; omega; unfold liftΓ; split; simp; contradiction
  · cases' k with k
    · simp; unfold liftΓ; rw [getElem?_cons]; split; omega; rfl
    · simp; unfold liftΓ; simp at ihΓ; simp; rw [getElem?_cons]; split; omega
      rw [getElem?_cons]; split; omega; apply ihΓ; simp at h; assumption; omega

/-! Before proving the substitution lemma, we need to show a small lemma about lifting: as we
    prove a general statement, we substitute k for N in M. Hence, the actual pertinent things
    in Γ for N should start at k, i.e., we should lift N by k. Hence, we actually want to
    show some kind of "soundness" about this intuition: adding an element to the context at 
    an index, and lifting by one preserves typability. We thus want, if Γ ⊢ lift n k M : A and
    we place B at m in Γ, that:
    * m should be lower than n to avoid affecting the typability,
    * k is the lifting and we want it to be at most m

    This lemma can be shown by induction on the typability of lift n k M. -/
lemma lift_preserves_typability :
  ∀ (Γ : Con) (M : Λ) (A B : Ty) (n m k : ℕ),
    n ≤ List.length Γ → m ≤ n → k ≤ m → (Γ ⊢ lift n k M : A) → 
    (liftΓ Γ m B ⊢ lift (n + 1) k M : A) := by
  intro Γ M A B n m k hle h' h'' h
  generalize e : lift n k M = M'; rw [e] at h
  have e₀ : lift 1 m (lift n k M) = lift (n + 1) k M := by
    conv_rhs => rw [Nat.add_comm]; rfl
    apply double_lift; constructor; assumption; omega
  rw [←e₀, e]; clear e; revert n m M 
  induction h with
  | Var Γ x A e' => intro M n m hle hmn _ _; unfold lift; split; constructor
                    rw [liftΓ_get_lower]; assumption; omega; assumption
                    constructor
                    have : x + 1 > m := by omega
                    rw [liftΓ_get_greater]; assumption; omega; assumption
  | Fun Γ M A C _ ih => intro N n m hle hmn hkm _; unfold lift
                        simp at ih
                        have h₁ : n + 1 ≤ List.length Γ + 1 := by omega
                        have h₂ : m + 1 ≤ n + 1 := by omega
                        have h₃ : k ≤ m + 1 := by omega
                        have h₄ : lift 1 (m + 1) (lift (n + 1) k N) = lift (n + 1 + 1) k N :=
                          by conv_rhs => rw [Nat.add_comm]; rfl
                             apply double_lift; constructor <;> omega
                        specialize ih N (n + 1) (m + 1) h₁ h₂ h₃ h₄; constructor
                        unfold liftΓ at ih; simp at ih; apply ih
  | App Γ M N A C _ _ ihM ihN => intro P n m hle hmn hkm hm; constructor; apply ihM
                                 assumption; assumption; assumption; assumption
                                 apply ihN; assumption; assumption; assumption
                                 assumption

/-! Then, we can show the awaited substitution lemma. -/
lemma sr_substitution_lemma : 
  ∀ (Γ : Con) (M N : Λ) (A B : Ty) (k : ℕ), 
    k ≤ List.length Γ → (liftΓ Γ k A ⊢ M : B) → (Γ ⊢ lift k 0 N : A) → Γ ⊢ M[N⧸k] : B := by
  intro Γ M N A B k h hM hN
  generalize hΓ₀ : liftΓ Γ k A = Γ₀
  rw [hΓ₀] at hM; revert Γ k
  induction hM with
  | Var Γ₁ x B e => intro Γ k h' hN e'; unfold substitute; split
                    · constructor; rw [←e'] at e; rw [←liftΓ_get_lower] <;> assumption
                    · split
                      · have : x = k := by assumption
                        have : A = B := by rw [←e', this, liftΓ_get_eq] at e; injection e
                                           assumption
                        rw [←this]; assumption
                      · constructor; rw [←e]; rw [←e', liftΓ_get_greater]; assumption
                        omega
  | Fun Γ₁ M B C _ ih => intro Γ k h' hN e'; unfold substitute; constructor
                         apply ih; simp; assumption
                         have e : B :: Γ = liftΓ Γ 0 B := by unfold liftΓ; rfl
                         rw [e]; apply lift_preserves_typability; assumption; omega; omega
                         assumption; unfold liftΓ; simp; rw [←e']
  | App Γ₁ M P B C _ _ ihM ihP => intro Γ k h' hN e'; unfold substitute; constructor
                                  apply ihM <;> assumption; apply ihP <;> assumption

/-- Which has an almost direct corollary in the form of the subject reduction theorem. -/
theorem subject_reduction : 
  ∀ (Γ : Con) (M M' : Λ) (A : Ty),
    (Γ ⊢ M : A) → (M →β M') → Γ ⊢ M' : A := by
  intro Γ M M' A hty hM; revert Γ A
  induction' hM with M N M N _ ih M N P _ ih M N P _ ih <;> intro Γ A hty
  · cases hty with
    | App _ _ _ B hM hN => 
          apply sr_substitution_lemma; omega
          · cases hN with | Fun _ _ _ _ _ => unfold liftΓ; assumption
          · rw [lift_zero]; assumption
  · cases hty with
    | Fun _ _ A B hty => constructor; apply ih; exact hty
  · cases hty with
    | App _ _ _ B _ hN hM => constructor; exact hN; apply ih; exact hM
  · cases hty with
    | App _ _ _ B _ hM hN => constructor; apply ih Γ (Ty.Fun B A); exact hM; exact hN
