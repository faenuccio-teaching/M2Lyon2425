/- Dans ce fichier, eulement des résultats inutilisés ailleurs, mais qui soit:
- m'ont semblés être utiles à un moment,
- m'ont servis de base sur laquelle travailler, en tant que résultat plus faible.
-/
import M2Lyon2425.projet.projet

variable {α : Type*}

structure RedStep (f : ARS α) :=
  a : α
  b : α
  red : f a b

noncomputable def infRedSeq_of_emptyNF (f : ARS α) (hE : ¬ Nonempty (NF_of f)) (prems : α) (i : ℕ) :
  RedStep f := by
    have h₁ : ∀ b : α, ∃ c, f b c := by
      intro b
      simp only [nonempty_subtype, not_exists] at hE
      have := hE b
      rw [isNormalForm] at this
      push_neg at this
      exact this
    let a := match i with
    | 0 => prems
    | m+1 => (infRedSeq_of_emptyNF f hE prems m).b
    exact {
        a := a
        b := (h₁ a).choose
        red := (h₁ a).choose_spec
    }

private noncomputable def RedSeqAux (f : ARS α) (hE : ¬ Nonempty (NF_of f)) (prems : α) :
  InfRedSeq f := by
    let T := infRedSeq_of_emptyNF f hE prems
    exact ⟨fun i ↦ (T i).a, fun i ↦ (T i).red⟩

lemma exists_NF_of_termination [Inhabited α] (f : ARS α) :
  isTerminatingRel f → Nonempty (NF_of f) := by
    contrapose
    intro h
    rw [terminatingRelEquiv, isTerminatingRel']
    push_neg at h ⊢
    have a : α := Inhabited.default
    use (RedSeqAux f h a).val
    exact (RedSeqAux f h a).prop

def isProfondeur (f : ARS α) (π : α → ℕ) : Prop :=
  ∀ a, ∃ k, π a = Nat.succ k → ∃ b, π b = k ∧ f a b

def profondeurARS (f : ARS α) := Subtype (isProfondeur f)

def is_of_rank (f : ARS α) (k : ℕ) (a : α) :
  Prop := by
    match k with
    | 0 => exact isNormalForm f a
    | m+1 => exact ∃ b, f a b ∧ is_of_rank f m b

def ranks (f : ARS α) (a :α) := {k : ℕ | is_of_rank f k a}

def inacc (f : ARS α) (a : α) := ∀ k, ¬ is_of_rank f k a

def Inacc (f : ARS α) := Subtype (inacc f)

lemma lAux₁ (f : ARS α) : ∀ a : Inacc f, ∃ b : Inacc f, f a.val b.val := by
  intro ⟨a, ha⟩
  by_cases hNFa : isNormalForm f a
  · exfalso
    have := ha 0
    rw [is_of_rank] at this
    exact this hNFa
  · rw [isNormalForm] at hNFa
    push_neg at hNFa
    let b := hNFa.choose
    by_cases hb : inacc f b
    · use ⟨b, hb⟩
      simp only
      exact hNFa.choose_spec
    · exfalso
      rw [inacc] at hb
      push_neg at hb
      let k := hb.choose
      have hAbsu := ha (k+1)
      rw [is_of_rank] at hAbsu
      push_neg at hAbsu
      exact hAbsu b hNFa.choose_spec hb.choose_spec

/--Propiété d'être une suite de réduction infinie d'éléments inaccessible de f-/
def isInfRedSeq_of_Inacc (f : ARS α) (S : ℕ → Inacc f) :=
  ∀ i, f (S i).val (S (i+1)).val

def InfRedSeq_of_Inacc ( f : ARS α) := Subtype (isInfRedSeq_of_Inacc f)

/-- Étant donnée `f : ARS α` et `a : Inacc f`,
`dAux₀ f a : ℕ → Inacc f` est une suite de réduction infinie. -/
/- Malgré le nom pas très clair, elle me semble utile. -/
noncomputable def dAux₀ (f : ARS α) (a : Inacc f) (i : ℕ): Inacc f := match i with
    | 0 => a
    | j+1 => (lAux₁ f ((dAux₀ f a) j)).choose

/-- Preuve que `isInfRedSeq f (dAux₀ f a)`, pour `f : ARS α` et `a : Inacc f`-/
noncomputable def dAux₁ (f : ARS α) (a : Inacc f) : InfRedSeq_of_Inacc f := by
  exact ⟨dAux₀ f a, by
    rw [isInfRedSeq_of_Inacc]
    intro i
    match i with
    | 0 =>
      have : (dAux₀ f a) 0 = a := by
        unfold dAux₀
        rfl
      rw [this]
      exact (lAux₁ f a).choose_spec
    | j+1 =>
      have := (lAux₁ f (dAux₀ f a (j+1))).choose_spec
      unfold dAux₀ at this ⊢
      exact this
    ⟩

noncomputable instance existsInfRedSeq_of_Inacc (f : ARS α) (a : Inacc f) :
  Inhabited (InfRedSeq f) := by
    let S := dAux₁ f a
    use fun i ↦ (S.val i).val
    exact fun i ↦ S.prop i

lemma nonTerminating_f_of_Inacc (f : ARS α) (a : Inacc f) :
  ¬ isTerminatingRel f := by
    intro hfT
    have S := (existsInfRedSeq_of_Inacc f a).default
    rw [terminatingRelEquiv, isTerminatingRel'] at hfT
    push_neg at hfT
    exact hfT S.val S.prop
