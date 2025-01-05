import M2Lyon2425.projet.projet

/- Dans ce fichier, seulement des résultats inutilisés ailleurs, mais qui soit:
- m'ont semblés être utiles à un moment,
- m'ont servis de base sur laquelle travailler, en tant que résultat plus faible. -/

variable {α : Type*}

@[reducible]
def indexed_op (ι β : Type*) := ι → ARS β

@[reducible]
def big_sum {ι : Type*} (t : indexed_op ι α) : ARS α :=
  fun x y ↦ ∃ i, t i x y

def big_sum_respects_le {ι : Type*} {g : ARS α} (t : indexed_op ι α) :
  (∀ i, t i ≤ g) → big_sum t ≤ g := by
    intro htflef
    rw [ARS.le_iff_imp]
    intro x y hbigsum
    exact ARS.le_iff_imp.mp (htflef hbigsum.choose) x y hbigsum.choose_spec

def big_sum_comm_from_comm {ι : Type*} {f : ARS α} (t : indexed_op ι α) :
  (∀ i, t i * f = f * t i) → big_sum t * f = f * big_sum t := by
    intro hypcomm
    ext x y
    constructor
    · intro hyp
      let z1 := hyp.choose
      let ⟨hz1bs, hz1f⟩ := hyp.choose_spec
      let i := hz1bs.choose
      have hi := hz1bs.choose_spec
      have hypcommi := (hypcomm i)
      have h₀ : ((t i * f) x y ↔ (f * t i) x y) :=  by rw [hypcommi]
      have h₁ : (t i * f) x y := by use z1
      have h₃ := h₀.mp h₁
      let z2 := h₃.choose
      have ⟨hz2f, hz2bs⟩ := h₃.choose_spec
      use z2
      constructor
      · exact hz2f
      · use i
    · intro hyp
      let z1 := hyp.choose
      let ⟨hz1f, hz1bs⟩ := hyp.choose_spec
      let i := hz1bs.choose
      have hi := hz1bs.choose_spec
      have hypcommi := (hypcomm i)
      have h₀ : ((t i * f) x y ↔ (f * t i) x y) :=  by rw [hypcommi]
      have h₁ : (f * t i) x y := by use z1
      have h₃ := h₀.mpr h₁
      let z2 := h₃.choose
      have ⟨hz2bs, hz2f⟩ := h₃.choose_spec
      use z2
      constructor
      · use i
      · exact hz2f

/-- Le fait que `∃ i, ∃ w, ⋯` est la même chose que `∃ w, ∃ i, ⋯`
On pourrait aller plus loin et faire une distributivité d'une
big sum sur une autre, mais c'est plus que le nécessaire.
-/
def big_sum_distrib_left {ι : Type*} {f: ARS α} {t : indexed_op ι α} :
  f * big_sum t = big_sum (fun i ↦ f * t i)
    := by
      ext x y
      constructor
      · intro hyp
        let w := hyp.choose
        have ⟨hwf, hwbs⟩ := hyp.choose_spec
        let i := hwbs.choose
        have hi := hwbs.choose_spec
        use i
        simp only
        use w
      · intro hyp
        let i := hyp.choose
        have hi := hyp.choose_spec
        simp only at hi
        let w := hi.choose
        have ⟨hwf, hwbs⟩ := hi.choose_spec
        use w
        constructor
        · exact hwf
        · use i

/-- Le choix d'avoir des fonctions dans ℕ plutôt que Fin (n+1) est arbitraire.-/
def existsChaine (f :ARS α) (n : ℕ) (x y : α) :=
  ∃ w : ℕ → α, (w 0 = x ∧ w n = y) ∧ (∀ i, n < i+1 ∨ f (w i) (w (i+1)))

/-- Une description alternative de f^n
On remarque que l'ordre de quantification est important,
si on commence par `∀ x y, ∀ n, ⋯`, il n'est pas possible
de faire une induction sur `n` en gardant `x` et `y` généraux.-/
lemma npow' {f : ARS α} :
  ∀ n : ℕ, ∀ x y : α,
  (f^n) x y →
  existsChaine f n x y := by
    intro n
    induction n with
    | zero =>
      intro x y hypf0
      use (fun _ ↦ x)
      simp only [pow_zero] at hypf0
      constructor
      · constructor <;> rw [hypf0]
      · intro i
        left
        omega
    | succ m hm =>
      intro x y' hypfn
      rw [pow_succ] at hypfn
      let wn := hypfn.choose
      have ⟨hfmwn, hfwn⟩ := hypfn.choose_spec
      let w := (hm x wn hfmwn).choose
      have ⟨⟨hw0, hwm⟩, hwf⟩ := (hm x wn hfmwn).choose_spec
      let w' :=  fun (i: ℕ) ↦ if i = m+1 then y' else w i
      use w'
      constructor
      · constructor
        · simp only [w', reduceIte]
          exact hw0
        · simp only [w', reduceIte]
      · intro i' -- on va faire une *trichotomie* sur i'>m, i'=m, i'< m
        by_cases hi₁ : m+1 < i'+1
        · left; exact hi₁
        · right
          simp only [add_lt_add_iff_right, not_lt] at hi₁
          by_cases hi₂ : i' = m
          · have hi₃ : m ≠ m+1 := by omega
            simp only [w', hi₂, hi₃, reduceIte, w, hwm, hfwn]
          · have hi₃ : i' ≠ m +1 := by omega
            have hi₄ : i'+1 ≠ m+1 := by omega
            simp only [w', hi₃, hi₄, reduceIte]
            cases hwf i' with
            | inl hi => exfalso; omega
            | inr hw' => exact hw'

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
