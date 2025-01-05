import M2Lyon2425.projet.projet

variable {α : Type*}

def hasNoetherianInduction (f : ARS α) (P : α → Prop) :=
  (∀ a, (∀ b, f a b → P b) → P a) → ∀ x, P x

def isNoetherian (f : ARS α) (P : α → Prop) := ∀ a, (∀ b, f a b → P b) → P a

def nP (P : α → Prop) := Subtype (¬ P ·)

def redStep_of_exists_nP (f : ARS α) (P : α → Prop) (hNP : isNoetherian f P) (x : nP P) :
  ∃ y : nP P, f x.val y.val := by
    rw [isNoetherian] at hNP
    by_contra hc
    push_neg at hc
    refine x.prop (hNP x.val ?_)
    intro b  hfxb
    by_cases hb : P b
    · exact hb
    · exfalso
      exact hc ⟨b, hb⟩ hfxb

structure RedStep_nP (f : ARS α) (P : α → Prop):=
  a : nP P
  b : nP P
  red : f a.val b.val

noncomputable def infRedSeq_of_nP
(f : ARS α) (P : α → Prop) (hNP : isNoetherian f P) (x : nP P) (i : ℕ) :
  RedStep_nP f P := by
    let a := match i with
    | 0 => x
    | m+1 => (infRedSeq_of_nP f P hNP x m).b
    exact {
        a := a
        b := (redStep_of_exists_nP f P hNP a).choose
        red := (redStep_of_exists_nP f P hNP a).choose_spec
    }

noncomputable def InfRedSeq_of_nP
(f : ARS α) (P : α → Prop) (hNP : isNoetherian f P) (x : nP P) :
  InfRedSeq f := by
    let T := infRedSeq_of_nP f P hNP x
    refine ⟨fun i ↦ (T i).a.val, fun i ↦ (T i).red⟩

theorem NoetherianInduction_from_termination {f : ARS α} (hfT : isTerminatingRel f) (P : α → Prop):
 hasNoetherianInduction f P := by
    intro hNP xv
    by_contra hx
    have x : nP P := ⟨xv, hx⟩
    have T := InfRedSeq_of_nP f P hNP x
    rw [terminatingRelEquiv] at hfT
    exact hfT (by use T.val; exact T.prop)
