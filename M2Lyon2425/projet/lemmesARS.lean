/- Un lemme très utilisé -/
import «M2Lyon2425».projet.ARSinstKleene

variable {α : Type*}

namespace ARS

/-- Étant donnés `f g : ARS α`, la relation algébrique `f ≤ g` est équivalente
au fait que pour tout `x y : α`, `f x y`, en tant que proposition, est plus faible
que `g x y`. -/
lemma le_iff_imp {f g : ARS α} : f ≤ g ↔ ∀ x y, f x y → g x y := by
  constructor
  · intro hyp x y hfxy
    rw [← add_eq_right_iff_le] at hyp
    rw [← hyp]
    left
    exact hfxy
  · intro hyp
    ext x y
    constructor
    · intro ou
      cases ou with
      | inl fxy =>
        exact hyp x y fxy
      | inr gxy =>
        exact gxy
    · intro hgxy
      right
      exact hgxy

end ARS
