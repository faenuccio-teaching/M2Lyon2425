/-There exists a bounded Lebesgue Integrable Function $f : [0,1] → ℝ$ such that for all the functions g : [0,1] → ℝ which is equal to f almost everywhere with respect to the lebesgue measure, is never Riemann Integrable-/
/-## Proof-/
/-Let A be a set which is contained in [0,1] and has lebesgue measure less than 1 and contains all the rationals in [0,1]. -/
/- This is constructed by sets Ioo(rₙ - 1/2ⁿ, rₙ + 1/2ⁿ )  where rₙ is an enumeration of the rationals -/
/- Let the bounded integrable function f be the Indicator function on A. -/
/-If g is equal to A almost everywhere, then there exists a null set:= N s.t g(x) = 1 ∀ A\N and g(x) = 0 for x ∉ N ∪ A -/
/-We then use the fact that every bounded Riemann Integrable function is continuous almost everywhere.-/
/-Since A is open and dense in [0,1], A\N is dense in [0,1]  and (A∪N)ᶜ has some finite measure. -/

/- # Proof-/
/-A is open and dense in [0,1], so for any open interval I in [0,1], I∩A ≠ ∅. Thus ∃ an open interval I₁ such that I₁ ⊆ I∩A-/
/-μ(I∩A) > 0  -/
/- μ(A∩I) = μ(A∩I∖N) + μ(A∩I∩N) = μ(A∩I\N) ≤ μ(A\N)-/
/-So, g is discontinuous at all the points (A∪N)ᶜ-/
