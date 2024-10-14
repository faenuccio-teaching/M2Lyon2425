import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Action.Prod

-- Show that ordered pairs form a module over ℝ
example : Module ℝ (ℝ × ℝ) :=
{
  smul := fun x (a,b) => (x*a,x*b)


    --fun a (b,c) => (a * b , a*c)
  one_smul := by
    intro b
    exact one_mul b







  mul_smul :=  by
    intro x y
    intro b
    rw[Prod.smul_def]
    rw[Prod.smul_def]
    rw[Prod.smul_fst]
    rw[Prod.smul_snd]



  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry
}
