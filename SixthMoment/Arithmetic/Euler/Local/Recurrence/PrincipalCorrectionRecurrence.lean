import SixthMoment.Arithmetic.Euler.Local.Prime.PrincipalCorrectionBase


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem principalCorrection_succ (x : ℂ) (h : ℕ) :
    principalCorrection x (h+1)=principalCorrection x h-(1-x)^3*((h:ℂ)+1)*((h:ℂ)+2)/2*x^h := by
  unfold principalCorrection
  push_cast
  rw [pow_succ]
  ring

end SixthMoment.Source.NoDPLocal
