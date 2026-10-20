import Sechstmoment.Arithmetic.Euler.Local.Prime.PrincipalCorrection


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

@[simp] theorem principalCorrection_zero (x : ℂ) : principalCorrection x 0=1 := by norm_num [principalCorrection]
theorem principalCorrection_one (x : ℂ) : principalCorrection x 1=x*(3-3*x+x^2) := by
  norm_num [principalCorrection]

end Sechstmoment.Source.NoDPLocal
