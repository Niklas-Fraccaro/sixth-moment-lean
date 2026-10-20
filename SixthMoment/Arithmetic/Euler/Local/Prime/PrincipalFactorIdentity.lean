import SixthMoment.Arithmetic.Euler.Local.Bounds.FiniteEulerNorm
import SixthMoment.Arithmetic.Euler.Local.PrincipalFactor


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem principalCorrection_eq_existing (x : ℂ) (hx : ‖x‖<1) (h : ℕ) :
    principalCorrection x h=SixthMoment.Source.principalLocalFactor x h := by
  rw [SixthMoment.Source.principalLocalFactor_eq_polynomial x hx h]
  rfl

end SixthMoment.Source.NoDPLocal
