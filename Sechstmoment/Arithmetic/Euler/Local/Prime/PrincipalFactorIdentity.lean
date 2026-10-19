import Sechstmoment.Arithmetic.Euler.Local.Bounds.FiniteEulerNorm
import Sechstmoment.Arithmetic.Euler.Local.PrincipalFactor

/-! The new correction is exactly the existing convergent principalLocalFactor. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem principalCorrection_eq_existing (x : ℂ) (hx : ‖x‖<1) (h : ℕ) :
    principalCorrection x h=Sechstmoment.Source.principalLocalFactor x h := by
  rw [Sechstmoment.Source.principalLocalFactor_eq_polynomial x hx h]
  rfl

end Sechstmoment.Source.NoDPLocal
