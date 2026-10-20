import SixthMoment.Arithmetic.Euler.Local.Recurrence.PrincipalCorrectionRecurrence


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem principal_euler_expansion (x : ℂ) : (1-x)^4*(1+4*x+x^2)=1-9*x^2+16*x^3-9*x^4+x^6 := by ring
theorem principal_euler_error_factored (x : ℂ) : (1-x)^4*(1+4*x+x^2)-1=x^2*(-9+16*x-9*x^2+x^4) := by ring

end SixthMoment.Source.NoDPLocal
