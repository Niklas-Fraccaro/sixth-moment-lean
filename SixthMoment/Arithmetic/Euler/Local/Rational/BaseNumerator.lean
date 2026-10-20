import SixthMoment.Arithmetic.Euler.Local.Coefficients.ThirdLowCoefficient


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
@[simp] theorem numerator_base (a b c d t : R) : numerator a b c d 0 t = 1 := by
  simp [numerator]
theorem numerator_base_mul (a b c d t y : R) : numerator a b c d 0 t*y = y := by simp

end SixthMoment.Source.NoDPLocal
