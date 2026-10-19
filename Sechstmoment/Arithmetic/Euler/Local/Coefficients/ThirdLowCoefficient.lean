import Sechstmoment.Arithmetic.Euler.Local.Coefficients.SecondLowCoefficient

/-! The cubic fourfold coefficient and the third numerator at h=0. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff4_three (a b c d : R) : coeff4 a b c d 3 =
    (e1 a b c d)^3-2*e1 a b c d*e2 a b c d+e3 a b c d := by
  norm_num [coeff4_succ, coeff3_succ, coeff2_succ, coeff1,e1,e2,e3]; ring
@[simp] theorem q3_zero (a b c d : R) : q3 a b c d 0 = 0 := by
  simp [q3,coeff4_two,coeff4_three,e1]; ring

end Sechstmoment.Source.NoDPLocal
