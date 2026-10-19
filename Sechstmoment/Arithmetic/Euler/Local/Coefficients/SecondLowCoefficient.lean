import Sechstmoment.Arithmetic.Euler.Local.Rational.HigherCancellation

/-! The quadratic fourfold coefficient and the second numerator at h=0. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff4_two (a b c d : R) : coeff4 a b c d 2 =
    (e1 a b c d)^2-e2 a b c d := by
  norm_num [coeff4_succ, coeff3_succ, coeff2_succ, coeff1, e1,e2]; ring
@[simp] theorem q2_zero (a b c d : R) : q2 a b c d 0 = 0 := by
  simp [q2,coeff4_two,e1]; ring

end Sechstmoment.Source.NoDPLocal
