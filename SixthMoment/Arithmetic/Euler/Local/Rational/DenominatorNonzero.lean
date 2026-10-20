import SixthMoment.Arithmetic.Euler.Local.Coefficients.Scaling


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R] [NoZeroDivisors R]
theorem denom_ne_zero (a b c d t : R)
    (ha : 1-a*t≠0) (hb : 1-b*t≠0) (hc : 1-c*t≠0) (hd : 1-d*t≠0) : denom a b c d t≠0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd

end SixthMoment.Source.NoDPLocal
