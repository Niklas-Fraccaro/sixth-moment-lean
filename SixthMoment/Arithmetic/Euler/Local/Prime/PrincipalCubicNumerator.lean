import SixthMoment.Arithmetic.Euler.Local.Rational.ComplexRepeatedRoots


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem numerator_all_one (h : ℕ) (t : ℂ) :
    numerator (1:ℂ) 1 1 1 h t=
      (((h:ℂ)+1)*((h:ℂ)+2)*((h:ℂ)+3)-
        3*(h:ℂ)*((h:ℂ)+2)*((h:ℂ)+3)*t+
        3*(h:ℂ)*((h:ℂ)+1)*((h:ℂ)+3)*t^2-
        (h:ℂ)*((h:ℂ)+1)*((h:ℂ)+2)*t^3)/6 := by
  simp only [numerator,q0,q1,q2,q3,coeff4_all_one,e1,e2,e3]
  push_cast
  ring

end SixthMoment.Source.NoDPLocal
