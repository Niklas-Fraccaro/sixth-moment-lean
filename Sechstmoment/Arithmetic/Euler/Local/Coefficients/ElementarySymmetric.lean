import Sechstmoment.Arithmetic.Euler.Local.Coefficients.LowCoefficients


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def e1 (a b c d : R) := a+b+c+d
def e2 (a b c d : R) := a*b+a*c+a*d+b*c+b*d+c*d
def e3 (a b c d : R) := a*b*c+a*b*d+a*c*d+b*c*d
def e4 (a b c d : R) := a*b*c*d
def denom (a b c d t : R) := (1-a*t)*(1-b*t)*(1-c*t)*(1-d*t)
theorem denom_expansion (a b c d t : R) :
    denom a b c d t = 1-e1 a b c d*t+e2 a b c d*t^2-e3 a b c d*t^3+e4 a b c d*t^4 := by
  unfold denom e1 e2 e3 e4; ring
@[simp] theorem denom_zero (a b c d : R) : denom a b c d 0 = 1 := by simp [denom]

end Sechstmoment.Source.NoDPLocal
