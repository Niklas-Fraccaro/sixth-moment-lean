import Sechstmoment.Arithmetic.Euler.Local.Coefficients.TwoCoefficients


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def coeff3 (a b c : R) : ℕ → R := step a (coeff2 b c)
@[simp] theorem coeff3_zero (a b c : R) : coeff3 a b c 0 = 1 := by simp [coeff3]
theorem coeff3_succ (a b c : R) (n : ℕ) :
    coeff3 a b c (n+1) = coeff2 b c (n+1)+a*coeff3 a b c n := rfl
@[simp] theorem delta_coeff3 (a b c : R) (n : ℕ) :
    delta a (coeff3 a b c) n = coeff2 b c (n+1) := by simp [coeff3]

end Sechstmoment.Source.NoDPLocal
