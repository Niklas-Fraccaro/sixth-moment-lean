import SixthMoment.Arithmetic.Euler.Local.Coefficients.OneCoefficient


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def coeff2 (a b : R) : ℕ → R := step a (coeff1 b)
@[simp] theorem coeff2_zero (a b : R) : coeff2 a b 0 = 1 := by simp [coeff2]
theorem coeff2_succ (a b : R) (n : ℕ) :
    coeff2 a b (n+1) = coeff1 b (n+1)+a*coeff2 a b n := rfl
@[simp] theorem delta_coeff2 (a b : R) (n : ℕ) :
    delta a (coeff2 a b) n = coeff1 b (n+1) := by simp [coeff2]

end SixthMoment.Source.NoDPLocal
