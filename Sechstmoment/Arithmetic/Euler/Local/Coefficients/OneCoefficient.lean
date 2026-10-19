import Sechstmoment.Arithmetic.Euler.Local.Recurrence.DifferenceCommutation

/-! Coefficients of one geometric series. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def coeff1 (a : R) (n : ℕ) : R := a^n
@[simp] theorem coeff1_zero (a : R) : coeff1 a 0 = 1 := by simp [coeff1]
theorem coeff1_succ (a : R) (n : ℕ) : coeff1 a (n+1) = a*coeff1 a n := by
  simp only [coeff1, pow_succ]; ring
@[simp] theorem delta_coeff1 (a : R) (n : ℕ) : delta a (coeff1 a) n = 0 := by
  simp [delta, coeff1_succ]

end Sechstmoment.Source.NoDPLocal
