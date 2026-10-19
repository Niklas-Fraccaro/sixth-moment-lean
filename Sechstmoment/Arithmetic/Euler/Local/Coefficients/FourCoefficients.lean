import Sechstmoment.Arithmetic.Euler.Local.Coefficients.ThreeCoefficients

/-! The shifted fourfold local divisor coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def coeff4 (a b c d : R) : ℕ → R := step a (coeff3 b c d)
@[simp] theorem coeff4_zero (a b c d : R) : coeff4 a b c d 0 = 1 := by simp [coeff4]
theorem coeff4_succ (a b c d : R) (n : ℕ) :
    coeff4 a b c d (n+1) = coeff3 b c d (n+1)+a*coeff4 a b c d n := rfl
@[simp] theorem delta_coeff4 (a b c d : R) (n : ℕ) :
    delta a (coeff4 a b c d) n = coeff3 b c d (n+1) := by simp [coeff4]

end Sechstmoment.Source.NoDPLocal
