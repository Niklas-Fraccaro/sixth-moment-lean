import Sechstmoment.Arithmetic.Euler.Local.Coefficients.FourCoefficients

/-! The constant and linear shifted divisor coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
@[simp] theorem coeff2_one (a b : R) : coeff2 a b 1 = a+b := by
  rw [show 1=0+1 from rfl, coeff2_succ]; simp [coeff1]; ring
@[simp] theorem coeff3_one (a b c : R) : coeff3 a b c 1 = a+b+c := by
  rw [show 1=0+1 from rfl, coeff3_succ]; simp; ring
@[simp] theorem coeff4_one (a b c d : R) : coeff4 a b c d 1 = a+b+c+d := by
  rw [show 1=0+1 from rfl, coeff4_succ]; simp; ring

end Sechstmoment.Source.NoDPLocal
