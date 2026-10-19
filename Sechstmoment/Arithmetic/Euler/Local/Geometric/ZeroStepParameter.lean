import Sechstmoment.Arithmetic.Euler.Local.Rational.NumeratorShift

/-! At a ramified prime the zero geometric parameter does not change a sequence. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
@[simp] theorem step_zero_parameter (f : ℕ → R) (n : ℕ) : step 0 f n = f n := by
  cases n <;> simp
@[simp] theorem coeff4_first_zero (b c d : R) (n : ℕ) : coeff4 0 b c d n = coeff3 b c d n := by
  simp [coeff4]
@[simp] theorem coeff3_first_zero (b c : R) (n : ℕ) : coeff3 0 b c n = coeff2 b c n := by
  simp [coeff3]

end Sechstmoment.Source.NoDPLocal
