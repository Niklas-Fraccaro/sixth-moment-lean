import Sechstmoment.Arithmetic.Euler.Local.Rational.TailCubicBoundary

/-! A boundary formula for the quadratic correction. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem q2_add_two (a b c d : R) (h : ℕ) :
    q2 a b c d (h+2) = e3 a b c d*coeff4 a b c d (h+1)-e4 a b c d*coeff4 a b c d h := by
  unfold q2
  simp only [Nat.add_assoc]
  rw [coeff4_recurrence]; ring

end Sechstmoment.Source.NoDPLocal
