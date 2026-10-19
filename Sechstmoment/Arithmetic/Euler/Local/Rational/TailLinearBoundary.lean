import Sechstmoment.Arithmetic.Euler.Local.Rational.TailQuadraticBoundary

/-! A boundary formula for the linear correction. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem q1_add_three (a b c d : R) (h : ℕ) :
    q1 a b c d (h+3) = -e2 a b c d*coeff4 a b c d (h+2)+
      e3 a b c d*coeff4 a b c d (h+1)-e4 a b c d*coeff4 a b c d h := by
  unfold q1
  simp only [Nat.add_assoc]
  rw [coeff4_recurrence]; ring

end Sechstmoment.Source.NoDPLocal
