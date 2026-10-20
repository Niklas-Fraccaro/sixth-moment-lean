import SixthMoment.Arithmetic.Euler.Local.Rational.TailPolynomial


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem tail4_higher_cancel (a b c d : R) (h n : ℕ) :
    tail4 a b c d h (n+4)-e1 a b c d*tail4 a b c d h (n+3)+
      e2 a b c d*tail4 a b c d h (n+2)-e3 a b c d*tail4 a b c d h (n+1)+e4 a b c d*tail4 a b c d h n = 0 := by
  simp only [tail4, ← Nat.add_assoc]
  rw [coeff4_recurrence]; ring

end SixthMoment.Source.NoDPLocal
