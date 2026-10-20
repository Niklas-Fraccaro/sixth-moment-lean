import SixthMoment.Arithmetic.Euler.Local.Rational.BaseNumerator


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem q3_succ (a b c d : R) (h : ℕ) :
    q3 a b c d (h+1) = -e4 a b c d*coeff4 a b c d h := by
  unfold q3
  simp only [Nat.add_assoc]
  rw [coeff4_recurrence]; ring

end SixthMoment.Source.NoDPLocal
