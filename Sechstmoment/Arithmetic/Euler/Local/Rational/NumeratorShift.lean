import Sechstmoment.Arithmetic.Euler.Local.Rational.TailLinearBoundary


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem numerator_succ (a b c d t : R) (h : ℕ) :
    t*numerator a b c d (h+1) t = numerator a b c d h t-coeff4 a b c d h*denom a b c d t := by
  rw [denom_expansion]
  unfold numerator q0 q1 q2 q3
  simp only [Nat.add_assoc]
  rw [coeff4_recurrence]; ring

end Sechstmoment.Source.NoDPLocal
