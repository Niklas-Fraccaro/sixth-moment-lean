import SixthMoment.Arithmetic.Euler.Local.Recurrence.DifferenceTranslation


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff4_annihilated (a b c d : R) (n : ℕ) :
    delta d (delta c (delta b (delta a (coeff4 a b c d)))) n = 0 := by
  simp only [delta, coeff4_succ, coeff3_succ, coeff2_succ, coeff1_succ, Nat.add_assoc]
  ring

end SixthMoment.Source.NoDPLocal
